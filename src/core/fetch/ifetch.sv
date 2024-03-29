`include "core/params.svh"
`include "axi/axi4lite.svh"

module ifetch(
    input clk, rst,
    input flush,
    input flush_is_mispredict,
    input [`ALEN-1:0] flush_next_pc,
    input [`XLEN-1:0] pc,
    input [`ALEN-1:0] mepc, // May not be up to date, can be used to predict xRET
	input next_stalled,
    output reg stall_next,
    output reg ifetch_exception,
    output reg [3:0] ifetch_trap_cause,
    output reg [`ILEN-1:0] instruction, // Valid only if !ifetch_exception
    output reg [`ALEN-1:0] instruction_addr,
    output reg [`ALEN-1:0] instruction_next_addr,

    axi4lite.master sys_bus
);

generate
	if (basic_cache_params::data_size != 64)
		$error("icache's data_size must be 64bit (required by ifetch)");
endgenerate

logic icache_write_enable;
logic [basic_cache_params::aligned_addr_size-1:0] icache_waddr;
logic [basic_cache_params::data_size-1:0] icache_wdata;
logic [basic_cache_params::aligned_addr_size-1:0] icache_raddr;
wire [basic_cache_params::data_size-1:0] icache_rdata;
wire icache_lookup_valid;
basic_cache icache (
	.clk,
	.rst,
	.write_enable(icache_write_enable),
	.waddr(icache_waddr),
	.wdata(icache_wdata),
	.raddr(icache_raddr),
	.rdata(icache_rdata),
	.lookup_valid(icache_lookup_valid)
);

enum bit[3:0] {
	STATE_START_1ST_LOOKUP_FROM_PC,
	STATE_CHECK_1ST_LOOKUP,
	STATE_START_1ST_READ,
	STATE_WAIT_1ST_READ,
	STATE_CHECK_2ND_LOOKUP,
	STATE_START_2ND_READ,
	STATE_WAIT_2ND_READ,
	STATE_STALLED,
    STATE_DISCARD_FLUSHED_READ,
	STATE_EXCEPTION
} state;
logic [`ALEN-1:0] fetch_pc;
logic [`ALEN-1:0] instr_next_addr_comb;
logic [`ALEN-1:0] next_fetch_pc_comb;
logic [basic_cache_params::align_bits-1:0] next_line_offset_comb;
logic [basic_cache_params::aligned_addr_size-1:0] next_cache_line_addr;

// A cache line's content is addressed by align_bits bits, fetch_pc is 8bit granular, and instr are 16bit aligned so that's $clog2(16)=4 trailing zeros in the offset
wire [basic_cache_params::align_bits-1:0] line_instr_byte_offset = {fetch_pc[1 +: basic_cache_params::align_bits-1], 1'b0};
wire [basic_cache_params::data_size+3-1:0] line_instr_offset = {line_instr_byte_offset, 3'b000};
wire is_cache_compressed_instr = icache_rdata[line_instr_offset +: 2] != 2'b11;
wire is_bus_compressed_instr = sys_bus.rdata[line_instr_offset +: 2] != 2'b11;
integer parcels_per_line = basic_cache_params::data_size/16;
integer byte_offset_to_last_parcel = (parcels_per_line-1)*2;
wire cache_fetch_crosses_lines = !is_cache_compressed_instr && line_instr_offset[$size(line_instr_offset)-1 : 3] == byte_offset_to_last_parcel; // 2 bytes are cut off
wire bus_fetch_crosses_lines = !is_bus_compressed_instr && line_instr_offset[$size(line_instr_offset)-1 : 3] == byte_offset_to_last_parcel; // 2 bytes are cut off
wire cache_next_instr_on_next_line = (!is_cache_compressed_instr && line_instr_byte_offset == byte_offset_to_last_parcel-'h2) || line_instr_byte_offset == byte_offset_to_last_parcel;
wire bus_next_instr_on_next_line = (!is_bus_compressed_instr && line_instr_byte_offset == byte_offset_to_last_parcel-'h2) || line_instr_byte_offset == byte_offset_to_last_parcel;

// next_instruction is potentially invalid until we receive valid data
logic [`ILEN-1:0] next_instruction;
wire next_instruction_invalid_len = next_instruction[4:0] == 'b11111;
logic stall_next_comb;

wire should_follow_branch;
wire [`ALEN-1:0] branch_target;
follow_branch follow_branch(
    .clk,
    .rst,

    .instr_valid(!stall_next_comb),
    .instruction(next_instruction),
    .instruction_addr(fetch_pc),
    
    .mepc,

    .should_follow_branch,
    .branch_target
);

reg bus_read_pending;
always @(posedge clk) begin
    if (rst)
        bus_read_pending <= '0;
    else if (sys_bus.rready && sys_bus.rvalid)
        bus_read_pending <= '0;
    else if (sys_bus.arvalid && sys_bus.arready)
        bus_read_pending <= '1;
end

// Read cache lines
always_comb begin
    if (flush_is_mispredict) begin
	   icache_raddr = flush_next_pc[`ALEN-1 -: $size(icache_raddr)];
	end else begin
        `ifndef SYNTHESIS
        unique // Yosys does not parse "unique if" ...
        `endif
        if (state == STATE_START_1ST_LOOKUP_FROM_PC)
            icache_raddr = pc[`ALEN-1 -: $size(icache_raddr)];
        else if (state == STATE_CHECK_1ST_LOOKUP)
            icache_raddr = next_fetch_pc_comb[$size(next_fetch_pc_comb)-1 -: $size(icache_raddr)]; // Valid whether we cross into next line or not
        else if (state == STATE_START_1ST_READ || (state == STATE_WAIT_1ST_READ && !sys_bus.rvalid))
            icache_raddr = next_cache_line_addr;
        else if (state == STATE_WAIT_1ST_READ && sys_bus.rvalid)
            icache_raddr = next_fetch_pc_comb[$size(next_fetch_pc_comb)-1 -: $size(icache_raddr)]; // Prime next CHECK_1ST_LOOKUP
        else if (state == STATE_WAIT_2ND_READ || state == STATE_CHECK_2ND_LOOKUP || state == STATE_STALLED)
            icache_raddr = fetch_pc[$size(fetch_pc)-1 -: $size(icache_raddr)]; // fetch_pc has been updated after the 1st read, is now the next line (due to crossing)
        else
            icache_raddr = 'x;
    end
end

// Write cache lines
always_comb begin
    if (rst || flush || state == STATE_DISCARD_FLUSHED_READ) begin
        icache_write_enable = 'b0;
        icache_waddr = 'x;
        icache_wdata = 'x;
    end else if ((state == STATE_WAIT_1ST_READ || state == STATE_WAIT_2ND_READ) && sys_bus.rvalid) begin
		// We update fetch_pc after the 1st read is done, so this fetch_pc is in fact at the 2nd line's address in WAIT_2ND_READ!
        icache_waddr = fetch_pc[$size(fetch_pc)-1 : basic_cache_params::align_bits];
		icache_wdata = sys_bus.rdata;
    	icache_write_enable = 'b1;
    end else begin
        icache_waddr = 'x;
        icache_wdata = 'x;
        icache_write_enable = 'b0;
    end
end

always_comb begin
	`ifndef SYNTHESIS
	unique // Yosys does not parse "unique if"
	`endif
	if (state == STATE_START_1ST_LOOKUP_FROM_PC) begin
        next_line_offset_comb = 'x;
		instr_next_addr_comb = 'x; // Very long chain in other branches, just use pc directly in this state (opt can't see that)
	end else if (state == STATE_CHECK_1ST_LOOKUP) begin
        // By switching on fetch_crosses_lines, we can get all the high bits from either fetch_pc or next_cache_line_addr
        // This avoids a very wide addition, and we can also exclude the last bit from the math since it's always 0 (2B alignment)
        next_line_offset_comb = {fetch_pc[1 +: basic_cache_params::align_bits-1] + (is_cache_compressed_instr ? 'h1 : 'h2), 1'b0};
        if (cache_next_instr_on_next_line)
            instr_next_addr_comb = {next_cache_line_addr, next_line_offset_comb};
        else
            instr_next_addr_comb = {fetch_pc[$size(fetch_pc)-1 : basic_cache_params::align_bits], next_line_offset_comb};

        `ifndef SYNTHESIS
		if (!icache_lookup_valid)
			instr_next_addr_comb = 'x;
		`endif
	end else if (state == STATE_WAIT_1ST_READ) begin
        next_line_offset_comb = {fetch_pc[1 +: basic_cache_params::align_bits-1] + (is_bus_compressed_instr ? 'h1 : 'h2), 1'b0};
        if (bus_next_instr_on_next_line)
            instr_next_addr_comb = {next_cache_line_addr, next_line_offset_comb};
        else
            instr_next_addr_comb = {fetch_pc[$size(fetch_pc)-1 : basic_cache_params::align_bits], next_line_offset_comb};

		`ifndef SYNTHESIS
		if (!sys_bus.rvalid)
			instr_next_addr_comb = 'x;
		`endif
	end else begin
        next_line_offset_comb = 'x;
		instr_next_addr_comb = 'x;
	end
end

always_comb begin
    if (state == STATE_CHECK_1ST_LOOKUP && should_follow_branch)
        next_fetch_pc_comb <= branch_target;
    else
        next_fetch_pc_comb <= instr_next_addr_comb;
end

always @(posedge clk) begin
    if (flush_is_mispredict) begin
        state <= (bus_read_pending && !sys_bus.rvalid) ? STATE_DISCARD_FLUSHED_READ : STATE_CHECK_1ST_LOOKUP;
        fetch_pc <= flush_next_pc;
		next_cache_line_addr <= flush_next_pc[$bits(flush_next_pc)-1:basic_cache_params::align_bits] + 1;
	end else if (rst || flush) begin
		// Input PC is NOT guaranteed to be stable (or even valid) in rst, so of course we need a cycle just to start the read
		state <= (bus_read_pending && !sys_bus.rvalid) ? STATE_DISCARD_FLUSHED_READ : STATE_START_1ST_LOOKUP_FROM_PC;
		fetch_pc <= 'x;
		next_cache_line_addr <= 'x;
        instruction_next_addr <= 'x;
	end else unique case (state)
	STATE_START_1ST_LOOKUP_FROM_PC: begin
        `ifndef SYNTHESIS
        if (pc[0]) // Alignment exception (should never happen!)
            $error("Alignment exceptions MUST trap on the branch instruction, not at fetch time! The PC must always be aligned.");
        `endif

		state <= STATE_CHECK_1ST_LOOKUP;
		fetch_pc <= pc;
		next_cache_line_addr <= pc[$bits(pc)-1:basic_cache_params::align_bits] + 1;
	end
	STATE_CHECK_1ST_LOOKUP: begin
        if (next_stalled && !stall_next) begin
            // We have valid output but failed the handshake, stall to avoid completing a new read and overwriting pending outputs
			state <= STATE_STALLED;
		end else if (icache_lookup_valid) begin
			// Whether we go to 2nd read or the next instruction, those are updated as soon as we get the 1st instruction (see WAIT_1ST_READ for details)
			fetch_pc <= next_fetch_pc_comb;
            instruction_next_addr <= instr_next_addr_comb;
            if (should_follow_branch)
                next_cache_line_addr <= branch_target[$bits(branch_target)-1:basic_cache_params::align_bits] + 1;
            else if (cache_next_instr_on_next_line)
                next_cache_line_addr <= next_cache_line_addr + 1;

            if (icache_rdata[line_instr_offset +: 5] == 5'b11111) begin // Instr too long
                state <= STATE_EXCEPTION;
                // ifetch_trap_cause is the default EXC_ILLEGAL_INSTR
			end else if (cache_fetch_crosses_lines) begin
				state <= STATE_CHECK_2ND_LOOKUP;
			end else begin
				// Next line addr is primed, continue 1st lookups!
			end
		end else begin
			state <= STATE_START_1ST_READ;
		end
	end
	STATE_START_1ST_READ: begin
		if (sys_bus.arready)
			state <= STATE_WAIT_1ST_READ;
	end
	STATE_WAIT_1ST_READ: begin
		if (sys_bus.rvalid) begin
			// OK to update those now, if we need a 2nd read then we'll know the offset is 'h6 (non-compressed, crosses line)
			// Because we update fetch_pc to the next line (since it crosses for 2nd reads), we can use fetch_pc as sys_bus.araddr unconditionally
			// And it also happens that saving the 2nd read to cache can be done at the new fetch_pc (the next line)
			fetch_pc <= next_fetch_pc_comb;
            instruction_next_addr <= instr_next_addr_comb;
            if (bus_next_instr_on_next_line)
                next_cache_line_addr <= next_cache_line_addr + 1;

            if (sys_bus.rdata[line_instr_offset +: 5] == 5'b11111) begin // Instr too long
                state <= STATE_EXCEPTION;
                // ifetch_trap_cause is the default EXC_ILLEGAL_INSTR
			end else if (!bus_fetch_crosses_lines || icache_lookup_valid) begin // We do a 2nd lookup check at the same time as the 1st read finishes to save a cycle
				state <= STATE_CHECK_1ST_LOOKUP;
			end else begin
				state <= STATE_START_2ND_READ;
            end
		end
	end
	STATE_CHECK_2ND_LOOKUP: begin
		if (icache_lookup_valid) begin
			// Cache stays primed at fetch_pc. Since we JUST crossed, we know we'll just be reading the same line again
			state <= STATE_CHECK_1ST_LOOKUP;
		end else begin
			state <= STATE_START_2ND_READ;
		end
	end
	STATE_START_2ND_READ: begin
		if (sys_bus.arready)
			state <= STATE_WAIT_2ND_READ;
	end
	STATE_WAIT_2ND_READ: begin
		if (sys_bus.rvalid)
			state <= STATE_CHECK_1ST_LOOKUP;
	end
	STATE_STALLED: begin
		if (!next_stalled)
			state <= STATE_CHECK_1ST_LOOKUP;
	end
    STATE_DISCARD_FLUSHED_READ: begin
        if (sys_bus.rvalid || !bus_read_pending) // If we flush during a response cycle, we would miss the rvalid
            state <= STATE_START_1ST_LOOKUP_FROM_PC;
    end
    STATE_EXCEPTION: begin
        // Stay here until reset
    end
	endcase
end

always_comb begin
    unique case (state)
    // Note that we report alignment exceptions on the next cycle when entering STATE_EXCEPTION. It's not a huge priority to optimize.
    STATE_EXCEPTION: next_instruction = 'x;
    STATE_STALLED: next_instruction = instruction;
    STATE_WAIT_1ST_READ: begin
        if (!sys_bus.rvalid)
            next_instruction = instruction;
        else if (bus_fetch_crosses_lines)
            next_instruction = {icache_rdata[0 +: 16], sys_bus.rdata[$size(sys_bus.rdata)-1 -: 16]};
        else
            next_instruction = sys_bus.rdata[line_instr_offset +: `ILEN];
    end
    STATE_CHECK_1ST_LOOKUP: begin
        if (!icache_lookup_valid || (next_stalled && !stall_next))
            next_instruction = instruction;
        else if (cache_fetch_crosses_lines)
            next_instruction = {16'bx, icache_rdata[$size(icache_rdata)-1 -: 16]}; // A 1st lookup can't complete simultaneously w/ a 2nd, so just xpad
        else
            next_instruction = icache_rdata[line_instr_offset +: `ILEN];
    end
    STATE_WAIT_2ND_READ: next_instruction = sys_bus.rvalid ? {sys_bus.rdata[0 +: 16], instruction[0 +: `ILEN - 16]} : instruction;
    STATE_CHECK_2ND_LOOKUP: next_instruction = icache_lookup_valid ? {icache_rdata[0 +: 16], instruction[0 +: `ILEN - 16]} : instruction;
    default: next_instruction = instruction;
    endcase
end

// Outputs
always_comb begin
    if (rst || flush) begin
        stall_next_comb = '1;
    end else begin
		`ifndef SYNTHESIS
		unique // Yosys does not parse "unique if"
		`endif
		// Note that we report alignment exceptions on the next cycle when entering STATE_EXCEPTION. It's not a huge priority to optimize.
        if (state == STATE_EXCEPTION) begin
            stall_next_comb = '0;
        end else if (state == STATE_STALLED) begin
            stall_next_comb = !next_stalled;
        // Only one line to read (note: we'll get trailing Xs reading compressed instrs at the end of a line due to +: `ILEN, but that's okay)
        end else if (state == STATE_WAIT_1ST_READ && sys_bus.rvalid && !bus_fetch_crosses_lines) begin
            stall_next_comb = '0;
        end else if (state == STATE_CHECK_1ST_LOOKUP && next_stalled && !stall_next) begin
            // We're going to STATE_STALLED, our outputs are valid and we don't want to overwrite them before the next handshake
            stall_next_comb = '0;
        end else if (state == STATE_CHECK_1ST_LOOKUP && !(next_stalled && !stall_next) && icache_lookup_valid && !cache_fetch_crosses_lines) begin
            stall_next_comb = '0;
        // Complete instruction with 2nd read
        end else if (state == STATE_WAIT_2ND_READ && sys_bus.rvalid) begin
            stall_next_comb = '0;
        end else if (state == STATE_CHECK_2ND_LOOKUP && icache_lookup_valid) begin
            stall_next_comb = '0;
        // Partial 1st read, potentially immediately completed by 2nd lookup from cache
        end else if (state == STATE_WAIT_1ST_READ && sys_bus.rvalid && bus_fetch_crosses_lines) begin
            stall_next_comb = !icache_lookup_valid;
        end else if (state == STATE_CHECK_1ST_LOOKUP && !(next_stalled && !stall_next) && icache_lookup_valid && cache_fetch_crosses_lines) begin
            stall_next_comb = '1;
        // Yay more waiting. Talk about bubbly pipelines.
        end else begin
            stall_next_comb = '1;
        end
    end
end

always @(posedge clk) begin
    if (rst || flush) begin
        stall_next <= stall_next_comb;
        ifetch_exception <= 'x;
        instruction <= 'x;
        instruction_addr <= 'x;
    end else begin
        // This is safe, we go through this state exactly once per instruction, but only when unstalled
        if (state == STATE_CHECK_1ST_LOOKUP && (!next_stalled || stall_next))
            instruction_addr <= fetch_pc;
        else if (state == STATE_STALLED && !next_stalled)
            instruction_addr <= 'x;

        if (next_instruction_invalid_len)
            ifetch_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        else
            ifetch_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR; // Default trap cause

        stall_next <= stall_next_comb;
		instruction <= next_instruction;
		ifetch_exception <= next_instruction_invalid_len || state == STATE_EXCEPTION;
    end
end

assign sys_bus.aclk = clk;
assign sys_bus.aresetn = !rst;

assign sys_bus.arvalid = (state == STATE_START_1ST_READ || state == STATE_START_2ND_READ) && !flush;
assign sys_bus.araddr = fetch_pc[$size(fetch_pc)-1:basic_cache_params::align_bits] << basic_cache_params::align_bits; // fetch_pc is updated before 2nd reads, so stays valid for both
assign sys_bus.arprot = 'b000;

assign sys_bus.rready = flush || state == STATE_WAIT_1ST_READ || state == STATE_WAIT_2ND_READ || state == STATE_DISCARD_FLUSHED_READ;

assign sys_bus.awaddr = 'x;
assign sys_bus.awprot = 'x;
assign sys_bus.awvalid = 0;

assign sys_bus.wdata = 'x;
assign sys_bus.wstrb = 'x;
assign sys_bus.wvalid = 0;
assign sys_bus.bready = 0;

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (sys_bus.rvalid |-> sys_bus.rresp === AXI4LITE_RESP_OKAY);
    assert property (state == STATE_EXCEPTION && !rst && !flush |=> instruction === 'x);
    assert property (state == STATE_EXCEPTION && !rst && !flush |=> ifetch_exception);
    assert property (!$isunknown(fetch_pc) |-> next_cache_line_addr == fetch_pc[$bits(fetch_pc)-1:basic_cache_params::align_bits] + 1);
    // Trying to write a cache line in unexpected state
    assert property ((state != STATE_DISCARD_FLUSHED_READ
                    && state != STATE_WAIT_1ST_READ
                    && state != STATE_WAIT_2ND_READ) && !rst && !flush |=> !sys_bus.rvalid);
end
`endif

endmodule
