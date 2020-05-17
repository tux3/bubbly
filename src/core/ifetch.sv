`include "params.svh"
`include "../axi/axi4lite.svh"

module ifetch(
    input clk, rst,
    input flush,
    input [`XLEN-1:0] pc,
	input next_stalled,
    output reg stall_next,
    output reg ifetch_exception,
    output reg [`ILEN-1:0] instruction, // Valid only if !ifetch_exception
    output reg [`ALEN-1:0] instruction_addr,
    output reg [`ALEN-1:0] instruction_next_addr,

    axi4lite.master sys_bus,
);

assign sys_bus.aclk = clk;
assign sys_bus.aresetn = !rst;

assign sys_bus.arvalid = state == STATE_START_1ST_READ || state == STATE_START_2ND_READ;
assign sys_bus.araddr = fetch_pc[$size(fetch_pc)-1:basic_cache_params::align_bits] << basic_cache_params::align_bits; // fetch_pc is updated before 2nd reads, so stays valid for both
assign sys_bus.arprot = 'b000;

assign sys_bus.rready = state == STATE_WAIT_1ST_READ || state == STATE_WAIT_2ND_READ || state == STATE_DISCARD_FLUSHED_READ;

assign sys_bus.awaddr = 'x;
assign sys_bus.awprot = 'x;
assign sys_bus.awvalid = 0;

assign sys_bus.wdata = 'x;
assign sys_bus.wstrb = 'x;
assign sys_bus.wvalid = 0;
assign sys_bus.bready = 0;

generate
	if (basic_cache_params::data_size != 64)
		$error("icache's data_size must be 64bit (required by ifetch)");
endgenerate

basic_cache icache(
	.clk,
	.write_enable(icache_write_enable),
	.waddr(icache_waddr),
	.wdata(icache_wdata),
	.raddr(icache_raddr),
	.rdata(icache_rdata),
	.lookup_valid(icache_lookup_valid)
);

logic icache_write_enable;
logic [basic_cache_params::aligned_addr_size-1:0] icache_waddr;
logic [basic_cache_params::data_size-1:0] icache_wdata;
logic [basic_cache_params::aligned_addr_size-1:0] icache_raddr;
wire [basic_cache_params::data_size-1:0] icache_rdata;
wire icache_lookup_valid;

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

reg bus_read_pending;
always @(posedge clk) begin
    if (rst)
        bus_read_pending <= '0;
    else if (sys_bus.arvalid && sys_bus.arready)
        bus_read_pending <= '1;
    else if (sys_bus.rready && sys_bus.rvalid)
        bus_read_pending <= '0; 
end    

// Read cache lines
always_comb begin
	`ifndef SYNTHESIS
	unique // Yosys does not parse "unique if" ...
	`endif
	if (state == STATE_START_1ST_LOOKUP_FROM_PC)
		icache_raddr = next_fetch_pc_comb[$size(next_fetch_pc_comb)-1 -: $size(icache_raddr)];
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

// Write cache lines
always_comb begin
    if (rst || flush) begin
        icache_write_enable = 'b0;
        icache_waddr = 'x;
        icache_wdata = 'x;
    end else if ((state == STATE_WAIT_1ST_READ || state == STATE_WAIT_2ND_READ) && sys_bus.rvalid) begin
		// We update fetch_pc after the 1st read is done, so this fetch_pc is in fact at the 2nd line's address in WAIT_2ND_READ!
        icache_waddr = fetch_pc[$size(fetch_pc)-1 : basic_cache_params::align_bits];
		icache_wdata = sys_bus.rdata;
    	icache_write_enable = 'b1;
    end else begin
		`ifndef SYNTHESIS
		if (sys_bus.rvalid)
        	$error("Trying to write a cache line in an unexpected state!");
        `endif
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
		next_fetch_pc_comb = 'x; // Very long chain in other branches, just use pc directly in this state (opt can't see that)
	end else if (state == STATE_CHECK_1ST_LOOKUP) begin
        // By switching on fetch_crosses_lines, we can get all the high bits from either fetch_pc or next_cache_line_addr
        // This avoids a very wide addition, and we can also exclude the last bit from the math since it's always 0 (2B alignment)
        next_line_offset_comb = {fetch_pc[1 +: basic_cache_params::align_bits-1] + (is_cache_compressed_instr ? 'h1 : 'h2), 1'b0};
        if (cache_next_instr_on_next_line)
            next_fetch_pc_comb = {next_cache_line_addr, next_line_offset_comb};
        else
            next_fetch_pc_comb = {fetch_pc[$size(fetch_pc)-1 : basic_cache_params::align_bits], next_line_offset_comb};
            
        `ifndef SYNTHESIS
		if (!icache_lookup_valid)
			next_fetch_pc_comb = 'x;
		`endif
	end else if (state == STATE_WAIT_1ST_READ) begin
        next_line_offset_comb = {fetch_pc[1 +: basic_cache_params::align_bits-1] + (is_bus_compressed_instr ? 'h1 : 'h2), 1'b0};
        if (bus_next_instr_on_next_line)
            next_fetch_pc_comb = {next_cache_line_addr, next_line_offset_comb};
        else
            next_fetch_pc_comb = {fetch_pc[$size(fetch_pc)-1 : basic_cache_params::align_bits], next_line_offset_comb};
        
		`ifndef SYNTHESIS
		if (!sys_bus.rvalid)
			next_fetch_pc_comb = 'x;
		`endif
	end else begin
        next_line_offset_comb = 'x;
		next_fetch_pc_comb = 'x;
	end
end

always @(posedge clk) begin
	if (rst || flush) begin
		// Input PC is NOT guaranteed to be stable (or even valid) in rst, so of course we need a cycle just to start the read
		state <= bus_read_pending ? STATE_DISCARD_FLUSHED_READ : STATE_START_1ST_LOOKUP_FROM_PC;
		fetch_pc <= 'x;
		next_cache_line_addr <= 'x;
        instruction_next_addr <= 'x;
	end else unique case (state)
	STATE_START_1ST_LOOKUP_FROM_PC: begin
        if (pc[0]) // Alignment exception
            state <= STATE_EXCEPTION;
        else
		    state <= STATE_CHECK_1ST_LOOKUP;
		fetch_pc <= pc;
		next_cache_line_addr <= pc[$bits(pc)-1:basic_cache_params::align_bits] + 1;
	end
	STATE_CHECK_1ST_LOOKUP: begin
		if (icache_lookup_valid) begin
			// Whether we go to 2nd read or the next instruction, those are updated as soon as we get the 1st instruction (see WAIT_1ST_READ for details)
			fetch_pc <= next_fetch_pc_comb;
            instruction_next_addr <= next_fetch_pc_comb;
            if (cache_next_instr_on_next_line)
                next_cache_line_addr <= next_cache_line_addr + 1;

            if (icache_rdata[line_instr_offset +: 5] == 5'b11111) begin
                state <= STATE_EXCEPTION; // Instr too long
			end else if (cache_fetch_crosses_lines) begin
				state <= STATE_CHECK_2ND_LOOKUP;
			end else if (next_stalled) begin
				state <= STATE_STALLED;
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
            instruction_next_addr <= next_fetch_pc_comb;
            if (bus_next_instr_on_next_line)
                next_cache_line_addr <= next_cache_line_addr + 1;
		
            if (sys_bus.rdata[line_instr_offset +: 5] == 5'b11111) begin
                state <= STATE_EXCEPTION; // Instr too long
			end else if (!bus_fetch_crosses_lines || icache_lookup_valid) begin // We do a 2nd lookup check at the same time as the 1st read finishes to save a cycle
				state <= next_stalled ? STATE_STALLED : STATE_CHECK_1ST_LOOKUP;
			end else begin
				state <= STATE_START_2ND_READ;
            end
		end
	end
	STATE_CHECK_2ND_LOOKUP: begin
		if (icache_lookup_valid) begin
			// Cache stays primed at fetch_pc. Since we JUST crossed, we know we'll just be reading the same line again
			state <= next_stalled ? STATE_STALLED : STATE_CHECK_1ST_LOOKUP;
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
			state <= next_stalled ? STATE_STALLED : STATE_CHECK_1ST_LOOKUP;
	end
	STATE_STALLED: begin
		if (!next_stalled)
			state <= STATE_CHECK_1ST_LOOKUP;
	end
    STATE_DISCARD_FLUSHED_READ: begin
        if (sys_bus.rvalid
            || !bus_read_pending) // If we flush during a response cycle, we would miss the rvalid
            state <= STATE_START_1ST_LOOKUP_FROM_PC;
    end
    STATE_EXCEPTION: begin
        // Stay here until reset
    end
	endcase
end

// Outputs
always @(posedge clk) begin
    if (rst || flush) begin
        stall_next <= '1;
        ifetch_exception <= 'x;
        instruction <= 'x;
        instruction_addr <= 'x;
    end else begin: update_outputs
		logic [`ILEN-1:0] next_instruction;
		logic invalid_len_exception;

		`ifndef SYNTHESIS
		unique // Yosys does not parse "unique if"
		`endif
		// Note that we report alignment exceptions on the next cycle when entering STATE_EXCEPTION. It's not a huge priority to optimize.
        if (state == STATE_EXCEPTION) begin
            next_instruction = 'x;
            stall_next <= '0;
		end else if (state == STATE_STALLED) begin
			next_instruction = instruction;
            stall_next <= !next_stalled;
        // Only one line to read (note: we'll get trailing Xs reading compressed instrs at the end of a line due to +: `ILEN, but that's okay)
        end else if (state == STATE_WAIT_1ST_READ && sys_bus.rvalid && !bus_fetch_crosses_lines) begin
            next_instruction = sys_bus.rdata[line_instr_offset +: `ILEN];
            stall_next <= '0;
        end else if (state == STATE_CHECK_1ST_LOOKUP && icache_lookup_valid && !cache_fetch_crosses_lines) begin
            next_instruction = icache_rdata[line_instr_offset +: `ILEN];
            stall_next <= '0;
        // Complete instruction with 2nd read
        end else if (state == STATE_WAIT_2ND_READ && sys_bus.rvalid) begin
            next_instruction = {sys_bus.rdata[0 +: 16], instruction[0 +: `ILEN - 16]};
            stall_next <= '0;
        end else if (state == STATE_CHECK_2ND_LOOKUP && icache_lookup_valid) begin
            next_instruction = {icache_rdata[0 +: 16], instruction[0 +: `ILEN - 16]};
            stall_next <= '0;
        // Partial 1st read, potentially immediately completed by 2nd lookup from cache
        end else if (state == STATE_WAIT_1ST_READ && sys_bus.rvalid && bus_fetch_crosses_lines) begin
            next_instruction = {icache_rdata[0 +: 16], sys_bus.rdata[$size(sys_bus.rdata)-1 -: 16]};
            stall_next <= !icache_lookup_valid;
        end else if (state == STATE_CHECK_1ST_LOOKUP && icache_lookup_valid && cache_fetch_crosses_lines) begin
            next_instruction = {16'bx, icache_rdata[$size(icache_rdata)-1 -: 16]}; // A 1st lookup can't complete simultaneously w/ a 2nd, so just xpad
            stall_next <= '1;
        // Yay more waiting. This pipeline isn't called bubbly for nothing
        end else begin
			next_instruction = instruction;
            stall_next <= '1;
        end
        
        // This is safe, we go through this state exactly once per instruction, and only when unstalled
        if (state == STATE_CHECK_1ST_LOOKUP)
            instruction_addr <= fetch_pc;
        else if (state == STATE_STALLED)
            instruction_addr <= 'x;
		
		invalid_len_exception = next_instruction[4:0] == 'b11111;
        if (invalid_len_exception)
            next_instruction = 'x;
        
		instruction <= next_instruction;
		ifetch_exception <= invalid_len_exception || state == STATE_EXCEPTION;
    end
end

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (sys_bus.rvalid |-> sys_bus.rresp === AXI4LITE_RESP_OKAY);
    assert property (state == STATE_EXCEPTION && !rst && !flush |=> instruction === 'x);
    assert property (state == STATE_EXCEPTION && !rst && !flush |=> ifetch_exception);
    assert property (!$isunknown(fetch_pc) |-> next_cache_line_addr == fetch_pc[$bits(fetch_pc)-1:basic_cache_params::align_bits] + 1);
end
`endif

endmodule