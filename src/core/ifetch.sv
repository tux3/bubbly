`include "params.svh"
`include "../axi4lite.svh"

module ifetch(
    input clk, rst,
    input [`ALEN-1:0] pc,
    output reg stall_next,
    output reg ifetch_exception,
    output reg [`ILEN-1:0] instruction, // Valid only if !ifetch_exception

    axi4lite.master sys_bus,
);

assign sys_bus.aclk = clk;
assign sys_bus.aresetn = !rst;

assign sys_bus.arvalid = state == STATE_START_1ST_READ || state == STATE_START_2ND_READ;
assign sys_bus.araddr = fetch_pc[$size(fetch_pc)-1:icache_params::align_bits] << icache_params::align_bits; // fetch_pc is updated before 2nd reads, so stays valid for both
assign sys_bus.arprot = 'b000;

assign sys_bus.rready = state == STATE_WAIT_1ST_READ || state == STATE_WAIT_2ND_READ;

assign sys_bus.awaddr = 'x;
assign sys_bus.awprot = 'x;
assign sys_bus.awvalid = 0;

assign sys_bus.wdata = 'x;
assign sys_bus.wstrb = 'x;
assign sys_bus.wvalid = 0;
assign sys_bus.bready = 0;

icache icache(
	.clk,
	.write_enable(icache_write_enable),
	.waddr(icache_waddr),
	.wdata(icache_wdata),
	.raddr(icache_raddr),
	.rdata(icache_rdata),
	.lookup_valid(icache_lookup_valid)
);

logic icache_write_enable;
logic [icache_params::aligned_addr_size-1:0] icache_waddr;
logic [icache_params::instr_size-1:0] icache_wdata;
logic [icache_params::aligned_addr_size-1:0] icache_raddr;
wire [icache_params::instr_size-1:0] icache_rdata;
wire icache_lookup_valid;

enum { STATE_START_1ST_LOOKUP_FROM_PC, STATE_CHECK_1ST_LOOKUP, STATE_START_1ST_READ, STATE_WAIT_1ST_READ, STATE_CHECK_2ND_LOOKUP, STATE_START_2ND_READ, STATE_WAIT_2ND_READ, STATE_EXCEPTION } state;
logic [`ALEN-1:0] fetch_pc;
logic [`ALEN-1:0] next_fetch_pc_comb;
logic [icache_params::aligned_addr_size-1:0] next_cache_line_addr;
logic alignment_exception;

// A cache line is addressed by align_bits bits, fetch_pc is 8bit aligned, and instr are 16bit aligned so that's $clog2(16)=4 trailing zeros
wire [icache_params::instr_size-1:0] cache_line_instr_offset = {fetch_pc[1 +: icache_params::align_bits-1], 1'b0, 3'b000};
wire is_cache_compressed_instr = icache_rdata[cache_line_instr_offset +: 2] != 2'b11;
wire is_bus_compressed_instr = sys_bus.rdata[cache_line_instr_offset +: 2] != 2'b11;
wire cache_fetch_crosses_lines = !is_cache_compressed_instr && cache_line_instr_offset[$size(cache_line_instr_offset)-1 : 3] == 'h6; // 2 bytes are cut off
wire bus_fetch_crosses_lines = !is_bus_compressed_instr && cache_line_instr_offset[$size(cache_line_instr_offset)-1 : 3] == 'h6; // 2 bytes are cut off

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
	else if (state == STATE_WAIT_2ND_READ || state == STATE_CHECK_2ND_LOOKUP)
		icache_raddr = fetch_pc[$size(fetch_pc)-1 -: $size(icache_raddr)]; // fetch_pc has been updated after the 1st read, is now the next line (due to crossing)
	else
		icache_raddr = 'x;
end

// Write cache lines
always_comb begin
    if (rst) begin
        icache_write_enable = 'b0;
        icache_waddr = 'x;
        icache_wdata = 'x;
    end else if ((state == STATE_WAIT_1ST_READ || state == STATE_WAIT_2ND_READ) && sys_bus.rvalid) begin
		// We update fetch_pc after the 1st read is done, so this fetch_pc is in fact at the 2nd line's address in WAIT_2ND_READ!
        icache_waddr = fetch_pc[$size(fetch_pc)-1 : icache_params::align_bits];
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
		next_fetch_pc_comb = pc;
	end else if (state == STATE_CHECK_1ST_LOOKUP) begin
		next_fetch_pc_comb = fetch_pc + (is_cache_compressed_instr ? 'h2 : 'h4);
	end else if (state == STATE_WAIT_1ST_READ) begin
		next_fetch_pc_comb = fetch_pc + (is_bus_compressed_instr ? 'h2 : 'h4);
		`ifndef SYNTHESIS
		if (!sys_bus.rvalid)
			next_fetch_pc_comb = 'x;
		`endif
	end else begin
		next_fetch_pc_comb = 'x;
	end
end

always @(posedge clk) begin
	if (rst) begin
		// Input PC is NOT guaranteed to be stable (or even valid) in rst, so of course we need a cycle just to start the read
		state <= STATE_START_1ST_LOOKUP_FROM_PC;
		fetch_pc <= 'x;
		next_cache_line_addr <= 'x;
	end else unique case (state)
	STATE_START_1ST_LOOKUP_FROM_PC: begin
        if (alignment_exception)
            state <= STATE_EXCEPTION;
        else
		    state <= STATE_CHECK_1ST_LOOKUP;
		fetch_pc <= next_fetch_pc_comb;
		next_cache_line_addr <= next_fetch_pc_comb[$bits(next_fetch_pc_comb)-1:icache_params::align_bits] + 1;
	end
	STATE_CHECK_1ST_LOOKUP: begin
		if (icache_lookup_valid) begin
			// Whether we go to 2nd read or the next instruction, those are updated as soon as we get the 1st instruction (see WAIT_1ST_READ for details)
			fetch_pc <= next_fetch_pc_comb;
			next_cache_line_addr <= next_fetch_pc_comb[$bits(next_fetch_pc_comb)-1:icache_params::align_bits] + 1;

            if (icache_rdata[cache_line_instr_offset +: 5] == 5'b11111) begin
                state <= STATE_EXCEPTION; // Instr too long
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
			next_cache_line_addr <= next_fetch_pc_comb[$bits(next_fetch_pc_comb)-1:icache_params::align_bits] + 1;
		
            if (sys_bus.rdata[cache_line_instr_offset +: 5] == 5'b11111) begin
                state <= STATE_EXCEPTION; // Instr too long
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
    STATE_EXCEPTION: begin
        // Stay here until reset
    end
	endcase
end

// Outputs
always @(posedge clk) begin
    if (rst) begin
        stall_next <= '1;
        ifetch_exception <= 'x;
        instruction <= 'x;
        alignment_exception = 'x;
    end else begin: update_outputs
		logic [`ILEN-1:0] next_instruction;
		logic invalid_len_exception;
		
		// Note that this must preserve the unique if, this is not a priority condition
		alignment_exception = state == STATE_START_1ST_LOOKUP_FROM_PC && pc[0];

		`ifndef SYNTHESIS
		unique // Yosys does not parse "unique if"
		`endif
		// Alignment exception can happen if pc is not 2B aligned
        if (alignment_exception || state == STATE_EXCEPTION) begin
            next_instruction = 'x;
            stall_next <= '0;
        // Only one line to read (note: we'll get trailing Xs reading compressed instrs at the end of a line due to +: `ILEN, but that's okay)
        end else if (state == STATE_WAIT_1ST_READ && sys_bus.rvalid && !bus_fetch_crosses_lines) begin
            next_instruction = sys_bus.rdata[cache_line_instr_offset +: `ILEN];
            stall_next <= '0;
        end else if (state == STATE_CHECK_1ST_LOOKUP && icache_lookup_valid && !cache_fetch_crosses_lines) begin
            next_instruction = icache_rdata[cache_line_instr_offset +: `ILEN];
            stall_next <= '0;
        // Partial 1st read, potentially immediately completed by 2nd lookup from cache
        end else if (state == STATE_WAIT_1ST_READ && sys_bus.rvalid && bus_fetch_crosses_lines) begin
            next_instruction = {icache_rdata[0 +: 16], sys_bus.rdata[$size(sys_bus.rdata)-1 -: 16]};
            stall_next <= !icache_lookup_valid;
        end else if (state == STATE_CHECK_1ST_LOOKUP && icache_lookup_valid && cache_fetch_crosses_lines) begin
            next_instruction = {16'bx, icache_rdata[$size(icache_rdata)-1 -: 16]}; // A 1st lookup can't complete simultaneously w/ a 2nd, so just xpad
            stall_next <= '1;
        // Complete instruction with 2nd read
        end else if (state == STATE_WAIT_2ND_READ && sys_bus.rvalid) begin
            next_instruction = {sys_bus.rdata[0 +: 16], instruction[0 +: `ILEN - 16]};
            stall_next <= '0;
        end else if (state == STATE_CHECK_2ND_LOOKUP && icache_lookup_valid) begin
            next_instruction = {icache_rdata[0 +: 16], instruction[0 +: `ILEN - 16]};
            stall_next <= '0;
        // Yay more waiting. This pipeline isn't called bubbly for nothing
        end else begin
			next_instruction = instruction;
            stall_next <= '1;
        end
		
		invalid_len_exception = next_instruction[4:0] == 'b11111;
        if (invalid_len_exception)
            next_instruction = 'x;
        
		instruction <= next_instruction;
		ifetch_exception <= alignment_exception || invalid_len_exception || state == STATE_EXCEPTION;
    end
end

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (sys_bus.rvalid |-> sys_bus.rresp === AXI4LITE_RESP_OKAY);
    assert property (alignment_exception |=> rst || instruction === 'x);
    assert property (alignment_exception |=> rst || ifetch_exception);
end
`endif

endmodule