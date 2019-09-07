`include "params.svh"
`include "../axi4lite.svh"

module ifetch(
    input clk, rst,
    input [`ALEN-1:0] addr,
    input prev_stalled,
    output stall_prev,
    output reg stall_next,
    output reg ifetch_exception,
    output reg [`ILEN-1:0] instruction, // Valid only if !ifetch_exception

    axi4lite.master sys_bus,
);

// Pipeline handshake
//  - prev_stalled: Input data is NOT valid, can be asserted at any clock tick. Must not depend on stall_prev (like AXI)
//  - stall_prev: We are NOT ready to accept input data. Note that this is a wire output! When !stall_prev && !prev_stalled, we have a handshake and the input is accepted
//  - stall_next: Output data is NOT valid

assign sys_bus.arvalid = state == STATE_START_1ST_READ || state == STATE_START_2ND_READ;
assign sys_bus.araddr = (state == STATE_START_1ST_READ ? addr_buf[$size(addr_buf)-1:3] : second_addr_buf[$size(second_addr_buf)-1:3]) << 3;
assign sys_bus.arprot = 'b000;

assign sys_bus.rready = state == STATE_WAIT_1ST_READ || state == STATE_WAIT_2ND_READ;

assign sys_bus.awaddr = 'x;
assign sys_bus.awprot = 'x;
assign sys_bus.awvalid = 0;

assign sys_bus.wdata = 'x;
assign sys_bus.wstrb = 'x;
assign sys_bus.wvalid = 0;
assign sys_bus.bready = 0;

wire bus_has_instruction = (state == STATE_WAIT_1ST_READ || state == STATE_WAIT_2ND_READ) && sys_bus.rvalid;
wire cache_has_1st_instr = icache_lookup_valid && state == STATE_READY && next_addr_valid && next_addr_buf[$size(next_addr_buf)-1 -: icache_tag_size] == icache_lookup_tag;
wire cache_has_2nd_instr_after_check = icache_lookup_valid && state == STATE_CHECK_2ND_LOOKUP && second_addr_buf[$size(second_addr_buf)-1 -: icache_tag_size] == icache_lookup_tag;
wire cache_has_2nd_instr_after_1st_read = icache_lookup_valid && state == STATE_WAIT_1ST_READ && sys_bus.rvalid && second_addr_buf[$size(second_addr_buf)-1 -: icache_tag_size] == icache_lookup_tag;

// Next cycle is a second cache lookup. Note how we don't buffer lookup results, so we need to time our lookups the cycle before we need results
wire start_2nd_cache_lookup = state == STATE_WAIT_1ST_READ || (state == STATE_READY && next_addr_valid && !alignment_exception && fetch_crosses_lines);
// Instr must be 2B aligned
wire alignment_exception = state == STATE_READY && next_addr_valid && next_addr_buf[0];
// 4B instr may be 2B aligned, and our cache lines are 8B, so we need to read two cache lines if the addr is aligned on the 6th byte
wire fetch_crosses_lines = {state == STATE_READY ? next_addr_buf[2:1] : addr_buf[2:1], 1'b0} == 3'h6;

// We can't accept an address if the cache can't look it up next cycle, or if the 1st stage buffer is going to stay full
assign stall_prev = start_2nd_cache_lookup || (next_addr_valid && state != STATE_READY);

localparam STATE_READY = 'h0;
localparam STATE_START_1ST_READ = 'h1;
localparam STATE_WAIT_1ST_READ = 'h2;
localparam STATE_CHECK_2ND_LOOKUP = 'h3;
localparam STATE_START_2ND_READ = 'h4;
localparam STATE_WAIT_2ND_READ = 'h5;

logic [2:0] state;
logic [`ALEN-1:0] next_addr_buf;
logic [`ALEN-1:0] next_second_addr_buf;
logic next_addr_valid;
logic [`ALEN-1:0] addr_buf;
logic [`ALEN-1:0] second_addr_buf; // Address of the next cache line (aligned), for when the fetch crosses lines

// Our icache stores 64bits of instructions (64bit aligned), with ALEN=26 it requires 15 bits of tags (and valid 1bit), for 80bit per entry
// On the iCE40 a BRAM is 4kbits 16-bit addressable, so we fit 256*80bit icache entries in 5 BRAMs
// Cache line format: | Tag | Valid | Data |
localparam icache_blocks = 5;
localparam icache_addr_width = 8;
localparam icache_block_data_width = 16;
localparam icache_entry_size = icache_blocks*icache_block_data_width;
localparam icache_instr_size = 64; // Up to two uncompressed instructions / four compressed
localparam icache_flags_size = 1; // Valid flag
localparam icache_tag_size = icache_entry_size - icache_instr_size - icache_flags_size;

logic [icache_addr_width-1:0] icache_waddr;
logic [icache_entry_size-1:0] icache_wdata;
logic [icache_addr_width-1:0] icache_raddr;
logic [icache_entry_size-1:0] icache_rdata;
logic icache_write_enable;
wire [icache_blocks-1:0] icache_write_mask = {icache_blocks{icache_write_enable}};

wire [icache_instr_size-1:0] icache_lookup_instructions = icache_rdata[0 +: icache_instr_size];
wire [0:0] icache_lookup_valid = icache_rdata[icache_instr_size];
wire [icache_tag_size-1:0] icache_lookup_tag = icache_rdata[icache_instr_size+icache_flags_size +: icache_tag_size];

bram #(
    .read_after_write(1),
    .blocks(icache_blocks),
    .block_addr_width(icache_addr_width),
    .block_data_width(icache_block_data_width)
) icache (
    .wclk(clk),
    .rclk(clk),
    .waddr(icache_waddr),
    .raddr(icache_raddr),
    .wdata(icache_wdata),
    .write_mask(icache_write_mask),
    .rdata(icache_rdata)
);

// Outputs
always @(posedge clk, negedge rst) begin
    if (!rst) begin
        stall_next <= '1;
        ifetch_exception <= 'x;
        instruction <= 'x;
    end else begin: update_outputs
        logic [5:0] align_offset; // We read a 8B aligned cache line, this is the offset *in bits* to the 2B aligned instruction (only 4 possibilities!)
        align_offset = {state == STATE_READY ? next_addr_buf[2:1] : addr_buf[2:1], 1'b0, 3'b000};
    
        ifetch_exception <= alignment_exception;
        
        // Exceptions take priority, as usual
        if (alignment_exception) begin
            instruction <= 'x;
            stall_next <= '0;
        // Only one line to read
        end else if (!fetch_crosses_lines && state == STATE_WAIT_1ST_READ && sys_bus.rvalid) begin
            instruction <= sys_bus.rdata[align_offset +: `ILEN];
            stall_next <= '0;
        end else if (!fetch_crosses_lines && cache_has_1st_instr) begin
            instruction <= icache_lookup_instructions[align_offset +: `ILEN];
            stall_next <= '0;
        // Partial 1st read, potentially immediately completed by 2nd lookup from cache
        end else if (fetch_crosses_lines && state == STATE_WAIT_1ST_READ && sys_bus.rvalid) begin
            instruction <= {icache_lookup_instructions[0 +: 16], sys_bus.rdata[$size(sys_bus.rdata)-1 -: 16]};
            stall_next <= !cache_has_2nd_instr_after_1st_read;
        end else if (fetch_crosses_lines && cache_has_1st_instr) begin
            instruction <= {16'bx, icache_lookup_instructions[icache_instr_size-1 -: 16]}; // A 1st lookup can't complete simultaneously w/ a 2nd, so just xpad
            stall_next <= '1;
        // Complete instruction with 2nd read
        end else if (state == STATE_WAIT_2ND_READ && sys_bus.rvalid) begin
            instruction <= {sys_bus.rdata[0 +: 16], instruction[0 +: `ILEN - 16]};
            stall_next <= '0;
        end else if (cache_has_2nd_instr_after_check) begin
            instruction <= {icache_lookup_instructions[0 +: 16], instruction[0 +: `ILEN - 16]};
            stall_next <= '0;
        // Yay more waiting. This here pipeline ain't called bubbly for nothin'
        end else begin
            instruction <= fetch_crosses_lines ? instruction : 'x; // Just for the benefit of the simulator
            stall_next <= '1;
        end
    end
end

// First stage: handshake with prev, manage next_addr_buf and look it up in the cache
always @(posedge clk, negedge rst) begin
    if (!rst) begin
        next_addr_valid <= 'b0;
        next_addr_buf <= 'x;
        next_second_addr_buf <= 'x;
    end else begin
        if (!stall_prev && !prev_stalled) begin
            next_addr_valid <= 'b1;
            next_addr_buf <= addr;
            next_second_addr_buf <= {addr[$bits(addr)-1:3] + 1, 3'b000};
        end else if (state == STATE_READY) begin
            next_addr_valid <= 'b0;
            next_addr_buf <= 'x;
            next_second_addr_buf <= 'x;
        end
    end
end    

// Second stage: Main FSM, read from sys_bus, second cache lookup
always @(posedge clk, negedge rst) begin
    if (!rst) begin
        state <= STATE_READY;
        addr_buf <= 'x;
        second_addr_buf <= 'x;
    end else begin
        if (alignment_exception) begin
            // Exceptions take priority, we can handle them immediately
            addr_buf <= 'x;
            second_addr_buf <= 'x;
        end else if (state == STATE_READY && next_addr_valid && !fetch_crosses_lines && !cache_has_1st_instr) begin
            state <= STATE_START_1ST_READ;
            addr_buf <= next_addr_buf;
            second_addr_buf <= 'x;
        end else if (state == STATE_READY && next_addr_valid && fetch_crosses_lines) begin
            state <= cache_has_1st_instr ? STATE_CHECK_2ND_LOOKUP : STATE_START_1ST_READ;
            addr_buf <= next_addr_buf;
            second_addr_buf <= next_second_addr_buf;
        end else if (state == STATE_START_1ST_READ && sys_bus.arready) begin
            state <= STATE_WAIT_1ST_READ;
        end else if (state == STATE_WAIT_1ST_READ && sys_bus.rvalid) begin
            // Save a cycle by doing 2nd cache lookups during all STATE_WAIT_1ST_READ, instead of going to STATE_CHECK_2ND_LOOKUP after the read
            state <= (!fetch_crosses_lines || cache_has_2nd_instr_after_1st_read) ? STATE_READY : STATE_START_2ND_READ;
        end else if (state == STATE_CHECK_2ND_LOOKUP) begin
            state <= cache_has_2nd_instr_after_check ? STATE_READY : STATE_START_2ND_READ;
        end else if (state == STATE_START_2ND_READ && sys_bus.arready) begin
            state <= STATE_WAIT_2ND_READ;
        end else if (state == STATE_WAIT_2ND_READ && sys_bus.rvalid) begin
            state <= STATE_READY;
        end
    end
end

// Read cache lines
always_comb begin
    if (start_2nd_cache_lookup) begin
        icache_raddr = state == STATE_WAIT_1ST_READ ? second_addr_buf[3 +: icache_addr_width]
                                                     : next_second_addr_buf[3 +: icache_addr_width];
    end else begin
        icache_raddr = addr[3 +: icache_addr_width];
    end    
end

// Write cache lines
always @(posedge clk, negedge rst) begin
    if (!rst) begin
        icache_write_enable <= 'b0;
        icache_waddr <= 'x;
        icache_wdata <= 'x;
    end else begin
        if (bus_has_instruction) begin: write_cache_line
            logic [icache_tag_size-1:0] tag;
            logic valid_flag;
            
            valid_flag = 1'b1;
            if (state == STATE_WAIT_1ST_READ) begin
                tag = addr_buf[$size(addr_buf)-1 -: icache_tag_size];
                icache_waddr <= addr_buf[3 +: icache_addr_width];
            end else if (state == STATE_WAIT_2ND_READ) begin
                tag = second_addr_buf[$size(second_addr_buf)-1 -: icache_tag_size];
                icache_waddr <= second_addr_buf[3 +: icache_addr_width];
            end else begin
                `ifndef SYNTHESIS
                $error("Trying to write a cache line in an unexpected state!");
                `endif
            end
            
            icache_wdata <= {tag, valid_flag, sys_bus.rdata};
            icache_write_enable <= 'b1;
        end else begin
            icache_waddr <= 'x;
            icache_wdata <= 'x;
            icache_write_enable <= 'b0;
        end
    end
end

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (!prev_stalled |-> !$isunknown(addr));
    assert property (bus_has_instruction |-> sys_bus.rresp === AXI4LITE_RESP_OKAY);
    assert property (ifetch_exception |-> instruction === 'x);
    assert property (alignment_exception |=> ifetch_exception);
end
`endif

endmodule