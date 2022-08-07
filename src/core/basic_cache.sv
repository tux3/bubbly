`include "params.svh"

// Do not blindly modify params. The basic_cache is not fully parametrized, and also interracts with the `ALEN parameter
package basic_cache_params;
localparam data_size = 64;
localparam bram_blocks = 6; // Adjust to match ALEN
localparam bram_addr_width = 8;
localparam bram_block_data_width = 16;
localparam align_bits = $clog2(data_size/8);
localparam aligned_addr_size = `ALEN - align_bits;
localparam entry_size = bram_blocks*bram_block_data_width;
localparam tag_size = entry_size - data_size;
endpackage

// Our basic_cache stores 64bits of data (64bit aligned), with 32 bits of tags we match ALEN=43, at 96bit per entry
// On the iCE40 a BRAM is 4kbits 16-bit addressable, so we fit 256*96bit entries in 6 BRAMs
// Cache line entry format: | Tag | Data |
module basic_cache #(
    // Checking the tag early prevents dcache from being in a hard BRAM block, spends more time in
    // the cycle setting up the read, but saves combinatorial time at the start of the cycle reading results
    parameter CHECK_TAG_EARLY = 0
) (
	input clk,
	input rst,
	input write_enable,
	input [basic_cache_params::aligned_addr_size-1:0] waddr,
	input [basic_cache_params::data_size-1:0] wdata,
	input [basic_cache_params::aligned_addr_size-1:0] raddr,
	output logic [basic_cache_params::data_size-1:0] rdata,
	output logic lookup_valid
);

// The basic_cache's width and tag size depend directly on `ALEN, make sure everything is correct before changing this
generate
	if (basic_cache_params::aligned_addr_size != basic_cache_params::bram_addr_width + basic_cache_params::tag_size)
		$error("basic_cache's aligned_addr_size is inconsistent with other params");
	if (basic_cache_params::entry_size != basic_cache_params::tag_size + basic_cache_params::data_size)
		$error("basic_cache's entry_size is inconsistent with other params");
endgenerate

wire [basic_cache_params::bram_blocks-1:0] write_mask = {basic_cache_params::bram_blocks{write_enable}};
logic [basic_cache_params::bram_addr_width-1:0] line_waddr;
logic [basic_cache_params::entry_size-1:0] line_wdata;
logic [basic_cache_params::bram_addr_width-1:0] line_raddr;
logic [basic_cache_params::entry_size-1:0] line_rdata;

logic [(1<<basic_cache_params::bram_addr_width)-1:0] valid_bits;

logic [basic_cache_params::tag_size-1:0] cur_raddr_tag;
wire [basic_cache_params::tag_size-1:0] entry_tag = line_rdata[basic_cache_params::data_size +: basic_cache_params::tag_size];

always_comb begin: bram_io
	logic [basic_cache_params::tag_size-1:0] cur_waddr_tag;
	cur_waddr_tag = waddr[$size(waddr)-1 -: basic_cache_params::tag_size];
	line_waddr = waddr[0 +: basic_cache_params::bram_addr_width];
	line_wdata = {cur_waddr_tag, wdata};

	cur_raddr_tag = raddr[$size(raddr)-1 -: basic_cache_params::tag_size];
	line_raddr = raddr[0 +: basic_cache_params::bram_addr_width];
	rdata = line_rdata[0 +: basic_cache_params::data_size];
end

logic [basic_cache_params::entry_size-1:0] mem [(1<<basic_cache_params::bram_addr_width-1):0];
logic [basic_cache_params::entry_size-1:0] mem_read_buf;

generate
if (CHECK_TAG_EARLY) begin
    logic [basic_cache_params::entry_size-1:0] mem_read_comb;
    logic tag_matches_comb;
    logic valid_buf_comb;

    always_comb begin
        mem_read_comb = (write_enable && line_raddr == line_waddr) ? line_wdata : mem[line_raddr];
        valid_buf_comb = (write_enable && line_raddr == line_waddr) ? '1 : valid_bits[line_raddr];
        tag_matches_comb = cur_raddr_tag == mem_read_comb[basic_cache_params::data_size +: basic_cache_params::tag_size];
        line_rdata = mem_read_buf;
    end
    
    always_ff @(posedge clk) begin
        mem_read_buf <= mem_read_comb;
        lookup_valid <= valid_buf_comb && tag_matches_comb;
    end
end else begin
    logic [basic_cache_params::entry_size-1:0] line_wdata_buf;
    logic [basic_cache_params::tag_size-1:0] last_raddr_tag;
    logic [basic_cache_params::bram_addr_width-1:0] valid_raddr;
    logic read_from_write;
    wire entry_valid = valid_bits[valid_raddr];

    always_comb begin
        if (read_from_write)
            line_rdata = line_wdata_buf;
        else
            line_rdata = mem_read_buf;
        lookup_valid = entry_valid && last_raddr_tag == entry_tag;
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            read_from_write <= 'x;
            last_raddr_tag <= 'x;
            line_wdata_buf <= 'x;
            mem_read_buf <= 'x;
            valid_raddr <= '0;
        end else begin
            read_from_write <= write_enable && line_raddr == line_waddr;
            last_raddr_tag <= cur_raddr_tag;
            valid_raddr <= line_raddr;
            if (write_enable)
                line_wdata_buf <= line_wdata; 
            mem_read_buf <= mem[line_raddr];
        end
    end
end
endgenerate

always_ff @(posedge clk)
    if (write_enable)
        mem[line_waddr] <= line_wdata;

always_ff @(posedge clk) begin
    if (rst) begin
        valid_bits <= '0;
    end else begin
        if (write_enable)
            valid_bits[line_waddr] <= 1'b1;
    end
end

endmodule
