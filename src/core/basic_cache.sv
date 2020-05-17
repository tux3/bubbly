`include "params.svh"

// Do not blindly modify params. The basic_cache is not fully parametrized, and also interracts with the `ALEN parameter
package basic_cache_params;
localparam data_size = 64;
localparam align_bits = $clog2(data_size/8);
localparam aligned_addr_size = `ALEN - align_bits;
localparam flags_size = 1; // Valid flag
localparam bram_blocks = 6;
localparam bram_addr_width = 8;
localparam bram_block_data_width = 16;
localparam entry_size = bram_blocks*bram_block_data_width;
localparam tag_size = entry_size - data_size - flags_size;
endpackage

// Our basic_cache stores 64bits of data (64bit aligned), with ALEN=42 it requires 31 bits of tags (and valid 1bit), for 96bit per entry
// On the iCE40 a BRAM is 4kbits 16-bit addressable, so we fit 256*96bit entries in 6 BRAMs
// Cache line entry format: | Tag | Valid | Data |
module basic_cache (
	input clk,
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
	if (basic_cache_params::entry_size != basic_cache_params::tag_size + basic_cache_params::flags_size + basic_cache_params::data_size)
		$error("basic_cache's entry_size is inconsistent with other params");
endgenerate

wire [basic_cache_params::bram_blocks-1:0] write_mask = {basic_cache_params::bram_blocks{write_enable}};
logic [basic_cache_params::bram_addr_width-1:0] line_waddr;
logic [basic_cache_params::entry_size-1:0] line_wdata;
logic [basic_cache_params::bram_addr_width-1:0] line_raddr;
wire [basic_cache_params::entry_size-1:0] line_rdata;

bram #(
    .read_after_write(1),
    .blocks(basic_cache_params::bram_blocks),
    .block_addr_width(basic_cache_params::bram_addr_width),
    .block_data_width(basic_cache_params::bram_block_data_width)
) bram_basic_cache (
    .wclk(clk),
    .rclk(clk),
	.write_mask,
    .waddr(line_waddr),
    .raddr(line_raddr),
    .wdata(line_wdata),
    .rdata(line_rdata)
);

logic [basic_cache_params::tag_size-1:0] cur_raddr_tag;
logic [basic_cache_params::tag_size-1:0] last_raddr_tag;
wire [basic_cache_params::data_size-1:0] entry_instructions = line_rdata[0 +: basic_cache_params::data_size];
wire [0:0] entry_valid = line_rdata[basic_cache_params::data_size];
wire [basic_cache_params::tag_size-1:0] entry_tag = line_rdata[basic_cache_params::data_size+basic_cache_params::flags_size +: basic_cache_params::tag_size];

always_comb begin: bram_io
	logic [basic_cache_params::tag_size-1:0] cur_waddr_tag;
	cur_waddr_tag = waddr[$size(waddr)-1 -: basic_cache_params::tag_size];
	line_waddr = waddr[0 +: basic_cache_params::bram_addr_width];
	line_wdata = {cur_waddr_tag, 1'b1, wdata};

	cur_raddr_tag = raddr[$size(raddr)-1 -: basic_cache_params::tag_size];
	line_raddr = raddr[0 +: basic_cache_params::bram_addr_width];
	rdata = line_rdata[0 +: basic_cache_params::data_size];
	lookup_valid = entry_valid && last_raddr_tag == entry_tag;
end

always_ff @(posedge clk)
	last_raddr_tag <= cur_raddr_tag;

endmodule
