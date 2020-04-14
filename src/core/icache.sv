`include "params.svh"

// Do not blindly modify params. The icache is not fully parametrized, and also interracts with the `ALEN parameter
package icache_params;
localparam instr_size = 64; // Up to two uncompressed instructions / four compressed
localparam align_bits = $clog2(instr_size/8);
localparam aligned_addr_size = `ALEN - align_bits;
localparam flags_size = 1; // Valid flag
localparam bram_blocks = 6;
localparam bram_addr_width = 8;
localparam bram_block_data_width = 16;
localparam entry_size = bram_blocks*bram_block_data_width;
localparam tag_size = entry_size - instr_size - flags_size;
endpackage

// Our icache stores 64bits of instructions (64bit aligned), with ALEN=42 it requires 31 bits of tags (and valid 1bit), for 96bit per entry
// On the iCE40 a BRAM is 4kbits 16-bit addressable, so we fit 256*96bit icache entries in 6 BRAMs
// Cache line entry format: | Tag | Valid | Data |
module icache (
	input clk,
	input write_enable,
	input [icache_params::aligned_addr_size-1:0] waddr,
	input [icache_params::instr_size-1:0] wdata,
	input [icache_params::aligned_addr_size-1:0] raddr,
	output logic [icache_params::instr_size-1:0] rdata,
	output logic lookup_valid
);

// The icache's width and tag size depend directly on `ALEN, make sure everything is correct before changing this
generate
	if (`ALEN != 42)
		$error("Cannot change `ALEN without updating the icache!");
	if (icache_params::aligned_addr_size != icache_params::bram_addr_width + icache_params::tag_size)
		$error("icache's aligned_addr_size is inconsistent with other params");
	if (icache_params::entry_size != icache_params::tag_size + icache_params::flags_size + icache_params::instr_size)
		$error("icache's entry_size is inconsistent with other params");
endgenerate

wire [icache_params::bram_blocks-1:0] write_mask = {icache_params::bram_blocks{write_enable}};
logic [icache_params::bram_addr_width-1:0] line_waddr;
logic [icache_params::entry_size-1:0] line_wdata;
logic [icache_params::bram_addr_width-1:0] line_raddr;
wire [icache_params::entry_size-1:0] line_rdata;

bram #(
    .read_after_write(1),
    .blocks(icache_params::bram_blocks),
    .block_addr_width(icache_params::bram_addr_width),
    .block_data_width(icache_params::bram_block_data_width)
) bram_icache (
    .wclk(clk),
    .rclk(clk),
	.write_mask,
    .waddr(line_waddr),
    .raddr(line_raddr),
    .wdata(line_wdata),
    .rdata(line_rdata)
);

logic [icache_params::tag_size-1:0] cur_raddr_tag;
logic [icache_params::tag_size-1:0] last_raddr_tag;
wire [icache_params::instr_size-1:0] entry_instructions = line_rdata[0 +: icache_params::instr_size];
wire [0:0] entry_valid = line_rdata[icache_params::instr_size];
wire [icache_params::tag_size-1:0] entry_tag = line_rdata[icache_params::instr_size+icache_params::flags_size +: icache_params::tag_size];
	
always_comb begin: bram_io
	logic [icache_params::tag_size-1:0] cur_waddr_tag;
	cur_waddr_tag = waddr[$size(waddr)-1 -: icache_params::tag_size];
	line_waddr = waddr[0 +: icache_params::bram_addr_width];
	line_wdata = {cur_waddr_tag, 1'b1, wdata};
	
	cur_raddr_tag = raddr[$size(raddr)-1 -: icache_params::tag_size];
	line_raddr = raddr[0 +: icache_params::bram_addr_width];
	rdata = line_rdata[0 +: icache_params::instr_size];
	lookup_valid = entry_valid && last_raddr_tag == entry_tag;
end

always_ff @(posedge clk)
	last_raddr_tag <= cur_raddr_tag;

endmodule
