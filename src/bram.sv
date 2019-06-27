module bram_256_8 #(
	parameter addr_width = 9,
	parameter data_width = 8
) (
    input [addr_width-1:0] waddr,
    input [addr_width-1:0] raddr,
	input [data_width-1:0] din,
	input write_en,
	input wclk,
	input rclk,
	output reg [data_width-1:0] dout
);

reg [data_width-1:0] mem [(1<<addr_width)-1:0];

always @(posedge wclk)
    if (write_en)
        mem[waddr] <= din;

always @(posedge rclk)
    dout <= mem[raddr];

endmodule

module bram #(
	parameter blocks = 16,
	parameter block_addr_width = 9,
	parameter block_data_width = 8,
	parameter data_width = block_data_width*16
) (
    input [block_addr_width-1:0] waddr,
    input [block_addr_width-1:0] raddr,
	input [data_width-1:0] din,
	input write_en,
	input [data_width / 8 - 1:0] byte_write_mask,
	input wclk,
	input rclk,
	output [data_width-1:0] dout
);

genvar i;
generate
    for (i=0; i<blocks; i=i+1) begin
        bram_256_8 bram_inst(
            waddr,
            raddr,
            din[(i+1)*block_data_width-1:i*block_data_width],
            byte_write_mask[i],
            wclk,
            rclk,
            dout[(i+1)*block_data_width-1:i*block_data_width]
        );
    end
endgenerate

endmodule
