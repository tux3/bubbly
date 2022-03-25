// Address and data width are extremely target-specific (iCE40 can do e.g. 8*16 or 9*8)
module bram_block #(
    parameter read_after_write = 0,
    parameter addr_width = 8,
    parameter data_width = 16
) (
    input [addr_width-1:0] waddr,
    input [addr_width-1:0] raddr,
    input [data_width-1:0] wdata,
    input write_enable,
    input clk,
    output logic [data_width-1:0] rdata
);
    logic [data_width-1:0] mem [(1<<addr_width)-1:0];

    `ifndef SYNTHESIS
    initial begin
        for (int i = 0; i<(1<<data_width); i = i+1)
            mem[i] = '0;
    end
    `endif

    generate
        if (read_after_write) begin
            reg conflict;
            reg [data_width-1:0] written_data;
            reg [data_width-1:0] rdata_reg;
            assign rdata = conflict ? written_data : rdata_reg;
            always_ff @(posedge clk)
                rdata_reg <= mem[raddr];

            always_ff @(posedge clk)
                if (write_enable)
                    written_data <= wdata;

            always_ff @(posedge clk)
                conflict <= write_enable && raddr == waddr;

            always_ff @(posedge clk)
                if (write_enable)
                    mem[waddr] <= wdata;
        end else begin
            always_ff @(posedge clk)
                rdata <= mem[raddr];

            always_ff @(posedge clk)
                if (write_enable)
                    mem[waddr] <= wdata;
        end
    endgenerate
endmodule


module bram #(
    parameter read_after_write = 0,  // Reads to the same address as a write observe the new value
    parameter blocks = 1,            // More BRAM blocks increase bandwidth
    parameter block_addr_width = 8,  // Address width of the BRAM
    parameter block_data_width = 16, // Bits each BRAM block can r/w per cycle
    localparam data_width = block_data_width*blocks // Total bits/cycle bandwidth
) (
    input clk,
    input [block_addr_width-1:0] waddr,
    input [block_addr_width-1:0] raddr,
    input [data_width-1:0] wdata,
    input [blocks-1:0] write_mask,
    output [data_width-1:0] rdata
);
    genvar i;
    generate
        for (i=0; i<blocks; i=i+1) begin
            bram_block #(
                .read_after_write(read_after_write),
                .addr_width(block_addr_width),
                .data_width(block_data_width)
            ) bram_block (
                .clk,
                .waddr,
                .raddr,
                .wdata(wdata[i*block_data_width +: block_data_width]),
                .write_enable(write_mask[i]),
                .rdata(rdata[i*block_data_width +: block_data_width])
            );
        end
    endgenerate
endmodule
