`include "params.svh"

module int_regfile(
    input clk,
    input rst,

    input bit write1_enable,
    input [4:0] write1_sel,
    input [`XLEN-1:0] write1_data,

    input [4:0] read1_sel,
    output logic [`XLEN-1:0] read1_data,
    input [4:0] read2_sel,
    output logic [`XLEN-1:0] read2_data,
    input [4:0] read3_sel,
    output logic [`XLEN-1:0] read3_data
);

reg [`XLEN-1:0] xreg [1:31];

always_comb begin
    read1_data = read1_sel == '0 ? '0 : xreg[read1_sel];
    read2_data = read2_sel == '0 ? '0 : xreg[read2_sel];
    read3_data = read3_sel == '0 ? '0 : xreg[read3_sel];
end

integer i;
always @(posedge clk) begin
    if (rst) begin
        // NOTE: Regs can't be cleared in one cycle here, must be handled by the core after reset
    end else begin
        if (write1_enable)
            xreg[write1_sel] <= write1_data;
    end
end

endmodule