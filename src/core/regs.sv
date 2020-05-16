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

bit [`XLEN-1:0] xreg [1:31];

always_comb begin
    read1_data = read1_sel == '0 ? '0 : xreg[read1_sel];
    read2_data = read2_sel == '0 ? '0 : xreg[read2_sel];
    read3_data = read3_sel == '0 ? '0 : xreg[read3_sel];
end

integer i;
always @(posedge clk) begin
    if (rst) begin
        // No Yosys support for the fun barely-synthetizable SV syntax :(
        //xreg <= '{default:'0};
        
        for (i=1; i<=$size(xreg); i=i+1) begin
            xreg[i] <= '0;
        end
    end else begin
        if (write1_enable)
            xreg[write1_sel] <= write1_data;
    end
end

endmodule