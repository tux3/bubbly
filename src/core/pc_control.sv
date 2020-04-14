`include "params.svh"

module pc_control(
    input clk, rst,
    input instr_retired,
    input [`ALEN-1:0] next_pc,
    output reg [`XLEN-1:0] pc,
);

always_ff @(posedge clk) begin
    if (rst)
        pc <= `RESET_PC;
    else if (instr_retired)
        pc <= next_pc;
end

endmodule
