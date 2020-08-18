`include "params.svh"

module pc(
    input clk, rst,
    input update_pc,
    input [`ALEN-1:0] next_pc,
    output reg [`XLEN-1:0] pc
);

always_ff @(posedge clk) begin
    if (rst)
        pc <= `RESET_PC;
    else if (update_pc)
        pc <= next_pc;
end

endmodule
