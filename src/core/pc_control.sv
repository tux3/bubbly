`include "params.svh"

module pc_control(
    input clk, rst,
    input instr_retired,
    output reg [`XLEN-1:0] pc
);

// TODO: Support compressed instructions

always_ff @(posedge clk) begin
    if (rst) begin
        pc <= '0;
    end else begin
        if (instr_retired)
            pc <= pc + 'h4;
    end
end

endmodule
