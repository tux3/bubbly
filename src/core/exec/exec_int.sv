`include "../params.svh"

module exec_int(
    input clk,
    input rst,
    input [`ALEN-1:0] decode_instruction_addr,
    input [4:0] opcode,
    input [4:0] rd,
    input [2:0] funct3,
    input [4:0] rs1,
    input [4:0] rs2,
    input [6:0] funct7,
    input [31:12] u_imm,
    
    input input_valid,
    input input_is_int,
    
    output reg exec_int_output_valid,
    output reg exec_int_exception,
    output reg [`XLEN-1:0] exec_int_result,
);

always_ff @(posedge clk) begin
    if (rst)
        exec_int_output_valid <= '0;
    else
        exec_int_output_valid <= input_valid && input_is_int;
end   

always_ff @(posedge clk) begin
    if (opcode == decode_types::OP_LUI) begin
        exec_int_exception <= '0;
        exec_int_result <= {{`XLEN-31{u_imm[31]}}, u_imm[30:12], 12'b0};
    end else begin
        exec_int_exception <= '1;
        exec_int_result <= 'x;
    end
end

endmodule