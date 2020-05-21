`include "../params.svh"

module exec_mem(
    input clk,
    input rst,
    input [`ALEN-1:0] decode_instruction_addr,
    input [4:0] opcode,
    input [4:0] rd,
    input [2:0] funct3,
    input [4:0] rs1,
    input [4:0] rs2,
    input [`XLEN-1:0] rs1_data,
    input [`XLEN-1:0] rs2_data,
    input [6:0] funct7,
    input [31:20] i_imm,
    input [31:12] u_imm,
    
    input input_valid,
    input input_is_mem,
    
    output reg exec_mem_output_valid,
    output reg exec_mem_exception,
    output reg [`XLEN-1:0] exec_mem_result
);

always_ff @(posedge clk) begin
    if (rst)
        exec_mem_output_valid <= '0;
    else
        exec_mem_output_valid <= input_valid && input_is_mem;
end   

always_ff @(posedge clk) begin
    exec_mem_exception <= '0;

    if (opcode == decode_types::OP_MISC_MEM) begin
        exec_mem_result <= 'x; // NOTE: We're single-core in-order, FENCE is a no-op
    end else begin
        exec_mem_exception <= '1;
        exec_mem_result <= 'x;
    end
end

endmodule