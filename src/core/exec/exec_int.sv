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
    input [`XLEN-1:0] rs1_data,
    input [`XLEN-1:0] rs2_data,
    input [6:0] funct7,
    input [31:20] i_imm,
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
    exec_int_exception <= '0;

    if (opcode == decode_types::OP_LUI) begin
        exec_int_result <= {{`XLEN-31{u_imm[31]}}, u_imm[30:12], 12'b0};
    end else if (opcode == decode_types::OP_AUIPC) begin
        exec_int_result <= decode_instruction_addr + {{`XLEN-31{u_imm[31]}}, u_imm[30:12], 12'b0};
    end else if (opcode == decode_types::OP_OP_IMM) begin
        // NOTE: $signed() is okay because:
        //  - the result (unsigned) is the same size as rs1
        //  - rs1 (unsigned) is always bigger than the immediate
        //  - the immediate is legitimately signed
        unique case (funct3)
            3'b000: begin // ADDI
                exec_int_result <= $signed(rs1_data) + $signed(i_imm);
            end
            3'b001: begin // SLLI
                exec_int_exception <= i_imm[31:26] != '0;
                exec_int_result <= rs1_data << i_imm[25:20];
            end
            3'b010: begin // SLTI
                exec_int_result <= $signed(rs1_data) < $signed(i_imm);
            end
            3'b011: begin // SLTIU
                exec_int_result <= rs1_data < {{`XLEN-11{i_imm[31]}}, i_imm[30:20]};
            end
            3'b100: begin // XORI
                exec_int_result <= $signed(rs1_data) ^ $signed(i_imm);
            end
            3'b101: begin // SRLI/SRAI
                exec_int_exception <= i_imm[31] != 1'b0 || i_imm[29:26] != 4'b0000;
                exec_int_result <= {{`XLEN{ i_imm[30] & rs1_data[`XLEN-1] }}, rs1_data} >> i_imm[25:20];
            end
            3'b110: begin // ORI
                exec_int_result <= $signed(rs1_data) | $signed(i_imm);
            end
            3'b111: begin // ANDI
                exec_int_result <= $signed(rs1_data) & $signed(i_imm);
            end
        endcase
    end else begin
        exec_int_exception <= '1;
        exec_int_result <= 'x;
    end
end

endmodule