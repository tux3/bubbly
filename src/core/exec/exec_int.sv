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
    input rs1_mul_sign,
    input rs2_mul_sign,
    input [6:0] funct7,
    input [31:20] i_imm,
    input [31:12] u_imm,

    input input_valid,
    input input_is_int,

    output reg exec_int_output_valid,
    output reg exec_int_exception,
    output reg [3:0] exec_int_trap_cause,
    output reg [`XLEN-1:0] exec_int_result
);

logic muldiv_pending;
wire is_muldiv = (opcode == opcodes::OP || opcode == opcodes::OP_32) && funct7 == 'b0000001;

always_ff @(posedge clk) begin
    if (rst) begin
        muldiv_pending <= '0;
        exec_int_output_valid <= '0;
    end else begin
        if (input_valid && input_is_int) begin
            muldiv_pending <= is_muldiv;
            exec_int_output_valid <= !is_muldiv;
        end else begin
            muldiv_pending <= '0;
            exec_int_output_valid <= muldiv_pending;
        end
    end
end

logic [4:0] opcode_buf;
logic [2:0] funct3_buf;
always_ff @(posedge clk) begin
    if (rst) begin
        opcode_buf <= 'x;
        funct3_buf <= 'x;
    end else begin
        opcode_buf <= opcode;
        funct3_buf <= funct3;
    end
end

logic [`XLEN*2-1:0] mul_result;
always_ff @(posedge clk) begin
    if (rst) begin
        mul_result <= 'x;
    end else if (input_valid && input_is_int && is_muldiv) begin
        mul_result <= { {`XLEN{rs1_mul_sign}}, rs1_data }
                    * { {`XLEN{rs2_mul_sign}}, rs2_data };
    end
end

always_ff @(posedge clk) begin
    exec_int_exception <= '0;
    exec_int_trap_cause <= 'x;

    if (input_valid && input_is_int) begin
        if (opcode == opcodes::LUI) begin
            exec_int_result <= {{`XLEN-31{u_imm[31]}}, u_imm[30:12], 12'b0};
        end else if (opcode == opcodes::AUIPC) begin
            exec_int_result <= decode_instruction_addr + {{`XLEN-31{u_imm[31]}}, u_imm[30:12], 12'b0};
        end else if (opcode == opcodes::OP_IMM) begin
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
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
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
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= {{`XLEN{ i_imm[30] & rs1_data[`XLEN-1] }}, rs1_data} >> i_imm[25:20];
                end
                3'b110: begin // ORI
                    exec_int_result <= $signed(rs1_data) | $signed(i_imm);
                end
                3'b111: begin // ANDI
                    exec_int_result <= $signed(rs1_data) & $signed(i_imm);
                end
            endcase
        end else if (opcode == opcodes::OP_IMM_32) begin
            // NOTE: $signed() is okay because:
            //  - while the result is wider, we make the operation self-determined using unary concatenation
            //  - both operands are signed, and we want to sign-extend the smallest to the size of the (self-determined) operation
            unique case (funct3)
                3'b000: begin // ADDIW
                    exec_int_result <= $signed({ $signed(rs1_data[31:0]) + $signed(i_imm) });
                end
                3'b001: begin // SLLIW
                    exec_int_exception <= i_imm[31:25] != '0;
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= $signed({ rs1_data[31:0] << i_imm[24:20] });
                end
                3'b101: begin // SRLIW/SRAIW
                    exec_int_exception <= i_imm[31] != 1'b0 || i_imm[29:25] != 5'b00000;
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= {{`XLEN{ i_imm[30] & rs1_data[31] }}, rs1_data[31:0]} >> i_imm[24:20];
                end
                default: begin
                    exec_int_exception <= '1;
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= 'x;
                end
            endcase
        end else if (opcode == opcodes::OP) begin
            // NOTE: $signed() is okay because:
            //  - the result (unsigned), rs1 and rs2 are all the same size, so we don't require any implicit sign-extension
            unique case (funct3)
                3'b000: begin // ADD/SUB
                    exec_int_result <= $signed(rs1_data) + (i_imm[30] ? -$signed(rs2_data) : $signed(rs2_data));
                end
                3'b001: begin // SLL
                    exec_int_result <= rs1_data << rs2_data[$clog2(`XLEN)-1:0];
                end
                3'b010: begin // SLT
                    exec_int_result <= $signed(rs1_data) < $signed(rs2_data);
                end
                3'b011: begin // SLTU
                    exec_int_result <= rs1_data < rs2_data;
                end
                3'b100: begin // XOR
                    exec_int_result <= $signed(rs1_data) ^ $signed(rs2_data);
                end
                3'b101: begin // SRL/SRA
                    exec_int_result <= {{`XLEN{ i_imm[30] & rs1_data[`XLEN-1] }}, rs1_data} >> rs2_data[$clog2(`XLEN)-1:0];
                end
                3'b110: begin // OR
                    exec_int_result <= $signed(rs1_data) | $signed(rs2_data);
                end
                3'b111: begin // AND
                    exec_int_result <= $signed(rs1_data) & $signed(rs2_data);
                end
            endcase
        end else if (opcode == opcodes::OP_32) begin
            // NOTE: $signed() is okay because:
            //  - while the result is wider, we make the operation self-determined using unary concatenation
            //  - both operands are signed and the same size
            unique case (funct3)
                3'b000: begin // ADDW/SUBW
                    exec_int_result <= $signed({ $signed(rs1_data[31:0]) + (i_imm[30] ? -$signed(rs2_data[31:0]) : $signed(rs2_data[31:0])) });
                end
                3'b001: begin // SLLW
                    exec_int_result <= $signed({ rs1_data[31:0] << rs2_data[4:0] });
                end
                3'b101: begin // SRLW/SRAW
                    exec_int_result <= {{`XLEN{ i_imm[30] & rs1_data[31] }}, rs1_data[31:0]} >> rs2_data[4:0];
                end
                default: begin
                    exec_int_exception <= '1;
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= 'x;
                end
            endcase
        end else begin
            exec_int_exception <= '1;
            exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
            exec_int_result <= 'x;
        end
    end else if (muldiv_pending) begin
        if (opcode_buf == opcodes::OP_32) begin
            unique case (funct3_buf)
                3'b000: begin // MULW
                    exec_int_result <= $signed({ mul_result[31:0] });
                end
                default: begin
                    exec_int_exception <= '1;
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= 'x;
                end
            endcase
        end else if (opcode_buf == opcodes::OP) begin
            unique case (funct3_buf)
                3'b000: begin // MUL
                    exec_int_result <= mul_result[`XLEN-1:0];
                end
                3'b001: begin // MULH
                    exec_int_result <= mul_result[`XLEN*2-1:`XLEN];
                end
                3'b010: begin // MULHSU
                    exec_int_result <= mul_result[`XLEN*2-1:`XLEN];
                end
                3'b011: begin // MULHU
                    exec_int_result <= mul_result[`XLEN*2-1:`XLEN];
                end
                default: begin
                    exec_int_exception <= '1;
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= 'x;
                end
            endcase
        end
    end
end

endmodule