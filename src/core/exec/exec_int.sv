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

logic [4:0] opcode_buf;
logic [2:0] funct3_buf;
wire div_was_rem = funct3_buf[1];
always_ff @(posedge clk) begin
    if (rst) begin
        opcode_buf <= 'x;
        funct3_buf <= 'x;
    end else if (input_valid && input_is_int) begin
        opcode_buf <= opcode;
        funct3_buf <= funct3;
    end
end

logic mul_pending;
wire is_muldiv = (opcode == opcodes::OP || opcode == opcodes::OP_32) && funct7 == 'b0000001;
wire is_muldiv_mul = !funct3[2];
wire is_muldiv_div = funct3[2];

logic [`XLEN-1:0] div_a;
logic [`XLEN-1:0] div_b;
logic [`XLEN-1:0] div_q;
wire div_input_valid = input_valid && input_is_int && is_muldiv && is_muldiv_div;
logic div_output_valid;
exec_div exec_div(
    .clk,
    .rst,
    .a_in(div_a),
    .b_in(div_b),
    .q_out(div_q),
    .do_rem(div_was_rem),
    .input_valid(div_input_valid),
    .output_valid(div_output_valid)
);

always_ff @(posedge clk) begin
    if (rst) begin
        mul_pending <= '0;
        exec_int_output_valid <= '0;
    end else begin
        if (input_valid && input_is_int) begin
            mul_pending <= is_muldiv && is_muldiv_mul;
            exec_int_output_valid <= !is_muldiv;
        end else begin
            mul_pending <= '0;
            exec_int_output_valid <= mul_pending || div_output_valid;
        end
    end
end

logic [`XLEN-1:0] dividend_buf;
logic [`XLEN-1:0] abs_dividend_buf;
logic div_was_by_zero;
logic div_was_signed_overflow;
logic div_had_sign_mismatch;
always_ff @(posedge clk) begin
    if (rst) begin
        dividend_buf <= 'x;
        div_was_by_zero <= 'x;
        div_was_signed_overflow <= 'x;
        div_had_sign_mismatch <= 'x;
    end else if (div_input_valid) begin
        dividend_buf <= rs1_data;
        abs_dividend_buf <= div_a;
        if (opcode == opcodes::OP_32) begin
            div_was_by_zero <= rs2_data[31:0] == '0;
            div_was_signed_overflow <= rs1_data[31:0] == 'h8000_0000 && rs2_data[31:0] == '1;
            div_had_sign_mismatch <= rs1_data[31] != rs2_data[31];
        end else begin
            div_was_by_zero <= rs2_data == '0;
            div_was_signed_overflow <= rs1_data == 'h8000_0000_0000_0000 && rs2_data == '1;
            div_had_sign_mismatch <= rs1_data[`XLEN-1] != rs2_data[`XLEN-1];
        end        
    end
end

wire muldiv_is_unsigned = funct3[0];
always_comb begin
    if (opcode == opcodes::OP_32) begin
        if (muldiv_is_unsigned) begin
            div_a = rs1_data[31:0];
            div_b = rs2_data[31:0];
        end else begin
            div_a = rs1_data[31] ? ({ -rs1_data[31:0] }) : rs1_data[31:0];
            div_b = rs2_data[31] ? ({ -rs2_data[31:0] }) : rs2_data[31:0];
        end
    end else begin
        if (muldiv_is_unsigned) begin
            div_a = rs1_data;
            div_b = rs2_data;
        end else begin
            div_a = rs1_data[`XLEN-1] ? -rs1_data : rs1_data;
            div_b = rs2_data[`XLEN-1] ? -rs2_data : rs2_data;
        end
    end
end

logic [`XLEN-1:0] mul_result_high;
logic [`XLEN-1:0] mul_result_ll;
logic [`XLEN-1:0] mul_result_lr;
logic [`XLEN-1:0] mul_result_rl;
logic [`XLEN-1:0] mul_result_rr;
wire [`XLEN*2-1:0] mul_result_low = mul_result_rr + {mul_result_lr, 32'b0} + {mul_result_rl, 32'b0} + {mul_result_ll, 64'b0};
wire [`XLEN*2-1:0] mul_result = {mul_result_high + mul_result_low[`XLEN +: `XLEN], mul_result_low[0 +: `XLEN]};
always_ff @(posedge clk) begin
    if (rst) begin
        mul_result_high <= 'x;
        mul_result_ll <= 'x;
        mul_result_lr <= 'x;
        mul_result_rl <= 'x;
        mul_result_rr <= 'x;
    end else if (input_valid && input_is_int) begin
        if (is_muldiv) begin
            mul_result_high <= (rs1_mul_sign ? ({ -rs2_data }) : '0)
                              + (rs2_mul_sign ? ({ -rs1_data }) : '0);
            mul_result_ll <= rs1_data[63:32] * rs2_data[63:32];
            mul_result_lr <= rs1_data[63:32] * rs2_data[31:0];
            mul_result_rl <= rs1_data[31:0] * rs2_data[63:32];
            mul_result_rr <= rs1_data[31:0] * rs2_data[31:0];
        end else begin
            mul_result_high <= 'x;
            mul_result_ll <= 'x;
            mul_result_lr <= 'x;
            mul_result_rl <= 'x;
            mul_result_rr <= 'x;
        end
    end
end

always_ff @(posedge clk) begin
    exec_int_exception <= '0;
    exec_int_trap_cause <= 'x;

    if (input_valid && input_is_int) begin
        unique if (opcode == opcodes::LUI) begin
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
        end else if (opcode == opcodes::OP && funct7 == 1) begin
            exec_int_result <= 'x; // MULDIV result set later
        end else if (opcode == opcodes::OP && funct7[4:0] == '0) begin
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
        end else if (opcode == opcodes::OP_32 && funct7 == 1) begin
            exec_int_result <= 'x; // MULDIV result set later
        end else if (opcode == opcodes::OP_32 && funct7[4:0] == '0) begin
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
    end else if (mul_pending) begin
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
    end else if (div_output_valid) begin
        if (opcode_buf == opcodes::OP_32) begin
            unique case (funct3_buf)
                3'b100: begin // DIVW
                    if (div_was_by_zero)
                        exec_int_result <= '1;
                    else if (div_was_signed_overflow)
                        exec_int_result <= $signed({ 32'h8000_0000 });
                    else
                        exec_int_result <= $signed({ div_had_sign_mismatch ? -div_q[31:0] : div_q[31:0] });
                end
                3'b101: begin // DIVUW
                    if (div_was_by_zero)
                        exec_int_result <= '1;
                    else
                        exec_int_result <= $signed({ div_q[31:0] });
                end
                3'b110: begin // REMW
                    if (div_was_by_zero)
                        exec_int_result <= $signed({ dividend_buf[31:0] });
                    else if (div_was_signed_overflow)
                        exec_int_result <= '0;
                    else if (dividend_buf[31]) // Rem is negative iff dividend was negative
                        exec_int_result <= $signed({ div_q[31:0] - abs_dividend_buf[31:0] });
                    else
                        exec_int_result <= $signed({ abs_dividend_buf[31:0] - div_q[31:0] });
                end
                3'b111: begin // REMUW
                    if (div_was_by_zero)
                        exec_int_result <= $signed({ dividend_buf[31:0] });
                    else
                        exec_int_result <= $signed({ abs_dividend_buf[31:0] - div_q[31:0] });
                end
                default: begin
                    exec_int_exception <= '1;
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= 'x;
                end
            endcase
        end else if (opcode_buf == opcodes::OP) begin
            unique case (funct3_buf)
                3'b100: begin // DIV
                    if (div_was_by_zero)
                        exec_int_result <= '1;
                    else if (div_was_signed_overflow)
                        exec_int_result <= 'h8000_0000_0000_0000;
                    else
                        exec_int_result <= div_had_sign_mismatch ? -div_q : div_q;
                end
                3'b101: begin // DIVU
                    if (div_was_by_zero)
                        exec_int_result <= '1;
                    else
                        exec_int_result <= div_q;
                end
                3'b110: begin // REM
                    if (div_was_by_zero)
                        exec_int_result <= dividend_buf;
                    else if (div_was_signed_overflow)
                        exec_int_result <= '0;
                    else if (dividend_buf[`XLEN-1]) // Rem is negative iff dividend was negative
                        exec_int_result <= div_q - abs_dividend_buf;
                    else
                        exec_int_result <= abs_dividend_buf - div_q;
                end
                3'b111: begin // REMU
                    if (div_was_by_zero)
                        exec_int_result <= dividend_buf;
                    else
                        exec_int_result <= abs_dividend_buf - div_q;
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