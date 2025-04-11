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

generate if ((`WITH_BITMANIP_ZBS || `WITH_BITMANIP_ZBB) && `XLEN != 64)
    $error("Bitmanip is only implemented for RV64");
endgenerate

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
                3'b001: begin
                    if (`WITH_BITMANIP_ZBS && funct7[6:1] == 'b001010) begin // BSETI
                        exec_int_result <= rs1_data | (64'b1 << i_imm[25:20]);
                    end else if (`WITH_BITMANIP_ZBS && funct7[6:1] == 'b010010) begin // BCLRI
                        exec_int_result <= rs1_data & ~(64'b1 << i_imm[25:20]);
                    end else if (`WITH_BITMANIP_ZBS && funct7[6:1] == 'b011010) begin // BINVI
                        exec_int_result <= rs1_data ^ (64'b1 << i_imm[25:20]);
                    end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && rs2 == '0) begin // CLZ
                        unique if (rs1_data == '0)
                            exec_int_result <= `XLEN;
                        `define X(N) else if (rs1_data[`XLEN-1 -: N] == 1) exec_int_result <= N-1;
                        `X( 1) `X( 2) `X( 3) `X( 4) `X( 5) `X( 6) `X( 7) `X( 8) `X( 9) `X(10) `X(11) `X(12) `X(13) `X(14) `X(15) `X(16)
                        `X(17) `X(18) `X(19) `X(20) `X(21) `X(22) `X(23) `X(24) `X(25) `X(26) `X(27) `X(28) `X(29) `X(30) `X(31) `X(32)
                        `X(33) `X(34) `X(35) `X(36) `X(37) `X(38) `X(39) `X(40) `X(41) `X(42) `X(43) `X(44) `X(45) `X(46) `X(47) `X(48)
                        `X(49) `X(50) `X(51) `X(52) `X(53) `X(54) `X(55) `X(56) `X(57) `X(58) `X(59) `X(60) `X(61) `X(62) `X(63) `X(64)
                        `undef X
                    end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && rs2 == 'b1) begin // CTZ
                        unique if (rs1_data == '0)
                            exec_int_result <= `XLEN;
                        `define X(N) else if (rs1_data[0 +: N] == (64'b1 << (N-1))) exec_int_result <= N-1;
                        `X( 1) `X( 2) `X( 3) `X( 4) `X( 5) `X( 6) `X( 7) `X( 8) `X( 9) `X(10) `X(11) `X(12) `X(13) `X(14) `X(15) `X(16)
                        `X(17) `X(18) `X(19) `X(20) `X(21) `X(22) `X(23) `X(24) `X(25) `X(26) `X(27) `X(28) `X(29) `X(30) `X(31) `X(32)
                        `X(33) `X(34) `X(35) `X(36) `X(37) `X(38) `X(39) `X(40) `X(41) `X(42) `X(43) `X(44) `X(45) `X(46) `X(47) `X(48)
                        `X(49) `X(50) `X(51) `X(52) `X(53) `X(54) `X(55) `X(56) `X(57) `X(58) `X(59) `X(60) `X(61) `X(62) `X(63) `X(64)
                        `undef X
                    end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && rs2 == 'b10) begin: cpop // CPOP
                        automatic logic [$clog2(`XLEN):0] cpop_acc = 0;
                        foreach(rs1_data[i])
                            cpop_acc += rs1_data[i];
                        exec_int_result <= cpop_acc;
                    end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && rs2 == 'b100) begin // SEXT.B
                        exec_int_result <= {{`XLEN-8{rs1_data[7]}}, rs1_data[7:0]};
                    end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && rs2 == 'b101) begin // SEXT.H
                        exec_int_result <= {{`XLEN-16{rs1_data[15]}}, rs1_data[15:0]};
                    end else begin // SLLI
                        exec_int_exception <= i_imm[31:26] != '0;
                        exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        exec_int_result <= rs1_data << i_imm[25:20];
                    end
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
                    if (`WITH_BITMANIP_ZBS && funct7[6:1] == 'b010010) begin // BEXTI
                        exec_int_result <= rs1_data[i_imm[25:20]];
                    end else if (`WITH_BITMANIP_ZBB && i_imm == 'b011010111000) begin // REV8
                        exec_int_result <= {
                            rs1_data[0  +: 8], rs1_data[8  +: 8],
                            rs1_data[16  +: 8], rs1_data[24  +: 8],
                            rs1_data[32  +: 8], rs1_data[40  +: 8],
                            rs1_data[48  +: 8], rs1_data[56  +: 8]
                        };
                    end else if (`WITH_BITMANIP_ZBB && funct7[6:1] == 'b011000) begin: rori // RORI
                        automatic logic [$clog2(`XLEN)-1:0] shamt = i_imm[25:20];
                        exec_int_result <= (rs1_data >> shamt) | (rs1_data << (`XLEN-shamt));
                    end else if (`WITH_BITMANIP_ZBB && i_imm == 'b0010_1000_0111) begin // ORC.B
                        for (integer i=0; i<8; i+=1)
                            exec_int_result[8*i +: 8] <= rs1_data[8*i +: 8] == '0 ? '0 : '1;
                    end else begin
                        exec_int_exception <= i_imm[31] != 1'b0 || i_imm[29:26] != 4'b0000;
                        exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        exec_int_result <= {{`XLEN{ i_imm[30] & rs1_data[`XLEN-1] }}, rs1_data} >> i_imm[25:20];
                    end
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
                3'b001: begin
                    if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && rs2 == '0) begin // CLZW
                        unique if (rs1_data[31:0] == '0)
                            exec_int_result <= 32;
                        `define X(N) else if (rs1_data[31 -: N] == 1) exec_int_result <= N-1;
                        `X( 1) `X( 2) `X( 3) `X( 4) `X( 5) `X( 6) `X( 7) `X( 8) `X( 9) `X(10) `X(11) `X(12) `X(13) `X(14) `X(15) `X(16)
                        `X(17) `X(18) `X(19) `X(20) `X(21) `X(22) `X(23) `X(24) `X(25) `X(26) `X(27) `X(28) `X(29) `X(30) `X(31) `X(32)
                        `undef X
                    end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && rs2 == 1) begin // CTZW
                        unique if (rs1_data[31:0] == '0)
                            exec_int_result <= 32;
                        `define X(N) else if (rs1_data[0 +: N] == (64'b1 << (N-1))) exec_int_result <= N-1;
                        `X( 1) `X( 2) `X( 3) `X( 4) `X( 5) `X( 6) `X( 7) `X( 8) `X( 9) `X(10) `X(11) `X(12) `X(13) `X(14) `X(15) `X(16)
                        `X(17) `X(18) `X(19) `X(20) `X(21) `X(22) `X(23) `X(24) `X(25) `X(26) `X(27) `X(28) `X(29) `X(30) `X(31) `X(32)
                        `undef X
                    end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && rs2 == 'b10) begin: cpopw // CPOPW
                        automatic logic [$clog2(32):0] cpopw_acc = 0;
                        for (integer i=0; i<32; i+=1)
                            cpopw_acc += rs1_data[i];
                        exec_int_result <= cpopw_acc;
                    end else begin // SLLIW
                        exec_int_exception <= i_imm[31:25] != '0;
                        exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        exec_int_result <= $signed({ rs1_data[31:0] << i_imm[24:20] });
                    end
                end
                3'b101: begin
                    if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000) begin: roriw // RORIW
                        exec_int_result <= $signed({ (rs1_data[31:0] >> rs2) | (rs1_data[31:0] << (32-rs2)) });
                    end else begin  // SRLIW/SRAIW
                        exec_int_exception <= i_imm[31] != 1'b0 || i_imm[29:25] != 5'b00000;
                        exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        // This is subtle: The W shifts are defined to always sign-extend the 32-bit result to 64-bit
                        // But SRLIW still doesn't propagate the sign bit when shifting right.
                        // So there is a special case _only_ when SRLIW shifting a signed value by zero.
                        exec_int_result <= signed'(32'( {{`XLEN{ i_imm[30] & rs1_data[31] }}, rs1_data[31:0]} >> i_imm[24:20] ));
                    end
                end
                default: begin
                    exec_int_exception <= '1;
                    exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                    exec_int_result <= 'x;
                end
            endcase
        end else if (opcode == opcodes::OP) begin
            if (`WITH_BITMANIP_ZBS && funct7 == 'b0010100 && funct3 == 'b001) begin // BSET
                exec_int_result <= rs1_data | (64'b1 << rs2_data[$clog2(`XLEN)-1:0]);
            end else if (`WITH_BITMANIP_ZBS && funct7 == 'b0100100 && funct3 == 'b001) begin // BCLR
                exec_int_result <= rs1_data & ~(64'b1 << rs2_data[$clog2(`XLEN)-1:0]);
            end else if (`WITH_BITMANIP_ZBS && funct7 == 'b0100100 && funct3 == 'b101) begin // BEXT
                exec_int_result <= rs1_data[rs2_data[$clog2(`XLEN)-1:0]];
            end else if (`WITH_BITMANIP_ZBS && funct7 == 'b0110100 && funct3 == 'b001) begin // BINV
                exec_int_result <= rs1_data ^ (64'b1 << rs2_data[$clog2(`XLEN)-1:0]);
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0000101 && funct3 == 'b100) begin // MIN
                exec_int_result <= $signed(rs1_data) < $signed(rs2_data) ? rs1_data : rs2_data;
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0000101 && funct3 == 'b101) begin // MINU
                exec_int_result <= rs1_data < rs2_data ? rs1_data : rs2_data;
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0000101 && funct3 == 'b110) begin // MAX
                exec_int_result <= $signed(rs1_data) < $signed(rs2_data) ? rs2_data : rs1_data;
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0000101 && funct3 == 'b111) begin // MAXU
                exec_int_result <= rs1_data < rs2_data ? rs2_data : rs1_data;
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && funct3 == 'b001) begin: rol // ROL
                automatic logic [$clog2(`XLEN)-1:0] shamt = rs2_data[$clog2(`XLEN)-1:0];
                exec_int_result <= (rs1_data << shamt) | (rs1_data >> (`XLEN-shamt));
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && funct3 == 'b101) begin: ror // ROR
                automatic logic [$clog2(`XLEN)-1:0] shamt = rs2_data[$clog2(`XLEN)-1:0];
                exec_int_result <= (rs1_data >> shamt) | (rs1_data << (`XLEN-shamt));
            end else if (funct7 == 1) begin
                exec_int_result <= 'x; // MULDIV result set later
            end else if (funct7[6] == 0 && funct7[4:0] == '0) begin
                // NOTE: $signed() is okay because:
                //  - the result (unsigned), rs1 and rs2 are all the same size, so we don't require any implicit sign-extension
                unique case (funct3)
                    3'b000: begin // ADD/SUB
                        exec_int_result <= $signed(rs1_data) + (i_imm[30] ? -$signed(rs2_data) : $signed(rs2_data));
                    end
                    3'b001: begin // SLL
                        exec_int_result <= rs1_data << rs2_data[$clog2(`XLEN)-1:0];
                        if (funct7[5]) begin
                            exec_int_exception <= '1;
                            exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        end
                    end
                    3'b010: begin // SLT
                        exec_int_result <= $signed(rs1_data) < $signed(rs2_data);
                        if (funct7[5]) begin
                            exec_int_exception <= '1;
                            exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        end
                    end
                    3'b011: begin // SLTU
                        exec_int_result <= rs1_data < rs2_data;
                        if (funct7[5]) begin
                            exec_int_exception <= '1;
                            exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        end
                    end
                    3'b100: begin // XOR/XNOR
                        if (`WITH_BITMANIP_ZBB) begin
                            exec_int_result <= rs1_data ^ (funct7[5] ? ~rs2_data : rs2_data);
                        end else if (funct7[5]) begin
                            exec_int_exception <= '1;
                            exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        end else begin
                            exec_int_result <= rs1_data ^ rs2_data;
                        end
                    end
                    3'b101: begin // SRL/SRA
                        exec_int_result <= {{`XLEN{ i_imm[30] & rs1_data[`XLEN-1] }}, rs1_data} >> rs2_data[$clog2(`XLEN)-1:0];
                    end
                    3'b110: begin // OR/ORN
                        if (`WITH_BITMANIP_ZBB) begin
                            exec_int_result <= rs1_data | (funct7[5] ? ~rs2_data : rs2_data);
                        end else if (funct7[5]) begin
                            exec_int_exception <= '1;
                            exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        end else begin
                            exec_int_result <= rs1_data | rs2_data;
                        end
                    end
                    3'b111: begin // AND/ANDN
                        if (`WITH_BITMANIP_ZBB) begin
                            exec_int_result <= rs1_data & (funct7[5] ? ~rs2_data : rs2_data);
                        end else if (funct7[5]) begin
                            exec_int_exception <= '1;
                            exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        end else begin
                            exec_int_result <= rs1_data & rs2_data;
                        end
                    end
                endcase
            end else begin
                exec_int_exception <= '1;
                exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                exec_int_result <= 'x;
            end
        end else if (opcode == opcodes::OP_32) begin
            if (funct7 == 1) begin
                exec_int_result <= 'x; // MULDIV result set later
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0000100 && rs2 == '0 && funct3 == 'b100) begin // ZEXT.H
                exec_int_result <= rs1_data[15:0];
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && funct3 == 'b001) begin: rolw // ROLW
                automatic logic [4:0] shamt = rs2_data[4:0];
                exec_int_result <= $signed({ (rs1_data[31:0] << shamt) | (rs1_data[31:0] >> (32-shamt)) });
            end else if (`WITH_BITMANIP_ZBB && funct7 == 'b0110000 && funct3 == 'b101) begin: rorw // RORW
                automatic logic [4:0] shamt = rs2_data[4:0];
                exec_int_result <= $signed({ (rs1_data[31:0] >> shamt) | (rs1_data[31:0] << (32-shamt)) });
            end else if (funct7[6] == 0 && funct7[4:0] == '0) begin
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
                        // This is subtle: The W shifts are defined to always sign-extend the 32-bit result to 64-bit
                        // But SRLW still doesn't propagate the sign bit when shifting right.
                        // So there is a special case _only_ when SRLW shifting a signed value by zero.
                        exec_int_result <= signed'(32'( {{`XLEN{ i_imm[30] & rs1_data[31] }}, rs1_data[31:0]} >> rs2_data[4:0] ));
                    end
                    default: begin
                        exec_int_exception <= '1;
                        exec_int_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
                        exec_int_result <= 'x;
                    end
                endcase
            end
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
