`include "../params.svh"

module decode_decompress(
    input clk,
    input rst,
    input flush,

    input prev_stalled,
    input next_stalled,
    output logic stall_prev,
    output logic stall_next,

    input ifetch_exception,
    input [3:0] ifetch_trap_cause,
    input [`ILEN-1:0] instruction,
    input [`ALEN-1:0] instruction_addr,
    input [`ALEN-1:0] instruction_next_addr,

    output logic decomp_exception,
    output logic [3:0] decomp_trap_cause,
    output logic [`ILEN-1:0] decomp_original_instruction,
    output logic [`ILEN-1:0] decomp_expanded_instruction,
    output logic [`ALEN-1:0] decomp_instruction_addr,
    output logic [`ALEN-1:0] decomp_instruction_next_addr
);

wire buf_full;
skid_buf_ctl sb_ctl(
    .clk,
    .rst(rst || flush),
    .prev_stalled,
    .next_stalled,
    .buf_full,
    .stall_prev,
    .stall_next
);

wire [$bits(ifetch_exception)-1:0] sb_ifetch_exception_out;
skid_buf_data #(.WIDTH($bits(ifetch_exception))) sb_ifetch_exception(
    .rst(rst || flush),
    .*,
    .in(ifetch_exception),
    .out(sb_ifetch_exception_out)
);
wire [$bits(ifetch_trap_cause)-1:0] sb_ifetch_trap_cause_out;
skid_buf_data #(.WIDTH($bits(ifetch_trap_cause)), .MAYBE_UNKNOWN(1)) sb_ifetch_trap_cause(
    .rst(rst || flush),
    .*,
    .in(ifetch_trap_cause),
    .out(sb_ifetch_trap_cause_out)
);
wire [$bits(instruction)-1:0] sb_instruction_out;
skid_buf_data #(.WIDTH($bits(instruction)), .MAYBE_UNKNOWN(1)) sb_instruction( // May be unknown on last 2 bytes of a cache line, upper two bytes will be 'x
    .rst(rst || flush),
    .*,
    .in(instruction),
    .out(sb_instruction_out)
);
wire [$bits(instruction_addr)-1:0] sb_instruction_addr_out;
skid_buf_data #(.WIDTH($bits(instruction_addr))) sb_instruction_addr(
    .rst(rst || flush),
    .*,
    .in(instruction_addr),
    .out(sb_instruction_addr_out)
);
wire [$bits(instruction_next_addr)-1:0] sb_instruction_next_addr_out;
skid_buf_data #(.WIDTH($bits(instruction_next_addr))) sb_instruction_next_addr(
    .rst(rst || flush),
    .*,
    .in(instruction_next_addr),
    .out(sb_instruction_next_addr_out)
);

decode_decompress_impl decode_decompress_impl(
    .clk,
    .rst,
    .flush,
    .ifetch_exception(sb_ifetch_exception_out),
    .ifetch_trap_cause(sb_ifetch_trap_cause_out),
    .instruction(sb_instruction_out),
    .instruction_addr(sb_instruction_addr_out),
    .instruction_next_addr(sb_instruction_next_addr_out),
    .*
);

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (!stall_next && !decomp_exception |-> !$isunknown(decomp_original_instruction[15:0]));
    assert property (!stall_next && !decomp_exception |-> !$isunknown(decomp_expanded_instruction));
end
`endif

endmodule

// Pipeline oblivious, protected from stalls by the parent's skid buffer
module decode_decompress_impl(
    input clk,
    input rst,
    input flush,
    input ifetch_exception,
    input [3:0] ifetch_trap_cause,
    input [`ILEN-1:0] instruction,
    input [`ALEN-1:0] instruction_addr,
    input [`ALEN-1:0] instruction_next_addr,

    output reg decomp_exception,
    output reg [3:0] decomp_trap_cause,
    output reg [`ILEN-1:0] decomp_original_instruction,
    output reg [`ILEN-1:0] decomp_expanded_instruction,
    output reg [`ALEN-1:0] decomp_instruction_addr,
    output reg [`ALEN-1:0] decomp_instruction_next_addr
);

wire is_compressed = instruction[1:0] != 2'b11;
wire [15:0] c_instr = instruction;
wire [2:0] funct3 = c_instr[15:13];
wire [4:0] c_op = {funct3, c_instr[1:0]};

wire [5:0] ci_imm = {c_instr[12], c_instr[6:2]};
wire [17:12] ci_lui_imm = {ci_imm[5], ci_imm[4:0]};
wire [9:0] ci_addi16sp_imm = {ci_imm[5], ci_imm[2:1], ci_imm[3], ci_imm[0], ci_imm[4], 4'b0000};
wire [7:0] ci_woff = {ci_imm[1:0], ci_imm[5], ci_imm[4:2], 2'b00};
wire [8:0] ci_doff = {ci_imm[2:0], ci_imm[5], ci_imm[4:3], 3'b000};
wire [5:0] css_imm = {c_instr[12:7]};
wire [7:0] css_woff = {css_imm[1:0], css_imm[5:2], 2'b00};
wire [8:0] css_doff = {css_imm[2:0], css_imm[5:3], 3'b000};
wire [9:0] ciw_imm = {c_instr[10:7], c_instr[12:11], c_instr[5], c_instr[6], 2'b00};
wire [4:0] cls_imm = {c_instr[12:10], c_instr[6:5]};
wire [6:0] cls_woff = {cls_imm[0], cls_imm[4:2], cls_imm[1], 2'b00};
wire [7:0] cls_doff = {cls_imm[1:0], cls_imm[4:2], 3'b000};
wire [11:0] cj_off = {c_instr[12], c_instr[8], c_instr[10:9], c_instr[6], c_instr[7], c_instr[2], c_instr[11], c_instr[5:3], 1'b0};
wire [7:0] cb_imm = {c_instr[12:10], c_instr[6:2]};
wire [8:0] cb_off = {cb_imm[7], cb_imm[4:3], cb_imm[0], cb_imm[6:5], cb_imm[2:1], 1'b0};

wire [4:0] rs2 = c_instr[6:2];
wire [4:0] rd_rs1 = c_instr[11:7];
wire [4:0] rd_rs1_prime = {2'b01, c_instr[9:7]};
wire [4:0] rd_prime = {2'b01, c_instr[4:2]};
wire [4:0] rs1_prime = {2'b01, c_instr[9:7]};
wire [4:0] rs2_prime = {2'b01, c_instr[4:2]};

logic [`ILEN-1:0] expanded;
logic is_c_reserved;

always_comb begin
    unique case (c_op)
        opcodes::C_ADDI4SPN: expanded = {{2'b00, ciw_imm}, 5'b00010, 3'b000, rd_prime, opcodes::OP_IMM, 2'b11};
        opcodes::C_LW: expanded = {{5'b00000, cls_woff}, rs1_prime, 3'b010, rd_prime, opcodes::LOAD, 2'b11};
        opcodes::C_LD: expanded = {{4'b0000, cls_doff}, rs1_prime, 3'b011, rd_prime, opcodes::LOAD, 2'b11};
        opcodes::C_SW: expanded = {{5'b00000, cls_woff[6:5]}, rs2_prime, rs1_prime, 3'b010, cls_woff[4:0], opcodes::STORE, 2'b11};
        opcodes::C_SD: expanded = {{4'b0000, cls_doff[7:5]}, rs2_prime, rs1_prime, 3'b011, cls_doff[4:0], opcodes::STORE, 2'b11};
        opcodes::C_ADDI: expanded = {{6{ci_imm[5]}}, ci_imm, rd_rs1, 3'b000, rd_rs1, opcodes::OP_IMM, 2'b11};
        opcodes::C_ADDIW: expanded = {{6{ci_imm[5]}}, ci_imm, rd_rs1, 3'b000, rd_rs1, opcodes::OP_IMM_32, 2'b11};
        opcodes::C_LI: expanded = {{6{ci_imm[5]}}, ci_imm, 5'b00000, 3'b000, rd_rs1, opcodes::OP_IMM, 2'b11};
        opcodes::C_LUI_ADDI16SP: if (rd_rs1 != 2) begin
            expanded = {{14{ci_lui_imm[17]}}, ci_lui_imm, rd_rs1, opcodes::LUI, 2'b11};
        end else begin
            expanded = {{2{ci_addi16sp_imm[9]}}, ci_addi16sp_imm, 5'b00010, 3'b000, 5'b00010, opcodes::OP_IMM, 2'b11};
        end
        opcodes::C_MISC_ALU: begin
            unique case (c_instr[11:10])
                2'b00: expanded = {6'b000000, ci_imm, rd_rs1_prime, 3'b101, rd_rs1_prime, opcodes::OP_IMM, 2'b11}; // SRLI
                2'b01: expanded = {6'b010000, ci_imm, rd_rs1_prime, 3'b101, rd_rs1_prime, opcodes::OP_IMM, 2'b11}; // SRAI
                2'b10: expanded = {{6{ci_imm[5]}}, ci_imm, rd_rs1_prime, 3'b111, rd_rs1_prime, opcodes::OP_IMM, 2'b11}; // ANDI
                2'b11: unique case ({c_instr[12], c_instr[6:5]})
                    3'b000: expanded = {7'b0100000, rs2_prime, rd_rs1_prime, 3'b000, rd_rs1_prime, opcodes::OP, 2'b11}; // SUB
                    3'b001: expanded = {7'b0000000, rs2_prime, rd_rs1_prime, 3'b100, rd_rs1_prime, opcodes::OP, 2'b11}; // XOR
                    3'b010: expanded = {7'b0000000, rs2_prime, rd_rs1_prime, 3'b110, rd_rs1_prime, opcodes::OP, 2'b11}; // OR
                    3'b011: expanded = {7'b0000000, rs2_prime, rd_rs1_prime, 3'b111, rd_rs1_prime, opcodes::OP, 2'b11}; // AND
                    3'b100: expanded = {7'b0100000, rs2_prime, rd_rs1_prime, 3'b000, rd_rs1_prime, opcodes::OP_32, 2'b11}; // SUBW
                    3'b101: expanded = {7'b0000000, rs2_prime, rd_rs1_prime, 3'b000, rd_rs1_prime, opcodes::OP_32, 2'b11}; // ADDW
                    3'b110: expanded = 'x; // Reserved
                    3'b111: expanded = 'x; // Reserved
                endcase
            endcase
        end
        opcodes::C_J: expanded = {cj_off[11], cj_off[10:1], cj_off[11], {8{cj_off[11]}}, 5'b00000, opcodes::JAL, 2'b11};
        opcodes::C_BEQZ: expanded = {{3{cb_off[8]}}, cb_off[8:5], 5'b00000, rs1_prime, 3'b000, {cb_off[4:1], cb_off[8]} , opcodes::BRANCH, 2'b11};
        opcodes::C_BNEZ: expanded = {{3{cb_off[8]}}, cb_off[8:5], 5'b00000, rs1_prime, 3'b001, {cb_off[4:1], cb_off[8]} , opcodes::BRANCH, 2'b11};
        opcodes::C_SLLI: expanded = {6'b000000, ci_imm, rd_rs1, 3'b001, rd_rs1, opcodes::OP_IMM, 2'b11};
        opcodes::C_LWSP: expanded = {{4'b0000, ci_woff}, 5'b00010, 3'b010, rd_rs1, opcodes::LOAD, 2'b11};
        opcodes::C_LDSP: expanded = {{3'b000, ci_doff}, 5'b00010, 3'b011, rd_rs1, opcodes::LOAD, 2'b11};
        opcodes::C_JALR_MV_ADD: begin
            if (c_instr[12] == 0 && rs2 == '0) begin // JR
                expanded = {12'b0000_0000_0000, rd_rs1, 3'b000, 5'b00000, opcodes::JALR, 2'b11};
            end else if (c_instr[12] == 0 && rs2 != '0) begin // MV
                expanded = {7'b0000000, rs2, 5'b00000, 3'b000, rd_rs1, opcodes::OP, 2'b11};
            end else if (c_instr[12] == 1 && rd_rs1 == '0 && rs2 == '0) begin // EBREAK
                expanded = {12'b0000_0000_0001, 5'b00000, 3'b000, 5'b00000, opcodes::SYSTEM, 2'b11};
            end else if (c_instr[12] == 1 && rd_rs1 != '0 && rs2 == '0) begin // JALR
                expanded = {12'b0000_0000_0000, rd_rs1, 3'b000, 5'b00001, opcodes::JALR, 2'b11};
            end else if (c_instr[12] == 1 && rs2 != '0) begin // ADD (HINT if rd_rs1 == 0)
                expanded = {7'b0000000, rs2, rd_rs1, 3'b000, rd_rs1, opcodes::OP, 2'b11};
            end else begin
                expanded = 'x;
            end
        end
        opcodes::C_SWSP: expanded = {{4'b0000, css_woff[7:5]}, rs2, 5'b00010, 3'b010, css_woff[4:0], opcodes::STORE, 2'b11};
        opcodes::C_SDSP: expanded = {{3'b000, css_doff[8:5]}, rs2, 5'b00010, 3'b011, css_doff[4:0], opcodes::STORE, 2'b11};
        default: expanded = 'x;
    endcase

    if (c_op == opcodes::C_ADDI4SPN && ciw_imm == '0) // Includes the all-zero instruction
        is_c_reserved = 1;
    else if (c_op == opcodes::C_RESERVED)
        is_c_reserved = 1;
    else if (c_op == opcodes::C_ADDIW && rd_rs1 == '0)
        is_c_reserved = 1;
    else if (c_op == opcodes::C_LUI_ADDI16SP && rd_rs1 == 5'b00010 && ci_imm == '0)
        is_c_reserved = 1;
    else if (c_op == opcodes::C_LUI_ADDI16SP && rd_rs1 != 5'b00010 && ci_imm == '0)
        is_c_reserved = 1;
    else if (c_op == opcodes::C_MISC_ALU && c_instr[11:10] == 2'b11 && {c_instr[12], c_instr[6]} == 2'b11)
        is_c_reserved = 1;
    else if ((c_op == opcodes::C_LWSP || c_op == opcodes::C_LDSP) && rd_rs1 == '0)
        is_c_reserved = 1;
    else if (c_op == opcodes::C_JALR_MV_ADD && c_instr[12] == 0 && rs2 == '0 && rd_rs1 == '0)
        is_c_reserved = 1;
    else
        is_c_reserved = 0;
end

always @(posedge clk) begin
    if (rst || flush) begin
        decomp_exception <= 'x;
        decomp_trap_cause <= 'x;
        decomp_instruction_addr <= 'x;
        decomp_instruction_next_addr <= 'x;
        decomp_original_instruction <= 'x;
        decomp_expanded_instruction <= 'x;
    end else begin
        decomp_instruction_addr <= instruction_addr;
        decomp_instruction_next_addr <= instruction_next_addr;

        decomp_original_instruction <= instruction;
        decomp_expanded_instruction <= is_compressed ? expanded : instruction;

        if (ifetch_exception) begin
            decomp_exception <= '1;
            decomp_trap_cause <= ifetch_trap_cause;
        end else if (is_compressed && is_c_reserved) begin
            decomp_exception <= '1;
            decomp_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        end else if (c_op == opcodes::C_FLD || c_op == opcodes::C_FSD
                    || c_op == opcodes::C_FLDSP || c_op == opcodes::C_FSDSP) begin // Unsupported F/D instructions
            decomp_exception <= '1;
            decomp_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        end else begin
            decomp_exception <= '0;
            decomp_trap_cause <= 'x;
        end
    end
end

endmodule
