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
    .*,
    .in(ifetch_exception),
    .out(sb_ifetch_exception_out)
);
wire [$bits(ifetch_trap_cause)-1:0] sb_ifetch_trap_cause_out;
skid_buf_data #(.WIDTH($bits(ifetch_trap_cause)), .MAYBE_UNKNOWN(1)) sb_ifetch_trap_cause(
    .*,
    .in(ifetch_trap_cause),
    .out(sb_ifetch_trap_cause_out)
);
wire [$bits(instruction)-1:0] sb_instruction_out;
skid_buf_data #(.WIDTH($bits(instruction)), .MAYBE_UNKNOWN(1)) sb_instruction( // May be unknown on last 2 bytes of a cache line, upper two bytes will be 'x
    .*,
    .in(instruction),
    .out(sb_instruction_out)
);
wire [$bits(instruction_addr)-1:0] sb_instruction_addr_out;
skid_buf_data #(.WIDTH($bits(instruction_addr))) sb_instruction_addr(
    .*,
    .in(instruction_addr),
    .out(sb_instruction_addr_out)
);
wire [$bits(instruction_next_addr)-1:0] sb_instruction_next_addr_out;
skid_buf_data #(.WIDTH($bits(instruction_next_addr))) sb_instruction_next_addr(
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

typedef enum bit [4:0] {
    COP_ADDI4SPN =      5'b000_00,
    COP_FLD =           5'b001_00,
    COP_LW =            5'b010_00,
    COP_LD =            5'b011_00,
    COP_RESERVED =      5'b100_00,
    COP_FSD =           5'b101_00,
    COP_SW =            5'b110_00,
    COP_SD =            5'b111_00,
    COP_ADDI =          5'b000_01,
    COP_ADDIW =         5'b001_01, // NOTE: This replaces C.JAL, which is RV32 only
    COP_LI =            5'b010_01,
    COP_LUI_ADDI16SP =  5'b011_01,
    COP_MISC_ALU =      5'b100_01,
    COP_J =             5'b101_01,
    COP_BEQZ =          5'b110_01,
    COP_BNEZ =          5'b111_01,
    COP_SLLI =          5'b000_10,
    COP_FLDSP =         5'b001_10,
    COP_LWSP =          5'b010_10,
    COP_LDSP =          5'b011_10,
    COP_JALR_MV_ADD =   5'b100_10,
    COP_FSDSP =         5'b101_10,
    COP_SWSP =          5'b110_10,
    COP_SDSP =          5'b111_10
} comp_opcodes_type;

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
        COP_ADDI4SPN: expanded = {{2'b00, ciw_imm}, 5'b00010, 3'b000, rd_prime, decode_types::OP_OP_IMM, 2'b11};
        COP_LW: expanded = {{5'b00000, cls_woff}, rs1_prime, 3'b010, rd_prime, decode_types::OP_LOAD, 2'b11};
        COP_LD: expanded = {{4'b0000, cls_doff}, rs1_prime, 3'b011, rd_prime, decode_types::OP_LOAD, 2'b11};
        COP_SW: expanded = {{5'b00000, cls_woff[6:5]}, rs2_prime, rs1_prime, 3'b010, cls_woff[4:0], decode_types::OP_STORE, 2'b11};
        COP_SD: expanded = {{4'b0000, cls_doff[7:5]}, rs2_prime, rs1_prime, 3'b011, cls_doff[4:0], decode_types::OP_STORE, 2'b11};
        COP_ADDI: expanded = {{6{ci_imm[5]}}, ci_imm, rd_rs1, 3'b000, rd_rs1, decode_types::OP_OP_IMM, 2'b11};
        COP_ADDIW: expanded = {{6{ci_imm[5]}}, ci_imm, rd_rs1, 3'b000, rd_rs1, decode_types::OP_OP_IMM_32, 2'b11};
        COP_LI: expanded = {{6{ci_imm[5]}}, ci_imm, 5'b00000, 3'b000, rd_rs1, decode_types::OP_OP_IMM, 2'b11};
        COP_LUI_ADDI16SP: if (rd_rs1 != 2) begin
            expanded = {{14{ci_lui_imm[17]}}, ci_lui_imm, rd_rs1, decode_types::OP_LUI, 2'b11};
        end else begin
            expanded = {{2{ci_addi16sp_imm[9]}}, ci_addi16sp_imm, 5'b00010, 3'b000, 5'b00010, decode_types::OP_OP_IMM, 2'b11};
        end
        COP_MISC_ALU: begin
            unique case (c_instr[11:10])
                2'b00: expanded = {6'b000000, ci_imm, rd_rs1_prime, 3'b101, rd_rs1_prime, decode_types::OP_OP_IMM, 2'b11}; // SRLI
                2'b01: expanded = {6'b010000, ci_imm, rd_rs1_prime, 3'b101, rd_rs1_prime, decode_types::OP_OP_IMM, 2'b11}; // SRAI
                2'b10: expanded = {{6{ci_imm[5]}}, ci_imm, rd_rs1_prime, 3'b111, rd_rs1_prime, decode_types::OP_OP_IMM, 2'b11}; // ANDI
                2'b11: unique case ({c_instr[12], c_instr[6:5]})
                    3'b000: expanded = {7'b0100000, rs2_prime, rd_rs1_prime, 3'b000, rd_rs1_prime, decode_types::OP_OP, 2'b11}; // SUB
                    3'b001: expanded = {7'b0000000, rs2_prime, rd_rs1_prime, 3'b100, rd_rs1_prime, decode_types::OP_OP, 2'b11}; // XOR
                    3'b010: expanded = {7'b0000000, rs2_prime, rd_rs1_prime, 3'b110, rd_rs1_prime, decode_types::OP_OP, 2'b11}; // OR
                    3'b011: expanded = {7'b0000000, rs2_prime, rd_rs1_prime, 3'b111, rd_rs1_prime, decode_types::OP_OP, 2'b11}; // AND
                    3'b100: expanded = {7'b0100000, rs2_prime, rd_rs1_prime, 3'b000, rd_rs1_prime, decode_types::OP_OP_32, 2'b11}; // SUBW
                    3'b101: expanded = {7'b0000000, rs2_prime, rd_rs1_prime, 3'b000, rd_rs1_prime, decode_types::OP_OP_32, 2'b11}; // ADDW
                    3'b110: expanded = 'x; // Reserved
                    3'b111: expanded = 'x; // Reserved
                endcase
            endcase
        end
        COP_J: expanded = {cj_off[11], cj_off[10:1], cj_off[11], {8{cj_off[11]}}, 5'b00000, decode_types::OP_JAL, 2'b11};
        COP_BEQZ: expanded = {{3{cb_off[8]}}, cb_off[8:5], 5'b00000, rs1_prime, 3'b000, {cb_off[4:1], cb_off[8]} , decode_types::OP_BRANCH, 2'b11};
        COP_BNEZ: expanded = {{3{cb_off[8]}}, cb_off[8:5], 5'b00000, rs1_prime, 3'b001, {cb_off[4:1], cb_off[8]} , decode_types::OP_BRANCH, 2'b11};
        COP_SLLI: expanded = {6'b000000, ci_imm, rd_rs1, 3'b001, rd_rs1, decode_types::OP_OP_IMM, 2'b11};
        COP_LWSP: expanded = {{4'b0000, ci_woff}, 5'b00010, 3'b010, rd_rs1, decode_types::OP_LOAD, 2'b11};
        COP_LDSP: expanded = {{3'b000, ci_doff}, 5'b00010, 3'b011, rd_rs1, decode_types::OP_LOAD, 2'b11};
        COP_JALR_MV_ADD: begin
            if (c_instr[12] == 0 && rs2 == '0) begin // JR
                expanded = {12'b0000_0000_0000, rd_rs1, 3'b000, 5'b00000, decode_types::OP_JALR, 2'b11};
            end else if (c_instr[12] == 0 && rs2 != '0) begin // MV
                expanded = {7'b0000000, rs2, 5'b00000, 3'b000, rd_rs1, decode_types::OP_OP, 2'b11};
            end else if (c_instr[12] == 1 && rd_rs1 == '0 && rs2 == '0) begin // EBREAK
                expanded = {12'b0000_0000_0001, 5'b00000, 3'b000, 5'b00000, decode_types::OP_SYSTEM, 2'b11};
            end else if (c_instr[12] == 1 && rd_rs1 != '0 && rs2 == '0) begin // JALR
                expanded = {12'b0000_0000_0000, rd_rs1, 3'b000, 5'b00001, decode_types::OP_JALR, 2'b11};
            end else if (c_instr[12] == 1 && rd_rs1 != '0 && rs2 != '0) begin // ADD
                expanded = {7'b0000000, rs2, rd_rs1, 3'b000, rd_rs1, decode_types::OP_OP, 2'b11};
            end else begin
                expanded = 'x;
            end
        end
        COP_SWSP: expanded = {{4'b0000, css_woff[7:5]}, rs2, 5'b00010, 3'b010, css_woff[4:0], decode_types::OP_STORE, 2'b11};
        COP_SDSP: expanded = {{3'b000, css_doff[8:5]}, rs2, 5'b00010, 3'b011, css_doff[4:0], decode_types::OP_STORE, 2'b11};
        default: expanded = 'x;
    endcase

    if (c_op == COP_ADDI4SPN && ciw_imm == '0) // Includes the all-zero instruction
        is_c_reserved = 1;
    else if (c_op == COP_RESERVED)
        is_c_reserved = 1;
    else if (c_op == COP_ADDIW && rd_rs1 == '0)
        is_c_reserved = 1;
    else if (c_op == COP_LUI_ADDI16SP && rd_rs1 == 5'b00010 && ci_imm == '0)
        is_c_reserved = 1;
    else if (c_op == COP_LUI_ADDI16SP && rd_rs1 != 5'b00010 && ci_imm == '0)
        is_c_reserved = 1;
    else if (c_op == COP_MISC_ALU && c_instr[11:10] == 2'b11 && {c_instr[12], c_instr[6]} == 2'b11)
        is_c_reserved = 1;
    else if ((c_op == COP_LWSP || c_op == COP_LDSP) && rd_rs1 == '0)
        is_c_reserved = 1;
    else if (c_op == COP_JALR_MV_ADD && c_instr[12] == 0 && rs2 == '0 && rd_rs1 == '0)
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
        end else if (c_op == COP_FLD || c_op == COP_FSD || c_op == COP_FLDSP || c_op == COP_FSDSP) begin // Unsupported F/D instructions
            decomp_exception <= '1;
            decomp_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
        end else begin
            decomp_exception <= '0;
            decomp_trap_cause <= 'x;
        end
    end
end

endmodule
