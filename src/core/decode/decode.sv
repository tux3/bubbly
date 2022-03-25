`include "../params.svh"

package opcodes;
typedef enum bit [6:2] {
    LOAD =       5'b00_000,
    MISC_MEM =   5'b00_011,
    OP_IMM =     5'b00_100,
    AUIPC =      5'b00_101,
    OP_IMM_32 =  5'b00_110,
    STORE =      5'b01_000,
    AMO =        5'b01_011,
    OP =         5'b01_100,
    LUI =        5'b01_101,
    OP_32 =      5'b01_110,
    BRANCH =     5'b11_000,
    JALR =       5'b11_001,
    JAL =        5'b11_011,
    SYSTEM =     5'b11_100
} opcodes_type;

typedef enum bit [4:0] {
    C_ADDI4SPN =      5'b000_00,
    C_FLD =           5'b001_00,
    C_LW =            5'b010_00,
    C_LD =            5'b011_00,
    C_RESERVED =      5'b100_00,
    C_FSD =           5'b101_00,
    C_SW =            5'b110_00,
    C_SD =            5'b111_00,
    C_ADDI =          5'b000_01,
    C_ADDIW =         5'b001_01, // NOTE: This replaces C.JAL, which is RV32 only
    C_LI =            5'b010_01,
    C_LUI_ADDI16SP =  5'b011_01,
    C_MISC_ALU =      5'b100_01,
    C_J =             5'b101_01,
    C_BEQZ =          5'b110_01,
    C_BNEZ =          5'b111_01,
    C_SLLI =          5'b000_10,
    C_FLDSP =         5'b001_10,
    C_LWSP =          5'b010_10,
    C_LDSP =          5'b011_10,
    C_JALR_MV_ADD =   5'b100_10,
    C_FSDSP =         5'b101_10,
    C_SWSP =          5'b110_10,
    C_SDSP =          5'b111_10
} comp_opcodes_type;
endpackage

module decode(
    input clk, rst,
    input flush,
    input ifetch_exception,
    input [3:0] ifetch_trap_cause,
    input [`ILEN-1:0] instruction,
    input [`ALEN-1:0] instruction_addr,
    input [`ALEN-1:0] instruction_next_addr,
    input prev_stalled,
    input next_stalled,
    output logic stall_prev,
    output logic stall_next,

    input wire [4:0] bypass_net_exec_reg,
    input wire [`XLEN-1:0] bypass_net_exec_data,
    input wire [4:0] bypass_net_writeback_reg,
    input wire [`XLEN-1:0] bypass_net_writeback_data,

    output wire [4:0] decode_reg_read1_sel,
    input wire [`XLEN-1:0] decode_reg_read1_data,
    output wire [4:0] decode_reg_read2_sel,
    input wire [`XLEN-1:0] decode_reg_read2_data,

    output logic decode_exception,
    output logic [3:0] decode_trap_cause,
    output logic decode_is_jump,
    output logic decode_is_reg_write,
    output logic [`ILEN-1:0] decode_original_instruction,
    output logic [`ALEN-1:0] decode_instruction_addr,
    output logic [`ALEN-1:0] decode_instruction_next_addr,
    output logic [4:0] opcode,
    output logic [4:0] rd,
    output logic [2:0] funct3,
    output logic [4:0] rs1,
    output logic [4:0] rs2,
    // Note: decode_rsX_data don't check the exec comb bypass (they're 1 cycle late), and may be invalid as a result
    output logic [`XLEN-1:0] decode_rs1_data,
    output logic [`XLEN-1:0] decode_rs2_data,
    output logic rs1_mul_sign,
    output logic rs2_mul_sign,
    output logic [6:0] funct7,
    output logic [31:20] i_imm,
    output logic [11:0] s_imm,
    output logic [12:1] b_imm,
    output logic [31:12] u_imm,
    output logic [20:1] j_imm
);

wire decomp_stall_prev;
wire decomp_stall_next;
wire decomp_next_stalled;
wire decomp_exception;
wire [3:0] decomp_trap_cause;
wire [`ILEN-1:0] decomp_original_instruction;
wire [`ILEN-1:0] decomp_expanded_instruction;
wire [`ALEN-1:0] decomp_instruction_addr;
wire [`ALEN-1:0] decomp_instruction_next_addr;
decode_decompress decompress(
    .clk,
    .rst,
    .flush,
    .prev_stalled(prev_stalled),
    .next_stalled(decomp_next_stalled),
    .stall_prev(decomp_stall_prev),
    .stall_next(decomp_stall_next),
    .*
);

wire explode_stall_next;
decode_explode explode(
    .clk,
    .rst,
    .flush,
    .prev_stalled(decomp_stall_next),
    .next_stalled(next_stalled),
    .stall_prev(decomp_next_stalled),
    .stall_next(explode_stall_next),
    .prev_exception(decomp_exception),
    .prev_trap_cause(decomp_trap_cause),
    .original_instruction(decomp_original_instruction),
    .instruction(decomp_expanded_instruction),
    .instruction_addr(decomp_instruction_addr),
    .instruction_next_addr(decomp_instruction_next_addr),
    .*
);

assign stall_prev = decomp_stall_prev;
assign stall_next = explode_stall_next;

endmodule
