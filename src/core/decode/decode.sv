`include "../params.svh"

package decode_types;
typedef enum bit [6:2] {
    OP_LOAD =       'b00_000,
    OP_MISC_MEM =   'b00_011,
    OP_OP_IMM =     'b00_100,
    OP_AUIPC =      'b00_101,
    OP_OP_IMM_32 =  'b00_110,
    OP_OP =         'b01_100,
    OP_LUI =        'b01_101,
    OP_OP_32 =      'b01_110,
    OP_STORE =      'b01_000,
    OP_BRANCH =     'b11_000,
    OP_JALR =       'b11_001,
    OP_JAL =        'b11_011,
    OP_SYSTEM =     'b11_100
} opcodes_type;
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
    output logic decode_is_compressed_instr,
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
    output logic [6:0] funct7,
    output logic [31:20] i_imm,
    output logic [11:0] s_imm,
    output logic [12:1] b_imm,
    output logic [31:12] u_imm,
    output logic [20:1] j_imm
);

assign stall_prev = decomp_stall_prev;
assign stall_next = explode_stall_next;

wire decomp_stall_prev;
wire decomp_stall_next;
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
    .next_stalled(explode_stall_prev),
    .stall_prev(decomp_stall_prev),
    .stall_next(decomp_stall_next),
    .*
);

wire explode_stall_prev;
wire explode_stall_next;
decode_explode explode(
    .clk,
    .rst,
    .flush,
    .prev_stalled(decomp_stall_next),
    .next_stalled(next_stalled),
    .stall_prev(explode_stall_prev),
    .stall_next(explode_stall_next),
    .prev_exception(decomp_exception),
    .prev_trap_cause(decomp_trap_cause),
    .original_instruction(decomp_original_instruction),
    .instruction(decomp_expanded_instruction),
    .instruction_addr(decomp_instruction_addr),
    .instruction_next_addr(decomp_instruction_next_addr),
    .*
);
endmodule
