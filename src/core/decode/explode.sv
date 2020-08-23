`include "../params.svh"

module decode_explode(
    input clk, rst,
    input flush,
    input prev_exception,
    input [3:0] prev_trap_cause,
    input [`ILEN-1:0] original_instruction,
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

wire [$bits(prev_exception)-1:0] sb_prev_exception_out;
skid_buf_data #(.WIDTH($bits(prev_exception))) sb_prev_exception(
    .*,
    .in(prev_exception),
    .out(sb_prev_exception_out)
);
wire [$bits(prev_trap_cause)-1:0] sb_prev_trap_cause_out;
skid_buf_data #(.WIDTH($bits(prev_trap_cause)), .MAYBE_UNKNOWN(1)) sb_prev_trap_cause(
    .*,
    .in(prev_trap_cause),
    .out(sb_prev_trap_cause_out)
);
wire [$bits(original_instruction)-1:0] sb_original_instruction_out;
skid_buf_data #(.WIDTH($bits(original_instruction)), .MAYBE_UNKNOWN(1)) sb_original_instruction(
    .*,
    .in(original_instruction),
    .out(sb_original_instruction_out)
);
wire [$bits(instruction)-1:0] sb_instruction_out;
skid_buf_data #(.WIDTH($bits(instruction))) sb_instruction(
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

decode_explode_impl decode_explode_impl(
    .clk,
    .rst,
    .flush,
    .prev_exception(sb_prev_exception_out),
    .prev_trap_cause(sb_prev_trap_cause_out),
    .original_instruction(sb_original_instruction_out),
    .instruction(sb_instruction_out),
    .instruction_addr(sb_instruction_addr_out),
    .instruction_next_addr(sb_instruction_next_addr_out),
    .*
);

endmodule

// Pipeline oblivious, protected from stalls by the parent's skid buffer
module decode_explode_impl(
    input clk,
    input rst,
    input flush,
    input prev_exception,
    input [3:0] prev_trap_cause,
    input [`ILEN-1:0] original_instruction,
    input [`ILEN-1:0] instruction,
    input [`ALEN-1:0] instruction_addr,
    input [`ALEN-1:0] instruction_next_addr,

    input wire [4:0] bypass_net_exec_reg,
    input wire [`XLEN-1:0] bypass_net_exec_data,
    input wire [4:0] bypass_net_writeback_reg,
    input wire [`XLEN-1:0] bypass_net_writeback_data,

    output logic [4:0] decode_reg_read1_sel,
    input wire [`XLEN-1:0] decode_reg_read1_data,
    output logic [4:0] decode_reg_read2_sel,
    input wire [`XLEN-1:0] decode_reg_read2_data,

    output reg decode_exception,
    output reg [3:0] decode_trap_cause,
    output reg decode_is_compressed_instr,
    output reg decode_is_jump,
    output reg decode_is_reg_write,
    output reg [`ILEN-1:0] decode_original_instruction,
    output reg [`ALEN-1:0] decode_instruction_addr,
    output reg [`ALEN-1:0] decode_instruction_next_addr,
    output reg [4:0] opcode,
    output reg [4:0] rd,
    output reg [2:0] funct3,
    output reg [4:0] rs1,
    output reg [4:0] rs2,
    output reg [`XLEN-1:0] decode_rs1_data,
    output reg [`XLEN-1:0] decode_rs2_data,
    output reg [6:0] funct7,
    output reg [31:20] i_imm,
    output reg [11:0] s_imm,
    output reg [12:1] b_imm,
    output reg [31:12] u_imm,
    output reg [20:1] j_imm
);

wire [4:0] rd_comb = instruction[11:7];
wire [4:0] rs1_comb = instruction[19:15];
wire [4:0] rs2_comb = instruction[24:20];

always_comb begin
    decode_reg_read1_sel = rs1_comb;
    decode_reg_read2_sel = rs2_comb;
end

always @(posedge clk) begin
    decode_original_instruction <= original_instruction;

    opcode <= instruction[6:2];
    rd <= rd_comb;
    funct3 <= instruction[14:12];
    rs1 <= rs1_comb;
    rs2 <= rs2_comb;
    funct7 <= instruction[31:25];

    i_imm <= instruction[31:20];
    s_imm <= {instruction[31:25], instruction[11:7]};
    b_imm <= {instruction[31], instruction[7], instruction[30:25], instruction[11:8]};
    u_imm <= instruction[31:12];
    j_imm <= {instruction[31], instruction[19:12], instruction[20], instruction[30:25], instruction[24:21]};

    decode_is_compressed_instr <= instruction[1:0] != 'b11;
    decode_is_jump <= instruction[6:4] == 'b110;
    decode_is_reg_write <= instruction[6:2] != decode_types::OP_STORE
                        && instruction[6:2] != decode_types::OP_BRANCH;

    if (rs1_comb == '0)
        decode_rs1_data <= '0;
    else if (bypass_net_exec_reg == rs1_comb)
        decode_rs1_data <= bypass_net_exec_data;
    else if (bypass_net_writeback_reg == rs1_comb)
        decode_rs1_data <= bypass_net_writeback_data;
    else
        decode_rs1_data <= decode_reg_read1_data;

    if (rs2_comb == '0)
        decode_rs2_data <= '0;
    else if (bypass_net_exec_reg == rs2_comb)
        decode_rs2_data <= bypass_net_exec_data;
    else if (bypass_net_writeback_reg == rs2_comb)
        decode_rs2_data <= bypass_net_writeback_data;
    else
        decode_rs2_data <= decode_reg_read2_data;
end

always @(posedge clk) begin
    if (rst || flush) begin
        decode_exception <= 'x;
        decode_trap_cause <= 'x;
        decode_instruction_addr <= 'x;
        decode_instruction_next_addr <= 'x;
    end else begin
        decode_instruction_addr <= instruction_addr;
        decode_instruction_next_addr <= instruction_next_addr;

        if (prev_exception) begin
            decode_exception <= '1;
            decode_trap_cause <= prev_trap_cause;
        end else begin
            decode_exception <= '0;
            decode_trap_cause <= 'x;
        end
    end
end

endmodule
