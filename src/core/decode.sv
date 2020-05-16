`include "params.svh"

// Wrapper around decode_impl that adds a stall point w/ a skid buffer.
module decode(
    input clk, rst,
    input flush,
    input ifetch_exception,
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
    output logic decode_is_compressed_instr,
    output logic decode_is_jump,
    output logic decode_is_reg_write,
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

wire [$bits(ifetch_exception)-1:0] sb_ifetch_exception_out;
skid_buf_data #(.WIDTH($bits(ifetch_exception))) sb_ifetch_exception(
    .*,
    .in(ifetch_exception),
    .out(sb_ifetch_exception_out)
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

decode_impl decode_impl(
    .clk,
    .rst,
    .flush,
    .ifetch_exception(sb_ifetch_exception_out),
    .instruction(sb_instruction_out),
    .instruction_addr(sb_instruction_addr_out),
    .instruction_next_addr(sb_instruction_next_addr_out),
    .*
);
endmodule

package decode_types;
typedef enum bit [6:2] {
    OP_LOAD =       'b00_000,
    OP_MISC_MEM =   'b00_011,
    OP_OP_IMM =     'b00_100,
    OP_AUIPC =      'b00_101,
    OP_OP =         'b01_100,
    OP_LUI =        'b01_101,
    OP_STORE =      'b01_000,
    OP_BRANCH =     'b11_000,
    OP_JALR =       'b11_001,
    OP_JAL =        'b11_011,
    OP_SYSTEM =     'b11_100
} opcodes_type;
endpackage

// Pipeline oblivious, protected from stalls by the parent's skid buffer
module decode_impl(
    input clk,
    input rst,
    input flush,
    input ifetch_exception,
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
    output reg decode_is_compressed_instr,
    output reg decode_is_jump,
    output reg decode_is_reg_write,
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
    opcode <= instruction[6:2];
    rd <= rd_comb;
    funct3 <= instruction[14:12];
    rs1 <= rs1_comb;
    rs2 <= rs2_comb;
    funct7 <= instruction[31:25];
    
    i_imm <= instruction[31:20];
    u_imm <= instruction[31:12];
    j_imm <= {instruction[31], instruction[19:12], instruction[20], instruction[30:25], instruction[24:21]};
    
    decode_is_compressed_instr <= instruction[1:0] != 'b11;
    decode_is_jump <= instruction[6:5] == 'b11;
    decode_is_reg_write <= instruction[6:2] != decode_types::OP_STORE
                        && instruction[6:2] != decode_types::OP_SYSTEM
                        && instruction[6:2] != decode_types::OP_BRANCH;
    
    if (bypass_net_exec_reg == rs1_comb)
        decode_rs1_data <= bypass_net_exec_data;
    else if (bypass_net_writeback_reg == rs1_comb)
        decode_rs1_data <= bypass_net_writeback_data;
    else
        decode_rs1_data <= decode_reg_read1_data;
        
    if (bypass_net_exec_reg == rs2_comb)
        decode_rs2_data <= bypass_net_exec_data;
    else if (bypass_net_writeback_reg == rs2_comb)
        decode_rs2_data <= bypass_net_writeback_data;
    else
        decode_rs2_data <= decode_reg_read1_data;
end

always @(posedge clk) begin
    if (rst || flush) begin
        decode_exception <= 'x;
        decode_instruction_addr <= 'x;
        decode_instruction_next_addr <= 'x;
    end else begin
        decode_instruction_addr <= instruction_addr;
        decode_instruction_next_addr <= instruction_next_addr;
        
        if (ifetch_exception)
            decode_exception <= '1;
        else if (instruction[1:0] != 'b11) // TODO: Support for compressed instr decoding
            decode_exception <= '1;
        else
            decode_exception <= '0;
    end
end

endmodule
