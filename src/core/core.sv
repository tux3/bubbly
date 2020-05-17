`include "params.svh"

module core(
    input clk, rst,

    axi4lite.master ifetch_port,
    axi4lite.master data_port,

    // State outputs
    output [`XLEN-1:0] reg_pc,
    
    input [4:0] reg_read_sel,
    output [`XLEN-1:0] reg_read_data
);

assign reg_pc = pc;

// Pipeline handshake
// - prev_stalled: Input data is NOT valid, can be asserted at any clock tick.
// - next_stalled: Next stage is NOT ready to accept output.
// - stall_prev: We are NOT ready to accept input data. When !stall_prev && !prev_stalled, we have a handshake and the input is accepted
// - stall_next: Output data is NOT valid. Must not depend on next_stalled (like AXI)

wire [`XLEN-1:0] pc;
pc_control pc_control(
    .clk,
    .rst,
	.instr_retired(writeback_instr_retired),
    .next_pc(writeback_next_pc),
    .pc
);

int_regfile regs(
    .clk,
    .rst,
    
    .write1_enable(writeback_reg_write_enable),
    .write1_sel(writeback_reg_write_sel),
    .write1_data(writeback_reg_write_data),
    .read1_sel(decode_reg_read1_sel),
    .read1_data(decode_reg_read1_data),
    .read2_sel(decode_reg_read2_sel),
    .read2_data(decode_reg_read2_data),
    .read3_sel(reg_read_sel),
    .read3_data(reg_read_data)
);

wire ifetch_stall_next;
wire [`ILEN-1:0] instruction;
wire [`ALEN-1:0] instruction_addr;
wire [`ALEN-1:0] instruction_next_addr;
wire ifetch_exception;
ifetch ifetch(
    .clk,
    .rst,
    .flush(exec_pipeline_flush),
    .pc(pc),
    .instruction,
    .instruction_addr,
    .instruction_next_addr,
    .ifetch_exception,
	.next_stalled(decode_stall_prev),
    .stall_next(ifetch_stall_next),
    .sys_bus(ifetch_port)
);

wire decode_stall_prev;
wire decode_stall_next;
wire [4:0] decode_reg_read1_sel;
wire [`XLEN-1:0] decode_reg_read1_data;
wire [4:0] decode_reg_read2_sel;
wire [`XLEN-1:0] decode_reg_read2_data;
wire decode_exception;
wire decode_is_compressed_instr;
wire decode_is_jump;
wire decode_is_reg_write;
wire [`ALEN-1:0] decode_instruction_addr;
wire [`ALEN-1:0] decode_instruction_next_addr;
wire [4:0] opcode;
wire [4:0] rd;
wire [2:0] funct3;
wire [4:0] rs1;
wire [4:0] rs2;
wire [`XLEN-1:0] decode_rs1_data;
wire [`XLEN-1:0] decode_rs2_data;
wire [6:0] funct7;
wire [31:20] i_imm;
wire [31:12] u_imm;
wire [20:1] j_imm;
decode decode(
    .clk,
    .rst,
    .flush(exec_pipeline_flush),
    .instruction,
    .instruction_addr,
    .instruction_next_addr,
    .ifetch_exception,
    .prev_stalled(ifetch_stall_next),
    .next_stalled(exec_stall_prev),
    .stall_prev(decode_stall_prev),
    .stall_next(decode_stall_next),
    .bypass_net_exec_reg(exec_reg_write_sel),
    .bypass_net_exec_data(exec_result),
    .bypass_net_writeback_reg(writeback_reg_write_sel),
    .bypass_net_writeback_data(writeback_reg_write_data),
    .*
);

wire exec_stall_prev;
wire exec_stall_next;
wire exec_exception;
wire exec_is_branch;
wire exec_is_reg_write;
wire [4:0] exec_reg_write_sel;
wire [`XLEN-1:0] exec_result;
wire [`ALEN-1:0] exec_branch_target;
wire [`ALEN-1:0] exec_instruction_next_addr;
wire exec_pipeline_flush;
exec exec(
    .clk,
    .rst,
    .prev_stalled(decode_stall_next),
    .stall_prev(exec_stall_prev),
    .stall_next(exec_stall_next),
    .data_bus(data_port),
    .*
);

wire writeback_reg_write_enable;
wire [4:0] writeback_reg_write_sel;
wire [`XLEN-1:0] writeback_reg_write_data;
wire writeback_instr_retired;
wire [`ALEN-1:0] writeback_next_pc;
writeback writeback(
    .clk,
    .rst,
    .prev_stalled(exec_stall_next),
    .*
);

endmodule