`include "params.svh"

module core#(
    parameter RESET_PC = `RESET_PC,
    parameter UNCACHEABLE_ADDR_MASK = '0 // If an addr AND-ed with this mask is non-zero, it's considered uncacheable
) (
    input clk, rst,

    axi4lite.master ifetch_port,
    axi4lite.master data_port,

    // Interrupt lines
    input mtime_int,
    input [3:0] platform_ints,

    // State outputs
    input [4:0] reg_read_sel,
    output [`XLEN-1:0] reg_read_data,
    output [`XLEN-1:0] reg_pc,
    output [`ALEN+`ILEN-1:0] fetch_instr
);

wire [`XLEN-1:0] pc;
assign reg_pc = pc;

// Pipeline handshake
// - prev_stalled: Input data is NOT valid, can be asserted at any clock tick.
// - next_stalled: Next stage is NOT ready to accept output.
// - stall_prev: We are NOT ready to accept input data. When !stall_prev && !prev_stalled, we have a handshake and the input is accepted
// - stall_next: Output data is NOT valid. Must not depend on next_stalled (like AXI)

logic [4:0] reg_to_clear;
logic do_clear_regs;
always @(posedge clk) begin
    if (rst) begin
        reg_to_clear <= 31;
        do_clear_regs <= 1;
    end else if (do_clear_regs) begin
        reg_to_clear <= reg_to_clear - 1;
        if (reg_to_clear == 1)
            do_clear_regs <= 0;
    end
end

wire [4:0] exec_reg_write_sel;
wire [`XLEN-1:0] exec_result;
wire exec_pipeline_flush;
wire exec_mispredict_detected;
wire [`ALEN-1:0] exec_mispredict_next_pc;
wire exec_interrupt;
wire [`ALEN-1:0] exec_mepc_approximate;

wire [4:0] writeback_reg_write_sel;
wire [`XLEN-1:0] writeback_reg_write_data;

wire ifetch_stall_next;
wire ifetch_next_stalled;
wire [`ILEN-1:0] instruction;
wire [`ALEN-1:0] instruction_addr;
wire [`ALEN-1:0] instruction_next_addr;
wire ifetch_exception;
wire [3:0] ifetch_trap_cause;
ifetch ifetch(
    .clk,
    .rst,
    .flush(exec_pipeline_flush || do_clear_regs),
    // Mispredict cannot be detected at the same time as a flush from an exception,
    // but we can raise an interrupt at the same time that a branch completes and detects mispredict
    // In that case, we should follow the interrupt, not go to the branch target.
    .flush_is_mispredict(exec_mispredict_detected && !exec_interrupt),
    .flush_next_pc(exec_mispredict_next_pc),
    .pc(pc),
    .mepc(exec_mepc_approximate),
    .instruction,
    .instruction_addr,
    .instruction_next_addr,
    .ifetch_exception,
    .ifetch_trap_cause,
    .next_stalled(ifetch_next_stalled),
    .stall_next(ifetch_stall_next),
    .sys_bus(ifetch_port)
);

assign fetch_instr = {instruction_addr, instruction};

wire decode_stall_next;
wire decode_next_stalled;
wire [4:0] decode_reg_read1_sel;
wire [`XLEN-1:0] decode_reg_read1_data;
wire [4:0] decode_reg_read2_sel;
wire [`XLEN-1:0] decode_reg_read2_data;
wire decode_exception;
wire [3:0] decode_trap_cause;
wire decode_is_jump;
wire decode_is_reg_write;
wire [`ILEN-1:0] decode_original_instruction;
wire [`ALEN-1:0] decode_instruction_addr;
wire [`ALEN-1:0] decode_instruction_next_addr;
wire [4:0] opcode;
wire [4:0] rd;
wire [2:0] funct3;
wire [4:0] rs1;
wire [4:0] rs2;
wire [`XLEN-1:0] decode_rs1_data;
wire [`XLEN-1:0] decode_rs2_data;
wire rs1_mul_sign;
wire rs2_mul_sign;
wire [6:0] funct7;
wire [31:20] i_imm;
wire [11:0] s_imm;
wire [12:1] b_imm;
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
    .ifetch_trap_cause,
    .prev_stalled(ifetch_stall_next),
    .next_stalled(decode_next_stalled),
    .stall_prev(ifetch_next_stalled),
    .stall_next(decode_stall_next),
    .bypass_net_exec_reg(exec_reg_write_sel),
    .bypass_net_exec_data(exec_result),
    .bypass_net_writeback_reg(writeback_reg_write_sel),
    .bypass_net_writeback_data(writeback_reg_write_data),
    .*
);

wire exec_stall_next;
wire exec_is_trap;
wire [`ALEN-1:0] exec_trap_target;
wire exec_exception;
wire exec_is_taken_branch;
wire exec_is_reg_write;
wire exec_is_xret;
wire [`ALEN-1:0] exec_branch_target;
wire [`ALEN-1:0] exec_instruction_next_addr;
exec #(
    .UNCACHEABLE_ADDR_MASK(UNCACHEABLE_ADDR_MASK)
) exec (
    .clk,
    .rst,
    .prev_stalled(decode_stall_next),
    .stall_prev(decode_next_stalled),
    .stall_next(exec_stall_next),
    .platform_ints(platform_ints),
    .data_bus(data_port),
    .*
);

wire writeback_reg_write_enable;
wire writeback_update_pc;
wire [`ALEN-1:0] writeback_next_pc;
writeback writeback(
    .clk,
    .rst,
    .prev_stalled(exec_stall_next),
    .*
);

pc #(.RESET_PC(RESET_PC)) pc_control(
    .clk,
    .rst,
    .update_pc(writeback_update_pc),
    .next_pc(writeback_next_pc),
    .pc
);

int_regfile regs(
    .clk,
    .rst,

    .write1_enable(do_clear_regs ? '1 : writeback_reg_write_enable),
    .write1_sel(do_clear_regs ? reg_to_clear : writeback_reg_write_sel),
    .write1_data(do_clear_regs ? '0 : writeback_reg_write_data),
    .read1_sel(decode_reg_read1_sel),
    .read1_data(decode_reg_read1_data),
    .read2_sel(decode_reg_read2_sel),
    .read2_data(decode_reg_read2_data),
    .read3_sel(reg_read_sel),
    .read3_data(reg_read_data)
);

endmodule