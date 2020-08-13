`include "params.svh"

module writeback(
    input clk,
    input rst,
    input prev_stalled,

    input exec_exception,
    input exec_is_taken_branch,
    input exec_is_reg_write,
    input [4:0] exec_reg_write_sel,
    input [`XLEN-1:0] exec_result,
    input [`ALEN-1:0] exec_branch_target,
    input [`ALEN-1:0] exec_instruction_next_addr,

    output logic writeback_reg_write_enable,
    output logic [4:0] writeback_reg_write_sel,
    output logic [`XLEN-1:0] writeback_reg_write_data,

    output logic writeback_instr_retired,
    output logic [`ALEN-1:0] writeback_next_pc
);

always_comb begin
    writeback_instr_retired = !prev_stalled && !exec_exception;
    writeback_next_pc = exec_is_taken_branch ? exec_branch_target : exec_instruction_next_addr;

    writeback_reg_write_enable = exec_is_reg_write && !prev_stalled && exec_reg_write_sel != '0;
    writeback_reg_write_sel = exec_reg_write_sel;
    writeback_reg_write_data = exec_result;
end

endmodule
