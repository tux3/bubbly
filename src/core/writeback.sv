`include "params.svh"

module writeback(
    input clk,
    input rst,
    input prev_stalled,

    input exec_exception,
    input [`ALEN-1:0] exec_trap_target,
    input exec_is_taken_branch,
    input exec_is_reg_write,
    input exec_is_xret,
    input [4:0] exec_reg_write_sel,
    input [`XLEN-1:0] exec_result,
    input [`ALEN-1:0] exec_branch_target,
    input [`ALEN-1:0] exec_instruction_next_addr,

    output logic writeback_reg_write_enable,
    output logic [4:0] writeback_reg_write_sel,
    output logic [`XLEN-1:0] writeback_reg_write_data,

    output logic writeback_update_pc,
    output logic [`ALEN-1:0] writeback_next_pc
);

always_comb begin
    writeback_update_pc = !prev_stalled;

    writeback_reg_write_enable = exec_is_reg_write && !prev_stalled && !exec_exception && exec_reg_write_sel != '0;
    writeback_reg_write_sel = exec_reg_write_sel;
    writeback_reg_write_data = exec_result;

    if (exec_exception)
        writeback_next_pc = exec_trap_target;
    else if (exec_is_xret)
        writeback_next_pc = exec_result;
    else if (exec_is_taken_branch)
        writeback_next_pc = exec_branch_target;
    else
        writeback_next_pc = exec_instruction_next_addr;
end

endmodule
