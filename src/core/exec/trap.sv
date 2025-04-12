`include "../params.svh"

package priv_levels;
typedef enum bit [1:0] {
    USER = 2'b00,
    RESERVED1 = 2'b01,
    SUPERVISOR = 2'b10,
    MACHINE = 2'b11
} priv_level_e;
endpackage

package trap_causes;
typedef enum bit [5:0] {
    INT_S_SOFTWARE =    0,
    INT_M_SOFTWARE =    3,
    INT_S_TIMER =       5,
    INT_M_TIMER =       7,
    INT_S_EXTERNAL =    9,
    INT_M_EXTERNAL =    11,
    INT_PLATFORM0 =     16
} interrupts;

typedef enum bit [3:0] {
    EXC_INSTR_ADDR_MISALIGNED = 0,
    EXC_INSTR_ACCESS_FAULT =    1,
    EXC_ILLEGAL_INSTR =         2,
    EXC_BREAKPOINT =            3,
    EXC_LOAD_ADDR_MISALIGNED =  4,
    EXC_LOAD_ACCESS_FAULT =     5,
    EXC_STORE_ADDR_MISALIGNED = 6,
    EXC_STORE_ACCESS_FAULT =    7,
    EXC_ENV_CALL_UMODE =        8,
    EXC_ENV_CALL_SMODE =        9,
    // Reserved
    EXC_ENV_CALL_MMODE =        11,
    EXC_INSTR_PAGE_FAULT =      12,
    EXC_LOAD_PAGE_FAULT =       13,
    // Reserved
    EXC_STORE_PAGE_FAULT =      15
} exceptions;
endpackage

// Note: This module is combinatorial and completes the exec module's outputs
//       So we're really running in & stealing time from the writeback stage!
module trap(
    input clk,
    input rst,

    input input_valid_unless_mispredict,
    input exec_mispredict_detected,
    input decode_exception,
    input exec_exception,

    input [`ALEN-1:0] decode_instruction_addr,
    input [`ALEN-1:0] decode_trap_mepc_buf,
    input exec_branch_output_valid,
    input [`ALEN-1:0] last_branch_target_or_next,
    input exec_is_xret,
    input exec_system_blocked_on_wfi,

    input [3:0] exec_trap_cause,
    input [`ALEN-1:0] exec_trap_instr_addr,
    input [`ALEN-1:0] exec_branch_target,
    input [`ALEN-1:0] exec_mem_fault_addr,
    input [`ILEN-1:0] exec_trap_instr,

    input [1:0] privilege_mode,
    input [`XLEN-1:0] mstatus,
    input [`INTR_LEN-1:0] mie,
    input [`INTR_LEN-1:0] mip,
    input [`XLEN-1:0] mtvec,

    output logic take_m_int,
    output logic [`INTR_LEN-1:0] int_cause, // NOTE: Does not contain the high interrupt bit of mcause
    output logic [`ALEN-1:0] exec_trap_target,
    output logic [`ALEN-1:0] trap_mepc,
    output logic [`XLEN-1:0] trap_mtval
);

wire st_mie = mstatus[3];
wire [`INTR_LEN-1:0] active_ints = mip & mie;
always_comb begin
    int_cause = 'x;
    // Standard M-mode interrupt priority (high to low): MEI, MSI, MTI, SEI, SSI, STI
    if (active_ints[trap_causes::INT_M_TIMER])
        int_cause = trap_causes::INT_M_TIMER;
    // Gives priority to highest platform-defined interrupt number
    for (integer i = 16; i < `INTR_LEN; i = i + 1) begin
        if (active_ints[i])
            int_cause = i;
    end
end

// Interrupts are raise at the same time that the last instruction completes,
// i.e. we must let the previous instruction finish retiring at the same time we trap
logic int_instr_addr_known;
always_comb begin
    if (exec_exception) begin
        trap_mepc = decode_trap_mepc_buf;
        int_instr_addr_known = 'x; // Won't have an interrupt if we have an exception
    end else if (exec_branch_output_valid) begin
        trap_mepc = last_branch_target_or_next;
        int_instr_addr_known = '1;
    end else if (exec_is_xret) begin
        // We're about to return to trap_mepc and immediately take an interrupt again
        // The csr module knows not to update mecp if we interrupt behind a completed xret
        trap_mepc = 'x;
        int_instr_addr_known = '1;
    end else if (exec_system_blocked_on_wfi) begin
        trap_mepc = decode_trap_mepc_buf; // Set to next addr past WFI, per spec
        int_instr_addr_known = '1;
    end else if (input_valid_unless_mispredict && !decode_exception) begin
        trap_mepc = decode_instruction_addr;
        int_instr_addr_known = '1;
    end else begin
        trap_mepc = 'x;
        int_instr_addr_known = '0;
    end
end

assign take_m_int = !exec_exception && int_instr_addr_known
                    && active_ints != '0 && ((privilege_mode == priv_levels::MACHINE && st_mie)
                                             || privilege_mode < priv_levels::MACHINE);

wire [`XLEN-1:0] mtvec_addr = {mtvec[`XLEN-1:2], 2'b00};
wire mtvec_vectored_mode = mtvec[0];
always_comb begin
    if (mtvec_vectored_mode && take_m_int)
        exec_trap_target = mtvec_addr + {int_cause, 2'b00};
     else
        exec_trap_target = mtvec_addr;

    if (take_m_int) begin
        trap_mtval = '0;
    end else if (exec_trap_cause == trap_causes::EXC_INSTR_ADDR_MISALIGNED) begin
        trap_mtval = exec_branch_target;
    end else if (exec_trap_cause == trap_causes::EXC_BREAKPOINT) begin
        trap_mtval = trap_mepc;
    end else if (exec_trap_cause == trap_causes::EXC_INSTR_ACCESS_FAULT
                || exec_trap_cause == trap_causes::EXC_INSTR_PAGE_FAULT) begin
        trap_mtval = exec_trap_instr_addr;
    end else if (exec_trap_cause == trap_causes::EXC_LOAD_ADDR_MISALIGNED
                || exec_trap_cause == trap_causes::EXC_LOAD_ACCESS_FAULT
                || exec_trap_cause == trap_causes::EXC_LOAD_PAGE_FAULT
                || exec_trap_cause == trap_causes::EXC_STORE_ADDR_MISALIGNED
                || exec_trap_cause == trap_causes::EXC_STORE_ACCESS_FAULT
                || exec_trap_cause == trap_causes::EXC_STORE_PAGE_FAULT) begin
        trap_mtval = exec_mem_fault_addr;
    end else if (exec_trap_cause == trap_causes::EXC_ILLEGAL_INSTR) begin
        trap_mtval = exec_trap_instr;
    end else begin
        trap_mtval = '0;
    end
end

endmodule
