`include "../params.svh"

package trap_causes;
typedef enum bit [3:0] {
    INT_S_SOFTWARE =    0,
    INT_M_SOFTWARE =    3,
    INT_S_TIMER =       5,
    INT_M_TIMER =       7,
    INT_S_EXTERNAL =    9,
    INT_M_EXTERNAL =    11
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

    input exec_trap_valid,
    input [3:0] exec_trap_cause,

    input [`XLEN-1:0] mtvec,

    output logic [`ALEN-1:0] exec_trap_target
);

wire [`XLEN-1:0] mtvec_addr = {mtvec[`XLEN-1:2], 2'b00};
wire mtvec_vectored_mode = mtvec[0]; // TODO: When we have interrupts, implement vectored mode
always_comb begin
    exec_trap_target = mtvec_addr;
end

endmodule