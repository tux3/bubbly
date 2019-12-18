`include "params.svh"

module core(
    input clk, rst,

    axi4lite.master sys_bus,

    // State outputs
    output [`XLEN-1:0] reg_pc,
    output [`ILEN-1:0] fetched_instruction
);

assign reg_pc = pc;
assign fetched_instruction = instruction;

// Pipeline handshake
//  - prev_stalled: Input data is NOT valid, can be asserted at any clock tick. Must not depend on stall_prev (like AXI)
//  - stall_prev: We are NOT ready to accept input data. Note that this is a wire output! When !stall_prev && !prev_stalled, we have a handshake and the input is accepted
//  - stall_next: Output data is NOT valid

wire [`XLEN-1:0] pc;
wire pc_stall;
pc_control pc_control(
    .clk,
    .rst,
	.instr_retired(0),
    .pc
);

wire ifetch_stall_prev;
wire ifetch_stall_next;
wire [`ILEN-1:0] instruction;
wire ifetch_exception;
ifetch ifetch(
    .clk,
    .rst,
    .pc(pc),
    .instruction,
    .ifetch_exception,
    .stall_next(ifetch_stall_next),
    .sys_bus
);

endmodule