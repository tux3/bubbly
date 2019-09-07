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

wire [`XLEN-1:0] pc;
wire pc_stall;
pc_control pc_control(
    .clk,
    .rst,
    .pc,
    .next_stalled(ifetch_stall_prev),
    .stall(pc_stall)
);

wire ifetch_stall_prev;
wire ifetch_stall_next;
wire [`ILEN-1:0] instruction;
wire ifetch_exception;
ifetch ifetch(
    .clk,
    .rst,
    .addr(pc),
    .instruction,
    .ifetch_exception,
    .prev_stalled(pc_stall),
    .stall_prev(ifetch_stall_prev),
    .stall_next(ifetch_stall_next),
    .sys_bus
);

// TODO:
// - Write an AXI4-Lite interconnect between the fetch and the flash device (an address decoder/demux)
// - Add a small offcore RAM block to the address decoder, as if we actually had DRAM onboard...

// NOTE: Decode does not stall up, so there's no next_stalled in ifecth (but everything can stall down ofc, since data flows forward)

endmodule