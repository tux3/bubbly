// Set addr and pulse read_from_addr to start a read at a new address
// Read the result from data on the rising edge of data_ready
// Assert read_next after a rising edge of data_ready to start a read at the next address.
// If read_from_addr and read_next are both asserted, read_from_addr takes precedence

// TODO:
// - Treat read_from_add as essentially a reset. We pull cs high and reset our state machine, when it goes low
// - After a read keep the spi module clock-gated, set our state to idle, and if we get read_next at any time while idle we un-clock-gate it
// - Make sure

module flash_reader (
    // Logic iface
    input clk,
    input rst,
    input [23:0] addr,
    input read_from_addr,
    input read_next,
    output reg data_ready,
    output reg [7:0] data,
    // Pins iface
    output reg cs,
    output sclk,
    inout si,
    inout so,
    inout wp,
    inout hold
);

wire setup_done;
wire do_read = 0;

qspi_flash flash(
    .clk,
    .rst,
    .addr,
    .setup_done,
    .do_read,
    .data_ready,
    .data,
    .cs,
    .sclk,
    .si,
    .so,
    .wp,
    .hold
);

endmodule