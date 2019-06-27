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

    localparam SETUP = 2'b00;
    localparam IDLE = 2'b01;
    localparam READING = 2'b10;

    logic [1:0] state;

    // TODO: Do we really want the interface to be "either keep reading or give a new address"? We could also take just an address and as long as it increments as we read we don't need to reset!
    // > Well we have the info before we increment PC, we know if we want to increment it or jump, so this interface is efficient, we avoid counters and comparators inside.

    always_ff @(posedge clk, negedge rst) begin
        if (!rst) begin
            state <= SETUP;
        end else
            unique case (state)
                SETUP: begin
                    if (setup_done)
                        state <= IDLE;
                end
                IDLE: begin

                end
            endcase
    end
endmodule