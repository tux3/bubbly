// To start a new read pulse start_read, !keep_reading, and addr, then hold keep_reading
// The read starts immediately and stays pending until data_ready.
// Any previously pending read is aborted (because keep_reading pulsed low).
// Unset keep_reading to abort all reads, so that data_ready never triggers.

// To schedule the next read set start_read while a read is pending (hold keep_reading)
// The read will go from scheduled to pending at data_ready. Hold addr until data_ready.
// (start_read doesn't need to be held until data_ready, a pulse is enough)
// Scheduling a read when no read is pending starts a new read immediately instead.

module flash_reader #(
    parameter USE_SB_IO = 0,
    parameter FLASH_SIZE_BITS = 24
) (
    // Logic iface
    input clk,
    input rst,
    input [FLASH_SIZE_BITS-1:0] addr,
    input start_read,
    input keep_reading,
    output data_ready,
    output [7:0] data,
    // Pins iface
    output cs,
    output sclk,
    input capture_clk,
    inout si,
    inout so,
    inout wp,
    inout hold
);

    localparam IDLE = 2'b00;
    localparam READING = 2'b01;
    localparam NEW_ADDR = 2'b10;

    logic [1:0] state;
    logic [FLASH_SIZE_BITS-1:0] active_addr;
    logic read_scheduled;

    wire setup_done;
    wire data_ready_raw;
    wire do_read = state == READING && setup_done;
    qspi_flash #(.USE_SB_IO(USE_SB_IO)) flash (
        .clk,
        .rst,
        .addr(active_addr),
        .setup_done,
        .do_read,
        .data_ready(data_ready_raw),
        .data,
        .cs,
        .sclk,
        .capture_clk,
        .si,
        .so,
        .wp,
        .hold
    );

    assign data_ready = data_ready_raw && keep_reading && state == READING;

    always_ff @(posedge clk) begin
        if (rst) begin
            state <= IDLE;
            read_scheduled <= 0;
            active_addr <= 'x;
        end else if (!keep_reading) begin
            read_scheduled <= 0;
            if (start_read) begin
                active_addr <= addr;
                if (do_read)
                    state <= NEW_ADDR;
                else
                    state <= READING;
            end else begin
                state <= IDLE;
                active_addr <= 'x;
            end
        end else begin
            unique case (state)
                IDLE: begin
                    if (start_read) begin
                        state <= READING;
                        active_addr <= addr;
                    end
                end
                READING: begin
                    if (data_ready) begin
                        if (start_read || read_scheduled) begin
                            read_scheduled <= 0;
                            active_addr <= addr;
                            state <= NEW_ADDR;
                        end else if (!start_read) begin
                            active_addr <= 'x;
                        end
                    end else if (start_read) begin
                        read_scheduled <= 1;
                    end
                end
                NEW_ADDR: begin
                    if (start_read)
                        read_scheduled <= 1;
                    state <= READING;
                end
            endcase
        end
    end

    `ifndef SYNTHESIS
    always @(posedge clk) begin
        assert property (@(posedge clk) start_read && keep_reading && !data_ready |=> state == READING);
        assert property (@(posedge clk) start_read && !keep_reading && !rst |=> state == READING || state == NEW_ADDR);
        assert property (@(posedge clk) read_scheduled |=> $stable(addr) || start_read);
        assert property (@(posedge clk) !keep_reading |=> (!do_read || $rose(do_read)) && !data_ready && !read_scheduled);

        assert property (@(posedge clk) !rst |-> !$isunknown(setup_done));
        assert property (@(posedge clk) read_scheduled |-> state == READING);
        assert property (@(posedge clk) data_ready |-> state == READING);
        assert property (@(posedge clk) data_ready |-> !$isunknown(data));
    end
    `endif
endmodule
