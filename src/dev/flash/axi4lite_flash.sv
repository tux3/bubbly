`include "../../axi/axi4lite.svh"

module axi4lite_flash #(
    parameter USE_SB_IO = 1,
    parameter FLASH_SIZE_BITS = 24
) (
    axi4lite.slave bus,

    // QSPI flash pins
    output cs,
    output sclk,
    inout si,
    inout so,
    inout wp,
    inout hold
);

// TODO: Accept two read requests in fligth at once (since flash_reader supports it)
//          Note that if we scheduled the read on the flash without accepting it on the master, the master could cancel it before we go ready!
//          It's probably simpler to accept the transaction and hold the address than to handle cancellation on the next data_ready (a lot happens on data_ready already...)

    wire rst = !bus.aresetn; // Enjoy the extra LUT of delay on each side of the bus courtesy of the AMBA spec!
    wire data_ready;
    wire [7:0] data_byte;

    logic start_read;
    logic keep_reading;

    logic [63:0] read_data;
    logic [3:0] read_counter;

    wire [FLASH_SIZE_BITS-1:0] flash_addr = bus.araddr;

    flash_reader #(
        .USE_SB_IO(USE_SB_IO),
        .FLASH_SIZE_BITS(FLASH_SIZE_BITS)
    ) flash_reader (
        .clk(bus.aclk),
        .rst(rst),
        .addr(flash_addr),
        .start_read,
        .keep_reading,

        .data_ready,
        .data(data_byte),

        .cs,
        .sclk,
        .si,
        .so,
        .wp,
        .hold
    );

    assign bus.rresp = AXI4LITE_RESP_OKAY;
    assign bus.rdata = data_ready ? {data_byte, read_data[$bits(read_data)-1 : $bits(data_byte)]} : read_data;

    // We can update reader inputs combinatorially
    always_comb begin
        if (bus.arready && bus.arvalid) begin
            start_read = 'b1;
            keep_reading = 'b0;
        end else begin
            start_read = 'b0;
            keep_reading = |read_counter;
        end
    end

    always_ff @(posedge bus.aclk) begin
        if (rst) begin
            read_counter <= 'h0;
        end else if (bus.arready && bus.arvalid) begin
            read_counter <= 'h8;
        end else if (data_ready) begin
            read_counter <= read_counter - 1;
        end
    end

    always_ff @(posedge bus.aclk) begin
        if (rst) begin
            read_data <= 'x;
        end else if (data_ready) begin
            read_data <= {data_byte, read_data[$bits(read_data)-1 : $bits(data_byte)]};
        end
    end

    // Accept read requests
    always_ff @(posedge bus.aclk) begin
        if (rst) begin
            bus.arready <= 'b1;
        end else if (bus.arready && bus.arvalid) begin
            bus.arready <= 'b0;
        end else if (bus.rready && bus.rvalid) begin
            bus.arready <= 'b1;
        end
    end

    // Sign read responses
    always @(posedge bus.aclk) begin
        if (rst) begin
            bus.rvalid <= 'b0;
        end else if (bus.rready && bus.rvalid) begin
            bus.rvalid <= 'b0;
        end else if (read_counter == 'h1) begin
            bus.rvalid <= 'b1;
        end
    end

    // Respond to all writes with an error
    always @(posedge bus.aclk) begin
        if (rst) begin
            bus.awready <= 'b0;
            bus.wready <= 'b0;
            bus.bvalid <= 'b0;
            bus.bresp <= 'x;
        end else begin
            bus.awready <= bus.awvalid && bus.wvalid && !bus.awready;
            bus.wready <= bus.awvalid && bus.wvalid && !bus.wready;
            if (bus.bvalid && bus.bready)
                bus.bvalid <= 'b0;
            else if (bus.awvalid && bus.wvalid && bus.awready && bus.wready)
                bus.bvalid <= 'b1;
            bus.bresp <= AXI4LITE_RESP_SLVERR;
        end
    end

    `ifndef SYNTHESIS
    initial assert($bits(bus.rdata) == $bits(read_data));

    always @(posedge bus.aclk) begin
        assert property (@(posedge bus.aclk) bus.arready && bus.arvalid && !rst |=> start_read | keep_reading);
        assert property (@(posedge bus.aclk) bus.arready && bus.arvalid && !rst |=> |read_counter);
        assert property (@(posedge bus.aclk) bus.rvalid |=> !data_ready); // Don't overwrite valid read data

        assert property (@(posedge bus.aclk) start_read |-> !$isunknown(flash_reader.addr));
    end
    `endif

endmodule
