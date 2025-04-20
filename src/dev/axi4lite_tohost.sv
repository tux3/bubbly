`include "../axi/axi4lite.svh"
`include "../core/params.svh"

/// Provides a very basic RISC-V tohost interface for debug text output
/// No other functions of tohost/fromhost are implemented

module axi4lite_tohost #(
    parameter ADDR_MASK = {`ALEN{1'b1}}
) (
    axi4lite.slave bus
);
    // ToHost protocol constants
    localparam DEVICE_BIT_POS = 56;
    localparam COMMAND_BIT_POS = 48;
    localparam DEVICE_CHAR = 8'h01;    // Device 1 is the blocking character device
    localparam COMMAND_WRITE_CHAR = 8'h01; // Device command 1 writes a character

    // Writes
    logic waddr_bad;
    logic [`ALEN-1:0] waddr;
    logic [7:0] wstrb;
    logic [63:0] wdata;

    wire [7:0] w_device = wdata[DEVICE_BIT_POS +: 8];
    wire [7:0] w_command = wdata[COMMAND_BIT_POS +: 8];

    string line_buffer = "";

    always @(posedge bus.aclk) begin
        if (!bus.aresetn) begin
            bus.awready <= 'b0;
            bus.wready <= 'b0;
            bus.bvalid <= 'b0;
            bus.bresp <= 'x;
            waddr <= 'x;
            wdata <= 'x;
            wstrb <= 'x;
        end else begin
            bus.awready <= bus.awvalid && bus.wvalid && !bus.awready;
            bus.wready <= bus.awvalid && bus.wvalid && !bus.wready;
            if (bus.awvalid && !bus.bvalid) begin
                waddr <= bus.awaddr & ADDR_MASK;
            end
            if (bus.wvalid && !bus.bvalid) begin
                wdata <= bus.wdata;
                wstrb <= bus.wstrb;
            end

            if (bus.bvalid && bus.bready) begin
                bus.bvalid <= 'b0;
                bus.bresp <= 'x;
            end else if (bus.awvalid && bus.wvalid && bus.awready && bus.wready) begin
                bus.bvalid <= 'b1;
                bus.bresp <= 'x;

                if (waddr == 'h0) begin
                    if (w_device == DEVICE_CHAR && w_command == COMMAND_WRITE_CHAR) begin
                        if (bus.wdata[7:0] == 'h0A) begin
                            $display("tohost dbg msg: %s", line_buffer);
                            $fflush();
                            line_buffer = "";
                        end else begin
                            line_buffer = {line_buffer, string'(bus.wdata[7:0])};
                        end
                        bus.bresp <= AXI4LITE_RESP_OKAY;
                    end else begin
                        bus.bresp <= AXI4LITE_RESP_SLVERR; // Unsupported command
                    end
                end else begin
                    bus.bresp <= AXI4LITE_RESP_DECERR; // Address not recognized
                end
            end
        end
    end

    // Reads
    wire [`ALEN-1:0] araddr_comb = bus.araddr & ADDR_MASK;
    always @(posedge bus.aclk) begin
        if (!bus.aresetn) begin
            bus.rvalid <= 'b0;
            bus.arready <= 'b0;
            bus.rdata <= 'x;
            bus.rresp <= 'x;
        end else begin
            bus.arready <= bus.arvalid && !bus.arready && (!bus.rvalid || bus.rready);
            if (bus.arready && bus.arvalid) begin
                bus.rvalid <= 'b1;
                if (araddr_comb == 'h0) begin
                    bus.rdata <= 'x;
                    bus.rresp <= AXI4LITE_RESP_SLVERR; // Valid address, but reading tohost make no sense
                end else begin
                    bus.rdata <= 'x;
                    bus.rresp <= AXI4LITE_RESP_DECERR; // Address not recognized
                end
            end else if (bus.rready && bus.rvalid) begin
                bus.rvalid <= 'b0;
                bus.rdata <= 'x;
                bus.rresp <= 'x;
            end
        end
    end
endmodule
