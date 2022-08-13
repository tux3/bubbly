`include "../axi/axi4lite.svh"
`include "../core/params.svh"

/// Provides mtime/mtimecmp and GPIO

module axi4lite_platform #(
    parameter NUM_OUTPUTS = 4,
    parameter ADDR_MASK = {`ALEN{1'b1}}
) (
    axi4lite.slave bus,
    input mtime_clk,
    output logic mtime_int,
    output [NUM_OUTPUTS-1:0] outputs
);
    localparam NUM_TIME_REGS = 2;
    localparam OUTPUT_REG_SIZE = NUM_OUTPUTS < 8 ? 8 : NUM_OUTPUTS;
    localparam GPIO_ADDR_BASE_OFFSET = NUM_TIME_REGS*8;

    localparam LOWEST_INVALID_ADDR = GPIO_ADDR_BASE_OFFSET + OUTPUT_REG_SIZE;
    localparam ADDR_GOOD_BITS = $clog2(LOWEST_INVALID_ADDR);
    localparam ADDR_BAD_MASK = {{64-ADDR_GOOD_BITS{1'b1}}, {ADDR_GOOD_BITS{1'b0}}};

    generate
        if (NUM_OUTPUTS > $clog2(($bits(ADDR_MASK)+1)'(ADDR_MASK)+1))
            $error("Cannot address more outputs than fit into ADDR_MASK");
    endgenerate

    wire rst = !bus.aresetn;

    reg [63:0] mtime;
    reg [63:0] mtimecmp;
    assign mtime_int = mtime >= mtimecmp;

    reg [3:0] mtime_tick_sync;
    always @(posedge bus.aclk) begin
        if (rst)
            mtime_tick_sync <= '0;
        else
            mtime_tick_sync <= {mtime_tick_sync, mtime_clk};
    end
    wire increment_mtime =  !mtime_tick_sync[$bits(mtime_tick_sync)-1]
                          && mtime_tick_sync[$bits(mtime_tick_sync)-2]
                          && mtime_tick_sync[$bits(mtime_tick_sync)-3];

    reg [OUTPUT_REG_SIZE-1:0] outputs_reg;
    assign outputs = outputs_reg[0 +: NUM_OUTPUTS];

    wire [`ALEN-1:0] araddr_comb = bus.araddr & ADDR_MASK;
    wire [ADDR_GOOD_BITS-1:0] araddr_gpio_off_comb = araddr_comb[ADDR_GOOD_BITS-1:0] - GPIO_ADDR_BASE_OFFSET;
    wire araddr_bad_comb = araddr_comb & ADDR_BAD_MASK != '0;
    wire [7:0] rgpio_comb = outputs_reg[araddr_gpio_off_comb +: 8];
    wire [63:0] rdata_gpio_comb = {7'b0, rgpio_comb[7], 7'b0, rgpio_comb[6], 7'b0, rgpio_comb[5], 7'b0, rgpio_comb[4],
                                   7'b0, rgpio_comb[3], 7'b0, rgpio_comb[2], 7'b0, rgpio_comb[1], 7'b0, rgpio_comb[0]};

    logic waddr_bad;
    logic [ADDR_GOOD_BITS-1:0] waddr;
    logic [7:0] wstrb;
    logic [63:0] wdata;
    wire [7:0] wdata_gpio = {wdata[56], wdata[48], wdata[40], wdata[32],
                             wdata[24], wdata[16], wdata[ 8], wdata[ 0]};

    // Reads
    always @(posedge bus.aclk) begin
        if (rst) begin
            bus.rvalid <= 'b0;
            bus.arready <= 'b0;
            bus.rdata <= 'x;
            bus.rresp <= 'x;
        end else begin
            bus.arready <= bus.arvalid && !bus.arready && (!bus.rvalid || bus.rready);
            if (bus.arready && bus.arvalid) begin
                bus.rvalid <= 'b1;
                if (araddr_bad_comb) begin
                    bus.rresp <= AXI4LITE_RESP_SLVERR;
                end else if (araddr_comb == 'h0) begin
                    bus.rdata <= mtime;
                    bus.rresp <= AXI4LITE_RESP_OKAY;
                end else if (araddr_comb == 'h8) begin
                    bus.rdata <= mtimecmp;
                    bus.rresp <= AXI4LITE_RESP_OKAY;
                end else if (araddr_comb >= GPIO_ADDR_BASE_OFFSET && araddr_gpio_off_comb + 8 <= OUTPUT_REG_SIZE) begin
                    bus.rdata <= rdata_gpio_comb;
                    bus.rresp <= AXI4LITE_RESP_OKAY;
                end else begin
                    bus.rdata <= 'x;
                    bus.rresp <= AXI4LITE_RESP_SLVERR;
                end
            end else if (bus.rready && bus.rvalid) begin
                bus.rvalid <= 'b0;
                bus.rdata <= 'x;
                bus.rresp <= 'x;
            end
        end
    end

    // Writes
    always @(posedge bus.aclk) begin
        if (rst) begin
            bus.awready <= 'b0;
            bus.wready <= 'b0;
            bus.bvalid <= 'b0;
            bus.bresp <= 'x;
            waddr_bad <= 'x;
            waddr <= 'x;
            wdata <= 'x;
            wstrb <= 'x;

            mtime <= '0;
            mtimecmp <= '0;
        end else begin
            if (increment_mtime)
                mtime <= mtime + 1;

            bus.awready <= bus.awvalid && bus.wvalid && !bus.awready;
            bus.wready <= bus.awvalid && bus.wvalid && !bus.wready;
            if (bus.awvalid && !bus.bvalid) begin
                waddr_bad <= (bus.awaddr & ADDR_MASK & ADDR_BAD_MASK) != '0;
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
                bus.bresp <= AXI4LITE_RESP_OKAY;

                if (waddr_bad) begin
                    bus.bresp <= AXI4LITE_RESP_SLVERR;
                end else if (waddr == 'h0) begin
                    for (integer i=0; i < 8; i++)
                        if (wstrb[i])
                            mtime[8*i +: 8] <= wdata[8*i +: 8];
                end else if (waddr == 'h8) begin
                    for (integer i=0; i < 8; i++)
                        if (wstrb[i])
                            mtimecmp[8*i +: 8] <= wdata[8*i +: 8];
                end else if (waddr < GPIO_ADDR_BASE_OFFSET || waddr + 8 > GPIO_ADDR_BASE_OFFSET + OUTPUT_REG_SIZE) begin
                    bus.bresp <= AXI4LITE_RESP_SLVERR;
                end else begin
                    for (integer i=0; i < 8; i++) begin
                        if (wstrb[i])
                            outputs_reg[(waddr - GPIO_ADDR_BASE_OFFSET) + i] <= wdata_gpio[i];
                    end
                end
            end
        end
    end
endmodule
