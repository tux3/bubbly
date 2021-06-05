`include "../axi/axi4lite.svh"
`include "../core/params.svh"

module axi4lite_gpio #(
    parameter NUM_OUTPUTS = 4,
    parameter ADDR_MASK = {`ALEN{1'b1}}
) (
    axi4lite.slave bus,
    output [NUM_OUTPUTS-1:0] outputs
);
    generate
        if (NUM_OUTPUTS > NUM_OUTPUTS+ADDR_MASK)
            $error("Cannot address more outputs than fit into ADDR_MASK");
    endgenerate
    localparam OUTPUT_REG_SIZE = NUM_OUTPUTS < 8 ? 8 : NUM_OUTPUTS;

    reg [OUTPUT_REG_SIZE-1:0] outputs_reg;
    assign outputs = outputs_reg[0 +: NUM_OUTPUTS];

    wire rst = !bus.aresetn;

    wire [`ALEN-1:0] araddr_comb = bus.araddr & ADDR_MASK;
    wire [7:0] rcomb = outputs_reg[araddr_comb +: 8];
    wire [63:0] rdata_comb = {7'b0, rcomb[7], 7'b0, rcomb[6], 7'b0, rcomb[5], 7'b0, rcomb[4],
                              7'b0, rcomb[3], 7'b0, rcomb[2], 7'b0, rcomb[1], 7'b0, rcomb[0]};
    wire [7:0] wdata_comb = {bus.wdata[56], bus.wdata[48], bus.wdata[40], bus.wdata[32],
                             bus.wdata[24], bus.wdata[16], bus.wdata[ 8], bus.wdata[ 0]};

    logic [`ALEN-1:0] waddr;
    logic [7:0] wstrb;
    logic [7:0] wdata;

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
                bus.rdata <= rdata_comb;
                bus.rresp <= araddr_comb + 8 > OUTPUT_REG_SIZE ? AXI4LITE_RESP_SLVERR : AXI4LITE_RESP_OKAY;
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
            waddr <= 'x;
            wdata <= 'x;
            wstrb <= 'x;
            outputs_reg <= '0;
        end else begin
            bus.awready <= bus.awvalid && bus.wvalid && !bus.awready;
            bus.wready <= bus.awvalid && bus.wvalid && !bus.wready;
            if (bus.awvalid && !bus.bvalid)
                waddr <= bus.awaddr & ADDR_MASK;
            if (bus.wvalid && !bus.bvalid) begin
                wdata <= wdata_comb;
                wstrb <= bus.wstrb;
            end

            if (bus.bvalid && bus.bready) begin
                bus.bvalid <= 'b0;
                bus.bresp <= 'x;
            end else if (bus.awvalid && bus.wvalid && bus.awready && bus.wready) begin
                bus.bvalid <= 'b1;
                if (waddr + 8 > OUTPUT_REG_SIZE) begin
                    bus.bresp <= AXI4LITE_RESP_SLVERR;
                end else begin
                    bus.bresp <= AXI4LITE_RESP_OKAY;
                    for (integer i=0; i < 8; i++) begin
                        if (wstrb[i])
                            outputs_reg[waddr + i] <= wdata[i];
                    end
                end
            end
        end
    end
endmodule
