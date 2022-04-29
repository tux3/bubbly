`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module axi4lite_ethernet #(
    parameter TARGET = "XILINX",
    parameter ADDR_MASK = {`ALEN{1'b1}}
) (
    axi4lite.slave bus,

    input  wire       phy_rx_clk,
    input  wire [3:0] phy_rxd,
    input  wire       phy_rx_dv,
    input  wire       phy_rx_er,
    input  wire       phy_tx_clk,
    output wire [3:0] phy_txd,
    output wire       phy_tx_en,
    input  wire       phy_col,
    input  wire       phy_crs,
    output wire       phy_reset_n
);

wire rst = !bus.aresetn;
assign phy_reset_n = !rst;

// Ignore reads
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
            bus.rdata <= '0;
            bus.rresp <= AXI4LITE_RESP_OKAY;
        end else if (bus.rready && bus.rvalid) begin
            bus.rvalid <= 'b0;
            bus.rdata <= 'x;
            bus.rresp <= 'x;
        end
    end
end

// Ignore writes
always @(posedge bus.aclk) begin
    if (rst) begin
        bus.awready <= 'b0;
        bus.wready <= 'b0;
        bus.bvalid <= 'b0;
        bus.bresp <= 'x;
    end else begin
        bus.awready <= bus.awvalid && bus.wvalid && !bus.awready;
        bus.wready <= bus.awvalid && bus.wvalid && !bus.wready;
        if (bus.bvalid && bus.bready) begin
            bus.bvalid <= 'b0;
            bus.bresp <= 'x;
        end else if (bus.awvalid && bus.wvalid && bus.awready && bus.wready) begin
            bus.bvalid <= 'b1;
            bus.bresp <= AXI4LITE_RESP_OKAY;
        end
    end
end

// AXI between MAC and Ethernet modules
wire [7:0] rx_axis_tdata;
wire rx_axis_tvalid;
wire rx_axis_tready;
wire rx_axis_tlast;
wire rx_axis_tuser;

wire [7:0] tx_axis_tdata;
wire tx_axis_tvalid;
wire tx_axis_tready;
wire tx_axis_tlast;
wire tx_axis_tuser;

// Ethernet frame
wire rx_eth_hdr_ready;
wire rx_eth_hdr_valid;
wire [47:0] rx_eth_dest_mac;
wire [47:0] rx_eth_src_mac;
wire [15:0] rx_eth_type;
wire [7:0] rx_eth_payload_axis_tdata;
wire rx_eth_payload_axis_tvalid;
wire rx_eth_payload_axis_tready;
wire rx_eth_payload_axis_tlast;
wire rx_eth_payload_axis_tuser;

wire tx_eth_hdr_ready;
wire tx_eth_hdr_valid;
wire [47:0] tx_eth_dest_mac;
wire [47:0] tx_eth_src_mac;
wire [15:0] tx_eth_type;
wire [7:0] tx_eth_payload_axis_tdata;
wire tx_eth_payload_axis_tvalid;
wire tx_eth_payload_axis_tready;
wire tx_eth_payload_axis_tlast;
wire tx_eth_payload_axis_tuser;

eth_mac_mii_fifo #(
    .TARGET(TARGET),
    .CLOCK_INPUT_STYLE("BUFR"),
    .ENABLE_PADDING(1),
    .MIN_FRAME_LENGTH(64),
    .TX_FIFO_DEPTH(4096),
    .TX_FRAME_FIFO(1),
    .RX_FIFO_DEPTH(4096),
    .RX_FRAME_FIFO(1)
)
eth_mac_inst (
    .rst(rst),
    .logic_clk(bus.aclk),
    .logic_rst(rst),

    .tx_axis_tdata(tx_axis_tdata),
    .tx_axis_tvalid(tx_axis_tvalid),
    .tx_axis_tready(tx_axis_tready),
    .tx_axis_tlast(tx_axis_tlast),
    .tx_axis_tuser(tx_axis_tuser),

    .rx_axis_tdata(rx_axis_tdata),
    .rx_axis_tvalid(rx_axis_tvalid),
    .rx_axis_tready(rx_axis_tready),
    .rx_axis_tlast(rx_axis_tlast),
    .rx_axis_tuser(rx_axis_tuser),

    .mii_rx_clk(phy_rx_clk),
    .mii_rxd(phy_rxd),
    .mii_rx_dv(phy_rx_dv),
    .mii_rx_er(phy_rx_er),
    .mii_tx_clk(phy_tx_clk),
    .mii_txd(phy_txd),
    .mii_tx_en(phy_tx_en),
    .mii_tx_er(),

    .tx_fifo_overflow(),
    .tx_fifo_bad_frame(),
    .tx_fifo_good_frame(),
    .rx_error_bad_frame(),
    .rx_error_bad_fcs(),
    .rx_fifo_overflow(),
    .rx_fifo_bad_frame(),
    .rx_fifo_good_frame(),

    .ifg_delay(12)
);

eth_axis_rx
eth_axis_rx_inst (
    .clk(bus.aclk),
    .rst(rst),
    // AXI input
    .s_axis_tdata(rx_axis_tdata),
    .s_axis_tvalid(rx_axis_tvalid),
    .s_axis_tready(rx_axis_tready),
    .s_axis_tlast(rx_axis_tlast),
    .s_axis_tuser(rx_axis_tuser),
    // Ethernet frame output
    .m_eth_hdr_valid(rx_eth_hdr_valid),
    .m_eth_hdr_ready(rx_eth_hdr_ready),
    .m_eth_dest_mac(rx_eth_dest_mac),
    .m_eth_src_mac(rx_eth_src_mac),
    .m_eth_type(rx_eth_type),
    .m_eth_payload_axis_tdata(rx_eth_payload_axis_tdata),
    .m_eth_payload_axis_tvalid(rx_eth_payload_axis_tvalid),
    .m_eth_payload_axis_tready(rx_eth_payload_axis_tready),
    .m_eth_payload_axis_tlast(rx_eth_payload_axis_tlast),
    .m_eth_payload_axis_tuser(rx_eth_payload_axis_tuser),
    // Status signals
    .busy(),
    .error_header_early_termination()
);

eth_axis_tx
eth_axis_tx_inst (
    .clk(bus.aclk),
    .rst(rst),
    // Ethernet frame input
    .s_eth_hdr_valid(tx_eth_hdr_valid),
    .s_eth_hdr_ready(tx_eth_hdr_ready),
    .s_eth_dest_mac(tx_eth_dest_mac),
    .s_eth_src_mac(tx_eth_src_mac),
    .s_eth_type(tx_eth_type),
    .s_eth_payload_axis_tdata(tx_eth_payload_axis_tdata),
    .s_eth_payload_axis_tvalid(tx_eth_payload_axis_tvalid),
    .s_eth_payload_axis_tready(tx_eth_payload_axis_tready),
    .s_eth_payload_axis_tlast(tx_eth_payload_axis_tlast),
    .s_eth_payload_axis_tuser(tx_eth_payload_axis_tuser),
    // AXI output
    .m_axis_tdata(tx_axis_tdata),
    .m_axis_tvalid(tx_axis_tvalid),
    .m_axis_tready(tx_axis_tready),
    .m_axis_tlast(tx_axis_tlast),
    .m_axis_tuser(tx_axis_tuser),
    // Status signals
    .busy()
);

// Echo back ethernet frames..
assign tx_eth_hdr_valid = rx_eth_hdr_valid;
assign rx_eth_hdr_ready = tx_eth_hdr_ready;
assign tx_eth_dest_mac = rx_eth_src_mac;
assign tx_eth_src_mac = rx_eth_dest_mac;
assign tx_eth_hdr_valid = rx_eth_hdr_valid;
assign tx_eth_type = rx_eth_type;
assign tx_eth_payload_axis_tdata = rx_eth_payload_axis_tdata;
assign tx_eth_payload_axis_tvalid = rx_eth_payload_axis_tvalid;
assign rx_eth_payload_axis_tready = tx_eth_payload_axis_tready;
assign tx_eth_payload_axis_tlast = rx_eth_payload_axis_tlast;
assign tx_eth_payload_axis_tuser = rx_eth_payload_axis_tuser;

endmodule
