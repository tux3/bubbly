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

wire clk = bus.aclk;
wire rst = !bus.aresetn;
assign phy_reset_n = !rst;

// NOTE: We mask out the three low bits of the address, you cannot do partial accesses at an offset.
//       *(reg0+3) still addresses *(reg0), while *(reg0+4) snaps to *(reg1). We also completely ignore the wstrb signal.
//       (and the core doesn't have a notion of non-cached memory regions yet, but the cacheline size *is* 64bits, so it works out!)
localparam NUM_MMIO_REGS = 2;
localparam MMIO_REGS_ALEN = $clog2(NUM_MMIO_REGS);
reg [47:0] mmio_eth_src_mac; // Reg 0: Source MAC to use for writes
reg [63:0] mmio_eth_ethertype_dst_mac; // Reg 1: Dest MAC and ethertype to use for writes
wire [15:0] mmio_eth_ethertype = mmio_eth_ethertype_dst_mac[48 +: 16];
wire [47:0] mmio_eth_dst_mac = mmio_eth_ethertype_dst_mac[0 +: 48];

// Handle reads
wire [`ALEN-1-3:0] bus_araddr_masked = (bus.araddr & ADDR_MASK) >> 3;
wire bus_araddr_bad_bits = bus_araddr_masked[`ALEN-1-3:MMIO_REGS_ALEN] != '0;

reg has_pending_araddr;
reg [MMIO_REGS_ALEN-1:0] pending_araddr;
reg pending_araddr_bad_bits;
wire [MMIO_REGS_ALEN-1:0] araddr_comb = has_pending_araddr ? pending_araddr : bus_araddr_masked;
wire araddr_bad_bits_comb = has_pending_araddr ? pending_araddr_bad_bits : bus_araddr_bad_bits;

wire ar_beat = bus.arvalid && bus.arready;
wire r_beat = bus.rvalid && bus.rready;
wire rdata_jam = bus.rvalid && !bus.rready;

wire is_reading = ar_beat || has_pending_araddr;
wire should_update_rdata = !rdata_jam && is_reading;
wire rvalid_next = is_reading || (bus.rvalid && !r_beat);

always_ff @(posedge clk) begin
    if (rst) begin
        bus.rvalid <= 'b0;
        bus.arready <= 'b0;
        bus.rdata <= 'x;
        bus.rresp <= 'x;
        
        has_pending_araddr <= '0;
        pending_araddr <= '0;
        pending_araddr_bad_bits <= '0;
    end else begin
        bus.arready <= !rvalid_next || !has_pending_araddr;

        if (rdata_jam) begin
            if (ar_beat) begin
                // We know !has_pending_araddr, as an invariant
                has_pending_araddr <= 'b1;
                pending_araddr <= bus_araddr_masked;
                pending_araddr_bad_bits <= bus_araddr_bad_bits;
            end
        end else if (!ar_beat) begin
            has_pending_araddr <= 'b0;
            pending_araddr <= 'x;
            pending_araddr_bad_bits <= 'x;
        end else if (has_pending_araddr) begin
            // No jam and an ar_beat means inflow = outflow
            pending_araddr <= bus_araddr_masked;
            pending_araddr_bad_bits <= bus_araddr_bad_bits;
        end
        
        if (is_reading)
            bus.rvalid <= 'b1;
        else if (r_beat)
            bus.rvalid <= 'b0;

        if (should_update_rdata) begin
            bus.rdata <= 'x;
            bus.rresp <= AXI4LITE_RESP_OKAY;
            if (araddr_bad_bits_comb) begin
                bus.rresp <= AXI4LITE_RESP_SLVERR;
            end else begin
                unique if (araddr_comb == 'h0) begin
                    bus.rdata <= {16'b0, mmio_eth_src_mac};
                end else if (araddr_comb == 'h1) begin
                    bus.rdata <= {16'b0, mmio_eth_ethertype_dst_mac};
                end else begin
                    bus.rresp <= AXI4LITE_RESP_SLVERR;
                end
            end
        end
    end
end

// Handle writes
wire [`ALEN-1-3:0] bus_waddr_masked = (bus.awaddr & ADDR_MASK) >> 3;
wire bus_waddr_bad_bits = bus_waddr_masked[`ALEN-1-3:MMIO_REGS_ALEN] != '0;

wire aw_beat = bus.awvalid && bus.awready;
wire w_beat = bus.wvalid && bus.wready;
wire b_beat = bus.bvalid && bus.bready;
wire b_jam = bus.bvalid && !bus.bready;

reg aw_pending;
reg w_pending;
wire aw_active = aw_beat || aw_pending;
wire w_active = w_beat || w_pending;

reg [MMIO_REGS_ALEN-1:0] waddr_buf;
reg waddr_bad_bits_buf;
reg [63:0] wdata_buf;
wire [MMIO_REGS_ALEN-1:0] waddr = aw_pending ? waddr_buf : bus_waddr_masked;
wire waddr_bad_bits = aw_pending ? waddr_bad_bits_buf : bus_waddr_bad_bits;
wire [63:0] wdata = w_pending ? wdata_buf : bus.wdata;

assign bus.awready = !aw_pending;
assign bus.wready = !w_pending;

// NOTE: AXI4 mandates ordering only for reads started _after_ a write response,
//       so we don't have to do the write until the moment we set bvalid.
always_ff @(posedge clk) begin
    if (rst) begin
        aw_pending <= '0;
        w_pending <= '0;
        waddr_buf <= 'x;
        waddr_bad_bits_buf <= 'x;
        wdata_buf <= 'x;
        
        mmio_eth_src_mac <= '0;
        mmio_eth_ethertype_dst_mac <= '0;
    end else if (aw_active && w_active && !(aw_pending && w_pending)) begin
        if (!waddr_bad_bits) begin
            unique if (waddr == 'h0) begin
                mmio_eth_src_mac <= wdata[47:0];
            end else if (waddr == 'h1) begin
                mmio_eth_ethertype_dst_mac <= wdata; 
            end else begin
                // No write
            end
        end
    
        if (b_jam) begin
            aw_pending <= '1;
            w_pending <= '1;
            waddr_buf <= bus_waddr_masked;
            waddr_bad_bits_buf <= bus_waddr_bad_bits;
            wdata_buf <= bus.wdata;
        end else begin
            aw_pending <= '0;
            w_pending <= '0;
            waddr_buf <= 'x;
            waddr_bad_bits_buf <= 'x;
            wdata_buf <= 'x;
        end
    end else begin
        if (aw_beat) begin
            aw_pending <= '1;
            waddr_buf <= bus_waddr_masked;
            waddr_bad_bits_buf <= bus_waddr_bad_bits;
        end else if (b_beat) begin
            aw_pending <= '0;
            waddr_buf <= 'x;
            waddr_bad_bits_buf <= 'x;
        end

        if (w_beat) begin
            w_pending <= '1;
            wdata_buf <= bus.wdata;
        end else if (b_beat) begin
            w_pending <= '0;
            wdata_buf <= 'x;
        end
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        bus.bvalid <= '0;
        bus.bresp <= 'x;
    end else if (b_jam) begin
        // Hold outputs stable
    end else if (aw_active && w_active) begin
        bus.bvalid <= '1;
        bus.bresp <= (waddr_bad_bits || waddr >= NUM_MMIO_REGS) ? AXI4LITE_RESP_SLVERR : AXI4LITE_RESP_OKAY;
    end else begin
        bus.bvalid <= '0;
        bus.bresp <= 'x;
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
    .logic_clk(clk),
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
    .clk(clk),
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
    .clk(clk),
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
assign tx_eth_dest_mac = mmio_eth_dst_mac;
assign tx_eth_src_mac = mmio_eth_src_mac;
assign tx_eth_hdr_valid = rx_eth_hdr_valid;
assign tx_eth_type = mmio_eth_ethertype;
assign tx_eth_payload_axis_tdata = rx_eth_payload_axis_tdata;
assign tx_eth_payload_axis_tvalid = rx_eth_payload_axis_tvalid;
assign rx_eth_payload_axis_tready = tx_eth_payload_axis_tready;
assign tx_eth_payload_axis_tlast = rx_eth_payload_axis_tlast;
assign tx_eth_payload_axis_tuser = rx_eth_payload_axis_tuser;


`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (is_reading && !rst |=> bus.rvalid);
    assert property (ar_beat |-> !rdata_jam || !has_pending_araddr);
    assert property (rdata_jam |-> !ar_beat || !has_pending_araddr);
end
`endif

endmodule
