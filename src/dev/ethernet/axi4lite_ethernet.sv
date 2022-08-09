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

// With our 64bit MMIO regs, we can move 7 bytes worth in and out, so set the AXIS width to that
localparam ETH_AXIS_DATA_WIDTH = 7*8;

// AXI between MAC and Ethernet modules
wire [ETH_AXIS_DATA_WIDTH-1:0] rx_axis_tdata;
wire [ETH_AXIS_DATA_WIDTH/8-1:0] rx_axis_tkeep;
wire rx_axis_tvalid;
wire rx_axis_tready;
wire rx_axis_tlast;
wire rx_axis_tuser;

wire [ETH_AXIS_DATA_WIDTH-1:0] tx_axis_tdata;
wire [ETH_AXIS_DATA_WIDTH/8-1:0] tx_axis_tkeep;
wire tx_axis_tvalid;
wire tx_axis_tready;
wire tx_axis_tlast;
wire tx_axis_tuser;

// Ethernet frame
logic rx_eth_hdr_ready;
logic rx_eth_hdr_valid;
logic [47:0] rx_eth_dest_mac;
logic [47:0] rx_eth_src_mac;
logic [15:0] rx_eth_type;
logic [ETH_AXIS_DATA_WIDTH-1:0] rx_eth_payload_axis_tdata;
logic [ETH_AXIS_DATA_WIDTH/8-1:0] rx_eth_payload_axis_tkeep;
logic rx_eth_payload_axis_tvalid;
logic rx_eth_payload_axis_tready;
logic rx_eth_payload_axis_tlast;
logic rx_eth_payload_axis_tuser;

logic tx_eth_hdr_ready;
logic tx_eth_hdr_valid;
logic [47:0] tx_eth_dest_mac;
logic [47:0] tx_eth_src_mac;
logic [15:0] tx_eth_type;
logic [ETH_AXIS_DATA_WIDTH-1:0] tx_eth_payload_axis_tdata;
logic [ETH_AXIS_DATA_WIDTH/8-1:0] tx_eth_payload_axis_tkeep;
logic tx_eth_payload_axis_tvalid;
logic tx_eth_payload_axis_tready;
logic tx_eth_payload_axis_tlast;
logic tx_eth_payload_axis_tuser;

wire mac_tx_error_underflow;
wire mac_tx_fifo_overflow;
wire mac_tx_fifo_bad_frame;
wire mac_tx_fifo_good_frame;
wire mac_rx_error_bad_frame;
wire mac_rx_error_bad_fcs;
wire mac_rx_fifo_overflow;
wire mac_rx_fifo_bad_frame;
wire mac_rx_fifo_good_frame;

eth_mac_mii_fifo #(
    .TARGET(TARGET),
    .CLOCK_INPUT_STYLE("BUFR"),
    .AXIS_DATA_WIDTH(ETH_AXIS_DATA_WIDTH),
    .ENABLE_PADDING(1),
    .MIN_FRAME_LENGTH(64),
    .TX_FIFO_DEPTH(2048),
    .TX_FRAME_FIFO(1),
    .RX_FIFO_DEPTH(8192),
    .RX_FRAME_FIFO(1)
)
eth_mac_inst (
    .rst(rst),
    .logic_clk(clk),
    .logic_rst(rst),

    .tx_axis_tdata(tx_axis_tdata),
    .tx_axis_tkeep(tx_axis_tkeep),
    .tx_axis_tvalid(tx_axis_tvalid),
    .tx_axis_tready(tx_axis_tready),
    .tx_axis_tlast(tx_axis_tlast),
    .tx_axis_tuser(tx_axis_tuser),

    .rx_axis_tdata(rx_axis_tdata),
    .rx_axis_tkeep(rx_axis_tkeep),
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

    .tx_error_underflow(mac_tx_error_underflow),
    .tx_fifo_overflow(mac_tx_fifo_overflow),
    .tx_fifo_bad_frame(mac_tx_fifo_bad_frame),
    .tx_fifo_good_frame(mac_tx_fifo_good_frame),
    .rx_error_bad_frame(mac_rx_error_bad_frame),
    .rx_error_bad_fcs(mac_rx_error_bad_fcs),
    .rx_fifo_overflow(mac_rx_fifo_overflow),
    .rx_fifo_bad_frame(mac_rx_fifo_bad_frame),
    .rx_fifo_good_frame(mac_rx_fifo_good_frame),

    .ifg_delay(12)
);

eth_axis_rx #(
    .DATA_WIDTH(ETH_AXIS_DATA_WIDTH)
) eth_axis_rx_inst (
    .clk(clk),
    .rst(rst),
    // AXI input
    .s_axis_tdata(rx_axis_tdata),
    .s_axis_tkeep(rx_axis_tkeep),
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
    .m_eth_payload_axis_tkeep(rx_eth_payload_axis_tkeep),
    .m_eth_payload_axis_tvalid(rx_eth_payload_axis_tvalid),
    .m_eth_payload_axis_tready(rx_eth_payload_axis_tready),
    .m_eth_payload_axis_tlast(rx_eth_payload_axis_tlast),
    .m_eth_payload_axis_tuser(rx_eth_payload_axis_tuser),
    // Status signals
    .busy(),
    .error_header_early_termination()
);

eth_axis_tx #(
    .DATA_WIDTH(ETH_AXIS_DATA_WIDTH)
) eth_axis_tx_inst (
    .clk(clk),
    .rst(rst),
    // Ethernet frame input
    .s_eth_hdr_valid(tx_eth_hdr_valid),
    .s_eth_hdr_ready(tx_eth_hdr_ready),
    .s_eth_dest_mac(tx_eth_dest_mac),
    .s_eth_src_mac(tx_eth_src_mac),
    .s_eth_type(tx_eth_type),
    .s_eth_payload_axis_tdata(tx_eth_payload_axis_tdata),
    .s_eth_payload_axis_tkeep(tx_eth_payload_axis_tkeep),
    .s_eth_payload_axis_tvalid(tx_eth_payload_axis_tvalid),
    .s_eth_payload_axis_tready(tx_eth_payload_axis_tready),
    .s_eth_payload_axis_tlast(tx_eth_payload_axis_tlast),
    .s_eth_payload_axis_tuser(tx_eth_payload_axis_tuser),
    // AXI output
    .m_axis_tdata(tx_axis_tdata),
    .m_axis_tkeep(tx_axis_tkeep),
    .m_axis_tvalid(tx_axis_tvalid),
    .m_axis_tready(tx_axis_tready),
    .m_axis_tlast(tx_axis_tlast),
    .m_axis_tuser(tx_axis_tuser),
    // Status signals
    .busy()
);

// IP packets
logic        tx_ip_hdr_valid;
wire         tx_ip_hdr_ready;
logic [5:0]  tx_ip_dscp;
logic [1:0]  tx_ip_ecn;
logic [15:0] tx_ip_length;
logic [7:0]  tx_ip_ttl;
logic [7:0]  tx_ip_protocol;
logic [31:0] tx_ip_source_ip;
logic [31:0] tx_ip_dest_ip;
logic [55:0] tx_ip_payload_axis_tdata;
logic [6:0]  tx_ip_payload_axis_tkeep;
logic        tx_ip_payload_axis_tvalid;
wire         tx_ip_payload_axis_tready;
logic        tx_ip_payload_axis_tlast;
logic        tx_ip_payload_axis_tuser;

wire        rx_ip_hdr_valid;
logic       rx_ip_hdr_ready;
wire [47:0] rx_ip_eth_dest_mac;
wire [47:0] rx_ip_eth_src_mac;
wire [15:0] rx_ip_eth_type;
wire [3:0]  rx_ip_version;
wire [3:0]  rx_ip_ihl;
wire [5:0]  rx_ip_dscp;
wire [1:0]  rx_ip_ecn;
wire [15:0] rx_ip_length;
wire [15:0] rx_ip_identification;
wire [2:0]  rx_ip_flags;
wire [12:0] rx_ip_fragment_offset;
wire [7:0]  rx_ip_ttl;
wire [7:0]  rx_ip_protocol;
wire [15:0] rx_ip_header_checksum;
wire [31:0] rx_ip_source_ip;
wire [31:0] rx_ip_dest_ip;
wire [55:0] rx_ip_payload_axis_tdata;
wire [6:0]  rx_ip_payload_axis_tkeep;
wire        rx_ip_payload_axis_tvalid;
logic       rx_ip_payload_axis_tready;
wire        rx_ip_payload_axis_tlast;
wire        rx_ip_payload_axis_tuser;

wire ip_rx_error_header_early_termination;
wire ip_rx_error_payload_early_termination;
wire ip_rx_error_invalid_header;
wire ip_rx_error_invalid_checksum;
wire ip_tx_error_payload_early_termination;
wire ip_tx_error_arp_failed;

logic [47:0] tx_ip_local_mac;
logic [31:0] tx_ip_local_ip;
logic [31:0] tx_ip_gateway_ip;
logic [31:0] tx_ip_subnet_mask;
logic tx_ip_clear_arp_cache;

ip_complete_56 #(
    .ARP_CACHE_ADDR_WIDTH(5),
    .ARP_REQUEST_RETRY_COUNT(2),
    .ARP_REQUEST_RETRY_INTERVAL(32500000*1),
    .ARP_REQUEST_TIMEOUT(32500000*5)
) ip_complete (
    .clk(clk),
    .rst(rst),

    // Ethernet frame input
    .s_eth_hdr_valid(rx_eth_hdr_valid),
    .s_eth_hdr_ready(rx_eth_hdr_ready),
    .s_eth_dest_mac(rx_eth_dest_mac),
    .s_eth_src_mac(rx_eth_src_mac),
    .s_eth_type(rx_eth_type),
    .s_eth_payload_axis_tdata(rx_eth_payload_axis_tdata),
    .s_eth_payload_axis_tkeep(rx_eth_payload_axis_tkeep),
    .s_eth_payload_axis_tvalid(rx_eth_payload_axis_tvalid),
    .s_eth_payload_axis_tready(rx_eth_payload_axis_tready),
    .s_eth_payload_axis_tlast(rx_eth_payload_axis_tlast),
    .s_eth_payload_axis_tuser(rx_eth_payload_axis_tuser),
    // Ethernet frame output    
    .m_eth_hdr_valid(tx_eth_hdr_valid),
    .m_eth_hdr_ready(tx_eth_hdr_ready),
    .m_eth_dest_mac(tx_eth_dest_mac),
    .m_eth_src_mac(tx_eth_src_mac),
    .m_eth_type(tx_eth_type),
    .m_eth_payload_axis_tdata(tx_eth_payload_axis_tdata),
    .m_eth_payload_axis_tkeep(tx_eth_payload_axis_tkeep),
    .m_eth_payload_axis_tvalid(tx_eth_payload_axis_tvalid),
    .m_eth_payload_axis_tready(tx_eth_payload_axis_tready),
    .m_eth_payload_axis_tlast(tx_eth_payload_axis_tlast),
    .m_eth_payload_axis_tuser(tx_eth_payload_axis_tuser),

    // IP frame input
    .s_ip_hdr_valid(tx_ip_hdr_valid),
    .s_ip_hdr_ready(tx_ip_hdr_ready),
    .s_ip_dscp(tx_ip_dscp),
    .s_ip_ecn(tx_ip_ecn),
    .s_ip_length(tx_ip_length),
    .s_ip_ttl(tx_ip_ttl),
    .s_ip_protocol(tx_ip_protocol),
    .s_ip_source_ip(tx_ip_source_ip),
    .s_ip_dest_ip(tx_ip_dest_ip),
    .s_ip_payload_axis_tdata(tx_ip_payload_axis_tdata),
    .s_ip_payload_axis_tkeep(tx_ip_payload_axis_tkeep),
    .s_ip_payload_axis_tvalid(tx_ip_payload_axis_tvalid),
    .s_ip_payload_axis_tready(tx_ip_payload_axis_tready),
    .s_ip_payload_axis_tlast(tx_ip_payload_axis_tlast),
    .s_ip_payload_axis_tuser(tx_ip_payload_axis_tuser),
    // IP frame output
    .m_ip_hdr_valid(rx_ip_hdr_valid),
    .m_ip_hdr_ready(rx_ip_hdr_ready),
    .m_ip_eth_dest_mac(rx_ip_eth_dest_mac),
    .m_ip_eth_src_mac(rx_ip_eth_src_mac),
    .m_ip_eth_type(rx_ip_eth_type),
    .m_ip_version(rx_ip_version),
    .m_ip_ihl(rx_ip_ihl),
    .m_ip_dscp(rx_ip_dscp),
    .m_ip_ecn(rx_ip_ecn),
    .m_ip_length(rx_ip_length),
    .m_ip_identification(rx_ip_identification),
    .m_ip_flags(rx_ip_flags),
    .m_ip_fragment_offset(rx_ip_fragment_offset),
    .m_ip_ttl(rx_ip_ttl),
    .m_ip_protocol(rx_ip_protocol),
    .m_ip_header_checksum(rx_ip_header_checksum),
    .m_ip_source_ip(rx_ip_source_ip),
    .m_ip_dest_ip(rx_ip_dest_ip),
    .m_ip_payload_axis_tdata(rx_ip_payload_axis_tdata),
    .m_ip_payload_axis_tkeep(rx_ip_payload_axis_tkeep),
    .m_ip_payload_axis_tvalid(rx_ip_payload_axis_tvalid),
    .m_ip_payload_axis_tready(rx_ip_payload_axis_tready),
    .m_ip_payload_axis_tlast(rx_ip_payload_axis_tlast),
    .m_ip_payload_axis_tuser(rx_ip_payload_axis_tuser),

    // Status signals
    .rx_busy(),
    .tx_busy(),
    .rx_error_header_early_termination(ip_rx_error_header_early_termination),
    .rx_error_payload_early_termination(ip_rx_error_payload_early_termination),
    .rx_error_invalid_header(ip_rx_error_invalid_header),
    .rx_error_invalid_checksum(ip_rx_error_invalid_checksum),
    .tx_error_payload_early_termination(ip_tx_error_payload_early_termination),
    .tx_error_arp_failed(ip_tx_error_arp_failed),

    // Configuration
    .local_mac(tx_ip_local_mac),
    .local_ip(tx_ip_local_ip),
    .gateway_ip(tx_ip_gateway_ip),
    .subnet_mask(tx_ip_subnet_mask),
    .clear_arp_cache(tx_ip_clear_arp_cache)
);

// NOTE: We mask out the three low bits of the address, you cannot do partial accesses at an offset.
//       *(reg0+3) still addresses *(reg0), while *(reg0+4) snaps to *(reg1). We also completely ignore the wstrb signal.
//       (and the core doesn't have a notion of non-cached memory regions yet, but the cacheline size *is* 64bits, so it works out!)
localparam NUM_MMIO_REGS = 11;
localparam MMIO_REGS_ALEN = $clog2(NUM_MMIO_REGS);
reg [47:0] mmio_eth_src_mac; // Reg 0: Source MAC to use for writes
reg [63:0] mmio_ip_ttl_proto_len_dst_ip; // Reg 1: Dest IP, tx len, IP proto, TTL
wire [7:0] mmio_ip_tx_ttl = mmio_ip_ttl_proto_len_dst_ip[56 +: 8];
wire [7:0] mmio_ip_tx_proto = mmio_ip_ttl_proto_len_dst_ip[48 +: 8];
wire [15:0] mmio_ip_tx_len = mmio_ip_ttl_proto_len_dst_ip[32 +: 16];
wire [47:0] mmio_dst_ip = mmio_ip_ttl_proto_len_dst_ip[0 +: 32];
// Reg 2 (virtual): Sent data 
reg [47:0] mmio_eth_rx_srx_mac; // Reg 3: Source MAC of the last packet we started receiving
reg [63:0] mmio_eth_rx_ethertype_dst_mac; // Reg 4: Dest MAC and ethertype of last packet we started receiving
// Reg 5 (virtual): Received data
// Reg 6: Src IP, misc IP flags
reg [39:0] mmio_ip_dscp_ecn_src_ip;
wire [5:0] mmio_ip_tx_dscp = mmio_ip_dscp_ecn_src_ip[34 +: 6];
wire [1:0] mmio_ip_tx_ecn = mmio_ip_dscp_ecn_src_ip[32 +: 2];
wire [31:0] mmio_src_ip = mmio_ip_dscp_ecn_src_ip[0 +: 32];
// Reg 7: Gateway IP, subnet mask
reg [63:0] mmio_gateway_ip_subnet_mask;
wire [31:0] mmio_gateway_ip = mmio_gateway_ip_subnet_mask[32 +: 32];
wire [31:0] mmio_subnet_mask = mmio_gateway_ip_subnet_mask[0 +: 32];
reg [63:0] mmio_ip_rx_src_ip_dst_ip; // Reg 8: Src/dst IP of last received packet
reg [63:0] mmio_ip_rx_ttl_proto_id_len_frag; // Reg 9: Misc headers of last received packet
reg [31:0] mmio_ip_rx_dscp_ecn_ver_ihl_chksum; // Reg 10: Misc headers of last received packet

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

// State for MMIO reg 5 reads
reg ip_rx_reading; // Set when we've acknowledged the first AXIS beat of a received packet, unset after getting the AXI `last` bit
logic [2:0] ip_rx_read_size;
always_comb unique casez (rx_ip_payload_axis_tkeep)
    'bzzzzzz0: ip_rx_read_size = 0;
    'bzzzzz01: ip_rx_read_size = 1;
    'bzzzz011: ip_rx_read_size = 2;
    'bzzz0111: ip_rx_read_size = 3;
    'bzz01111: ip_rx_read_size = 4;
    'bz011111: ip_rx_read_size = 5;
    'b0111111: ip_rx_read_size = 6;
    'b1111111: ip_rx_read_size = 7;
endcase

// NOTE: We don't check araddr is valid here to save combinatorial time.
// If you read an invalid addr that ends like MMIO reg 5, we'll drop a beat of data on the floor.
wire reading_mmio_reg5 = should_update_rdata && araddr_comb == 'h5;
assign rx_ip_hdr_ready = reading_mmio_reg5 && !ip_rx_reading;
assign rx_ip_payload_axis_tready = reading_mmio_reg5;

always_ff @(posedge clk) begin
    if (rst) begin
        bus.rvalid <= 'b0;
        bus.arready <= 'b0;
        bus.rdata <= 'x;
        bus.rresp <= 'x;
        
        has_pending_araddr <= '0;
        pending_araddr <= 'x;
        pending_araddr_bad_bits <= 'x;
        
        ip_rx_reading <= '0;
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
                    bus.rdata <= mmio_ip_ttl_proto_len_dst_ip;
                end else if (araddr_comb == 'h3) begin
                    bus.rdata <= {16'b0, mmio_eth_rx_srx_mac};
                end else if (araddr_comb == 'h4) begin
                    bus.rdata <= mmio_eth_rx_ethertype_dst_mac;
                end else if (araddr_comb == 'h5) begin
                    // Read ethernet frame from AXIS rx, if available
                    if (!ip_rx_reading && rx_ip_hdr_valid) begin
                        ip_rx_reading <= !rx_ip_payload_axis_tvalid || !rx_ip_payload_axis_tlast;
                        mmio_eth_rx_srx_mac <= rx_ip_eth_src_mac;
                        mmio_eth_rx_ethertype_dst_mac <= {rx_ip_eth_type, rx_ip_eth_dest_mac};
                        mmio_ip_rx_src_ip_dst_ip <= {rx_ip_source_ip, rx_ip_dest_ip};
                        mmio_ip_rx_ttl_proto_id_len_frag <= {rx_ip_ttl, rx_ip_protocol, rx_ip_identification,
                                                rx_ip_length, rx_ip_flags, rx_ip_fragment_offset};
                        mmio_ip_rx_dscp_ecn_ver_ihl_chksum <= {rx_ip_dscp, rx_ip_ecn, rx_ip_version,
                                                rx_ip_ihl, rx_ip_header_checksum};

                        bus.rdata <= {1'b1, rx_ip_payload_axis_tvalid && rx_ip_payload_axis_tlast, 3'b0,
                                    rx_ip_payload_axis_tvalid ? ip_rx_read_size : 3'b0, rx_ip_payload_axis_tdata};
                    end else if (ip_rx_reading && rx_ip_payload_axis_tvalid) begin
                        ip_rx_reading <= !rx_ip_payload_axis_tlast;
                        bus.rdata <= {1'b1, rx_ip_payload_axis_tlast, 3'b0, ip_rx_read_size, rx_ip_payload_axis_tdata};
                    end else begin
                        bus.rdata <= '0; // All 0 means not valid, not last, 0 bytes received
                    end
                end else if (araddr_comb == 'h6) begin
                    bus.rdata <= {24'b0, mmio_ip_dscp_ecn_src_ip};
                end else if (araddr_comb == 'h7) begin
                    bus.rdata <= mmio_gateway_ip_subnet_mask;
                end else if (araddr_comb == 'h8) begin
                    bus.rdata <= mmio_ip_rx_src_ip_dst_ip;
                end else if (araddr_comb == 'h9) begin
                    bus.rdata <= mmio_ip_rx_ttl_proto_id_len_frag;
                end else if (araddr_comb == 'hA) begin
                    bus.rdata <= {31'b0, mmio_ip_rx_dscp_ecn_ver_ihl_chksum};
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

// State for MMIO reg 2 writes
reg ip_tx_writing; // Set when we've handshaked the first AXIS beat of a sent packet, unset after sending the AXI `last` bit
reg ip_tx_writing_first_header; // Set if we're waiting for our header to go out
reg ip_tx_writing_first_data; // Set if we've written the header, but the first tx data hasn't been handshaken yet

wire ip_tx_last_flag = ip_tx_writing_first_data ? wdata_buf[63-1] : wdata[63-1];
wire [ETH_AXIS_DATA_WIDTH-1:0] ip_tx_payload_data = ip_tx_writing_first_data ? wdata_buf[ETH_AXIS_DATA_WIDTH-1:0] : wdata[ETH_AXIS_DATA_WIDTH-1:0];
logic [ETH_AXIS_DATA_WIDTH/8-1:0] ip_tx_write_size;
always_comb unique case (ip_tx_writing_first_data ? wdata_buf[ETH_AXIS_DATA_WIDTH +: 3] : wdata[ETH_AXIS_DATA_WIDTH +: 3])
    0: ip_tx_write_size = 'b0000000;
    1: ip_tx_write_size = 'b0000001;
    2: ip_tx_write_size = 'b0000011;
    3: ip_tx_write_size = 'b0000111;
    4: ip_tx_write_size = 'b0001111;
    5: ip_tx_write_size = 'b0011111;
    6: ip_tx_write_size = 'b0111111;
    7: ip_tx_write_size = 'b1111111;
endcase

wire ip_tx_write_ready = !ip_tx_writing_first_data &&
                    (!ip_tx_writing || tx_ip_payload_axis_tready);
wire writing_mmio_reg2 = aw_active && w_active && waddr == 'h2;

assign bus.awready = !aw_pending && ip_tx_write_ready;
assign bus.wready = !w_pending && ip_tx_write_ready && !ip_tx_writing_first_data;

// NOTE: Our valid depends on the ready for the header, which is against the AXI spec, but it should work for this particular device
assign tx_ip_hdr_valid = (writing_mmio_reg2 && !ip_tx_writing) || ip_tx_writing_first_header;
assign tx_ip_dscp = mmio_ip_tx_dscp;
assign tx_ip_ecn = mmio_ip_tx_ecn;
assign tx_ip_length = mmio_ip_tx_len;
assign tx_ip_ttl = mmio_ip_tx_ttl;
assign tx_ip_protocol = mmio_ip_tx_proto;
assign tx_ip_source_ip = mmio_src_ip;
assign tx_ip_dest_ip = mmio_dst_ip;
assign tx_ip_payload_axis_tdata = ip_tx_payload_data;
assign tx_ip_payload_axis_tkeep = ip_tx_write_size;
assign tx_ip_payload_axis_tvalid = writing_mmio_reg2 || ip_tx_writing_first_data;
assign tx_ip_payload_axis_tlast = ip_tx_last_flag;
assign tx_ip_payload_axis_tuser = '0;

assign tx_ip_local_mac = mmio_eth_src_mac;
assign tx_ip_local_ip = mmio_src_ip;
assign tx_ip_gateway_ip = mmio_gateway_ip;
assign tx_ip_subnet_mask = mmio_subnet_mask;
assign tx_ip_clear_arp_cache = '0;

always_ff @(posedge clk) begin
    if (rst) begin
        ip_tx_writing_first_header <= '0;
        ip_tx_writing_first_data <= '0;
    end else if (writing_mmio_reg2 && !ip_tx_writing) begin
        ip_tx_writing_first_header <= !tx_ip_hdr_ready;
        ip_tx_writing_first_data <= '1;
    end else begin
        if (tx_ip_hdr_ready)
            ip_tx_writing_first_header <= '0;
        if (tx_ip_payload_axis_tready)
            ip_tx_writing_first_data <= '0;
    end
end

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
        mmio_ip_ttl_proto_len_dst_ip <= '0;
        mmio_ip_dscp_ecn_src_ip <= '0;
        mmio_gateway_ip_subnet_mask <= '0;
    end else if (aw_active && w_active && !(aw_pending && w_pending)) begin
        if (!waddr_bad_bits) begin
            unique if (waddr == 'h0) begin
                mmio_eth_src_mac <= wdata[47:0];
            end else if (waddr == 'h1) begin
                mmio_ip_ttl_proto_len_dst_ip <= wdata;
            end else if (waddr == 'h2) begin
                // Write packet to AXIS tx, if ready
                if (!ip_tx_writing) begin
                    ip_tx_writing <= !ip_tx_last_flag;
                end else if (ip_tx_writing && tx_ip_payload_axis_tready) begin
                    ip_tx_writing <= !ip_tx_last_flag;
                end
            end else if (waddr == 'h6) begin
                mmio_ip_dscp_ecn_src_ip <= wdata;
            end else if (waddr == 'h7) begin
                mmio_gateway_ip_subnet_mask <= wdata;
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
            wdata_buf <= bus.wdata; // Our payload write can be delayed, even after a b beat
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

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (is_reading && !rst |=> bus.rvalid);
    assert property (ar_beat |-> !rdata_jam || !has_pending_araddr);
    assert property (rdata_jam |-> !ar_beat || !has_pending_araddr);
    assert property (rx_ip_payload_axis_tready |-> ip_rx_reading || (rx_ip_payload_axis_tvalid && rx_ip_hdr_valid));
end
`endif

endmodule
