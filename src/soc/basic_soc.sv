`include "../core/params.svh"
`include "../axi/axi4lite.svh"

module basic_soc#(
    parameter RESET_PC = `RESET_PC,
    parameter GPIO_OUTPUTS = 4,
    parameter SRAM_SIZE_KB = 8
) (
    input clk,
    input rst,

    // ROM flash interface
    output cs,
    output sclk,
    input capture_clk,
    inout si,
    inout so,
    inout wp,
    inout hold,

    // Core debug
    output [`ALEN+`ILEN-1:0] fetch_instr,
    output [`XLEN-1:0] reg_pc,
    input [4:0] reg_read_sel,
    output [`XLEN-1:0] reg_read_data,
    output [GPIO_OUTPUTS-1:0] gpio_outputs
);

axilxbar #(
    .C_AXI_DATA_WIDTH(64),
    .C_AXI_ADDR_WIDTH(`ALEN),
    .NM(2),
    .NS(4)
) sys_bus (
    .S_AXI_ACLK(clk),
    .S_AXI_ARESETN(!rst),

    // Core
    .S_AXI_AWADDR({ ifetch_axi.awaddr, data_axi.awaddr }),
    .S_AXI_AWPROT({ ifetch_axi.awprot, data_axi.awprot }),
    .S_AXI_AWVALID({ ifetch_axi.awvalid, data_axi.awvalid }),
    .S_AXI_AWREADY({ ifetch_axi.awready, data_axi.awready }),

    .S_AXI_WDATA({ ifetch_axi.wdata, data_axi.wdata }),
    .S_AXI_WSTRB({ ifetch_axi.wstrb, data_axi.wstrb }),
    .S_AXI_WVALID({ ifetch_axi.wvalid, data_axi.wvalid }),
    .S_AXI_WREADY({ ifetch_axi.wready, data_axi.wready }),

    .S_AXI_BRESP({ ifetch_axi.bresp, data_axi.bresp }),
    .S_AXI_BVALID({ ifetch_axi.bvalid, data_axi.bvalid }),
    .S_AXI_BREADY({ ifetch_axi.bready, data_axi.bready }),

    .S_AXI_ARADDR({ ifetch_axi.araddr, data_axi.araddr }),
    .S_AXI_ARPROT({ ifetch_axi.arprot, data_axi.arprot }),
    .S_AXI_ARVALID({ ifetch_axi.arvalid, data_axi.arvalid }),
    .S_AXI_ARREADY({ ifetch_axi.arready, data_axi.arready }),

    .S_AXI_RDATA({ ifetch_axi.rdata, data_axi.rdata }),
    .S_AXI_RRESP({ ifetch_axi.rresp, data_axi.rresp }),
    .S_AXI_RVALID({ ifetch_axi.rvalid, data_axi.rvalid }),
    .S_AXI_RREADY({ ifetch_axi.rready, data_axi.rready }),

    // Devices
    .M_AXI_AWADDR({ eth_axi.awaddr, platform_axi.awaddr, sram_axi.awaddr, flash_axi.awaddr }),
    .M_AXI_AWPROT({ eth_axi.awprot, platform_axi.awprot, sram_axi.awprot, flash_axi.awprot }),
    .M_AXI_AWVALID({ eth_axi.awvalid, platform_axi.awvalid, sram_axi.awvalid, flash_axi.awvalid }),
    .M_AXI_AWREADY({ eth_axi.awready, platform_axi.awready, sram_axi.awready, flash_axi.awready }),

    .M_AXI_WDATA({ eth_axi.wdata, platform_axi.wdata, sram_axi.wdata, flash_axi.wdata }),
    .M_AXI_WSTRB({ eth_axi.wstrb, platform_axi.wstrb, sram_axi.wstrb, flash_axi.wstrb }),
    .M_AXI_WVALID({ eth_axi.wvalid, platform_axi.wvalid, sram_axi.wvalid, flash_axi.wvalid }),
    .M_AXI_WREADY({ eth_axi.wready, platform_axi.wready, sram_axi.wready, flash_axi.wready }),

    .M_AXI_BRESP({ eth_axi.bresp, platform_axi.bresp, sram_axi.bresp, flash_axi.bresp }),
    .M_AXI_BVALID({ eth_axi.bvalid, platform_axi.bvalid, sram_axi.bvalid, flash_axi.bvalid }),
    .M_AXI_BREADY({ eth_axi.bready, platform_axi.bready, sram_axi.bready, flash_axi.bready }),

    .M_AXI_ARADDR({ eth_axi.araddr, platform_axi.araddr, sram_axi.araddr, flash_axi.araddr }),
    .M_AXI_ARPROT({ eth_axi.arprot, platform_axi.arprot, sram_axi.arprot, flash_axi.arprot }),
    .M_AXI_ARVALID({ eth_axi.arvalid, platform_axi.arvalid, sram_axi.arvalid, flash_axi.arvalid }),
    .M_AXI_ARREADY({ eth_axi.arready, platform_axi.arready, sram_axi.arready, flash_axi.arready }),

    .M_AXI_RDATA({ eth_axi.rdata, platform_axi.rdata, sram_axi.rdata, flash_axi.rdata }),
    .M_AXI_RRESP({ eth_axi.rresp, platform_axi.rresp, sram_axi.rresp, flash_axi.rresp }),
    .M_AXI_RVALID({ eth_axi.rvalid, platform_axi.rvalid, sram_axi.rvalid, flash_axi.rvalid }),
    .M_AXI_RREADY({ eth_axi.rready, platform_axi.rready, sram_axi.rready, flash_axi.rready })
);

axi4lite ifetch_axi();
axi4lite data_axi();
wire mtime_int;
wire eth_rx_interrupt;
core #(
    .RESET_PC(RESET_PC),
    .UNCACHEABLE_ADDR_MASK({3'b111, {(`ALEN-3){1'b0}}})
) core (
    .clk,
    .rst,

    .ifetch_port(ifetch_axi),
    .data_port(data_axi),

    .mtime_int,
    .platform_ints({{`PLATFORM_INTR_LEN-1{1'b0}}, eth_rx_interrupt}),

    .fetch_instr,
    .reg_pc,
    .reg_read_sel,
    .reg_read_data
);

axi4lite flash_axi();
assign flash_axi.aclk = clk;
assign flash_axi.aresetn = !rst;
axi4lite_flash #(.USE_SB_IO(0)) axi4lite_flash(
    .bus(flash_axi),
    .cs,
    .sclk,
    .capture_clk,
    .si,
    .so,
    .wp,
    .hold
);

axi4lite sram_axi();
assign sram_axi.aclk = clk;
assign sram_axi.aresetn = !rst;
axi4lite_sram #(
    .ADDR_MASK({4'b0000, {(`ALEN-4){1'b1}}}),
    .SIZE_KB(SRAM_SIZE_KB)
) axi4lite_sram (
    .bus(sram_axi)
);

axi4lite platform_axi();
assign platform_axi.aclk = clk;
assign platform_axi.aresetn = !rst;
axi4lite_platform #(
    .ADDR_MASK({3'b000, {(`ALEN-3){1'b1}}}),
    .NUM_OUTPUTS(GPIO_OUTPUTS)
) axi4lite_platform (
    .bus(platform_axi),
    .mtime_clk(clk),
    .mtime_int,
    .outputs(gpio_outputs)
);

// We only expose the ethernet MMIO registers, but the PHY itself is completely disconnected
wire       eth_rx_clk = '0;
wire [3:0] eth_rxd = '0;
wire       eth_rx_dv = '0;
wire       eth_rx_er = '0;
wire       eth_tx_clk = '0;
wire [3:0] eth_txd;
wire       eth_tx_en;
wire       eth_col = '0;
wire       eth_crs = '0;
wire       eth_reset_n;

axi4lite eth_axi();
assign eth_axi.aclk = clk;
assign eth_axi.aresetn = !rst;
axi4lite_ethernet #(
    .TARGET("GENERIC"),
    .ADDR_MASK({3'b000, {(`ALEN-3){1'b1}}})
) axi4lite_ethernet (
    .bus(eth_axi),
    .eth_rx_interrupt(eth_rx_interrupt),
    .phy_rx_clk(eth_rx_clk),
    .phy_rxd(eth_rxd),
    .phy_rx_dv(eth_rx_dv),
    .phy_rx_er(eth_rx_er),
    .phy_tx_clk(eth_tx_clk),
    .phy_txd(eth_txd),
    .phy_tx_en(eth_tx_en),
    .phy_col(eth_col),
    .phy_crs(eth_crs),
    .phy_reset_n(eth_reset_n)
);


endmodule