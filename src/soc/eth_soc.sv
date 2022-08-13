`include "../core/params.svh"
`include "../axi/axi4lite.svh"

module eth_soc #(
    parameter RESET_PC = `RESET_PC,
    parameter GPIO_OUTPUTS = 4
) (
    input clk,
    input rst,

    // Interrupt lines
    input [3:0] platform_ints,

    // ROM flash interface
    output cs,
    output sclk,
    input capture_clk,
    inout si,
    inout so,
    inout wp,
    inout hold,

    // Ethernet
    input        eth_rx_clk,
    input  [3:0] eth_rxd,
    input        eth_rx_dv,
    input        eth_rx_er,
    input        eth_tx_clk,
    output [3:0] eth_txd,
    output       eth_tx_en,
    input        eth_col,
    input        eth_crs,
    output       eth_reset_n,

    input mtime_clk,
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
core #(
    .RESET_PC(RESET_PC),
    .UNCACHEABLE_ADDR_MASK({3'b111, {(`ALEN-3){1'b0}}})
) core (
    .clk,
    .rst,

    .ifetch_port(ifetch_axi),
    .data_port(data_axi),

    .mtime_int,
    .platform_ints(platform_ints),

    .fetch_instr(),
    .reg_pc(),
    .reg_read_sel(),
    .reg_read_data()
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

// Addr 0x18000000000
axi4lite sram_axi();
assign sram_axi.aclk = clk;
assign sram_axi.aresetn = !rst;
axi4lite_sram #(
    .ADDR_MASK({4'b0000, {(`ALEN-4){1'b1}}}),
    .SIZE_KB(32)
) axi4lite_sram (
    .bus(sram_axi)
);

// Addr 0x20000000000
axi4lite platform_axi();
assign platform_axi.aclk = clk;
assign platform_axi.aresetn = !rst;
axi4lite_platform #(
    .ADDR_MASK({3'b000, {(`ALEN-3){1'b1}}}),
    .NUM_OUTPUTS(GPIO_OUTPUTS)
) axi4lite_platform (
    .bus(platform_axi),
    .mtime_clk,
    .mtime_int,
    .outputs(gpio_outputs)
);

// Addr 0x30000000000
axi4lite eth_axi();
assign eth_axi.aclk = clk;
assign eth_axi.aresetn = !rst;
axi4lite_ethernet #(
    .ADDR_MASK({3'b000, {(`ALEN-3){1'b1}}})
) axi4lite_ethernet (
    .bus(eth_axi),
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
