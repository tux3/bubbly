`include "../core/params.svh"
`include "../axi/axi4lite.svh"

module basic_soc#(
    parameter RESET_PC = `RESET_PC,
    parameter GPIO_OUTPUTS = 4
) (
    input clk,
    input rst,

    // ROM flash interface
    output cs,
    output sclk,
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
    .NS(3)
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
    .M_AXI_AWADDR({ gpio_axi.awaddr, sram_axi.awaddr, flash_axi.awaddr }),
    .M_AXI_AWPROT({ gpio_axi.awprot, sram_axi.awprot, flash_axi.awprot }),
    .M_AXI_AWVALID({ gpio_axi.awvalid, sram_axi.awvalid, flash_axi.awvalid }),
    .M_AXI_AWREADY({ gpio_axi.awready, sram_axi.awready, flash_axi.awready }),

    .M_AXI_WDATA({ gpio_axi.wdata, sram_axi.wdata, flash_axi.wdata }),
    .M_AXI_WSTRB({ gpio_axi.wstrb, sram_axi.wstrb, flash_axi.wstrb }),
    .M_AXI_WVALID({ gpio_axi.wvalid, sram_axi.wvalid, flash_axi.wvalid }),
    .M_AXI_WREADY({ gpio_axi.wready, sram_axi.wready, flash_axi.wready }),

    .M_AXI_BRESP({ gpio_axi.bresp, sram_axi.bresp, flash_axi.bresp }),
    .M_AXI_BVALID({ gpio_axi.bvalid, sram_axi.bvalid, flash_axi.bvalid }),
    .M_AXI_BREADY({ gpio_axi.bready, sram_axi.bready, flash_axi.bready }),

    .M_AXI_ARADDR({ gpio_axi.araddr, sram_axi.araddr, flash_axi.araddr }),
    .M_AXI_ARPROT({ gpio_axi.arprot, sram_axi.arprot, flash_axi.arprot }),
    .M_AXI_ARVALID({ gpio_axi.arvalid, sram_axi.arvalid, flash_axi.arvalid }),
    .M_AXI_ARREADY({ gpio_axi.arready, sram_axi.arready, flash_axi.arready }),

    .M_AXI_RDATA({ gpio_axi.rdata, sram_axi.rdata, flash_axi.rdata }),
    .M_AXI_RRESP({ gpio_axi.rresp, sram_axi.rresp, flash_axi.rresp }),
    .M_AXI_RVALID({ gpio_axi.rvalid, sram_axi.rvalid, flash_axi.rvalid }),
    .M_AXI_RREADY({ gpio_axi.rready, sram_axi.rready, flash_axi.rready })
);

axi4lite ifetch_axi();
axi4lite data_axi();
core #(.RESET_PC(RESET_PC)) core(
    .clk,
    .rst,

    .ifetch_port(ifetch_axi),
    .data_port(data_axi),

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
    .SIZE_KB(8)
) axi4lite_sram (
    .bus(sram_axi)
);

axi4lite gpio_axi();
assign gpio_axi.aclk = clk;
assign gpio_axi.aresetn = !rst;
axi4lite_gpio #(
    .ADDR_MASK({3'b000, {(`ALEN-3){1'b1}}}),
    .NUM_OUTPUTS(GPIO_OUTPUTS)
) axi4lite_gpio (
    .bus(gpio_axi),
    .outputs(gpio_outputs)
);

endmodule