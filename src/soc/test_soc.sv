`include "../core/params.svh"
`include "../axi/axi4lite.svh"

module test_soc#(
    parameter RESET_PC = `RESET_PC,
    parameter GPIO_OUTPUTS = 4,
    parameter SRAM_SIZE_KB = 8,
    parameter SRAM_INIT_FILE = ""
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
    .M_AXI_AWADDR({ tohost_axi.awaddr, platform_axi.awaddr, sram_axi.awaddr }),
    .M_AXI_AWPROT({ tohost_axi.awprot, platform_axi.awprot, sram_axi.awprot }),
    .M_AXI_AWVALID({ tohost_axi.awvalid, platform_axi.awvalid, sram_axi.awvalid }),
    .M_AXI_AWREADY({ tohost_axi.awready, platform_axi.awready, sram_axi.awready }),

    .M_AXI_WDATA({ tohost_axi.wdata, platform_axi.wdata, sram_axi.wdata }),
    .M_AXI_WSTRB({ tohost_axi.wstrb, platform_axi.wstrb, sram_axi.wstrb }),
    .M_AXI_WVALID({ tohost_axi.wvalid, platform_axi.wvalid, sram_axi.wvalid }),
    .M_AXI_WREADY({ tohost_axi.wready, platform_axi.wready, sram_axi.wready }),

    .M_AXI_BRESP({ tohost_axi.bresp, platform_axi.bresp, sram_axi.bresp }),
    .M_AXI_BVALID({ tohost_axi.bvalid, platform_axi.bvalid, sram_axi.bvalid }),
    .M_AXI_BREADY({ tohost_axi.bready, platform_axi.bready, sram_axi.bready }),

    .M_AXI_ARADDR({ tohost_axi.araddr, platform_axi.araddr, sram_axi.araddr }),
    .M_AXI_ARPROT({ tohost_axi.arprot, platform_axi.arprot, sram_axi.arprot }),
    .M_AXI_ARVALID({ tohost_axi.arvalid, platform_axi.arvalid, sram_axi.arvalid }),
    .M_AXI_ARREADY({ tohost_axi.arready, platform_axi.arready, sram_axi.arready }),

    .M_AXI_RDATA({ tohost_axi.rdata, platform_axi.rdata, sram_axi.rdata }),
    .M_AXI_RRESP({ tohost_axi.rresp, platform_axi.rresp, sram_axi.rresp }),
    .M_AXI_RVALID({ tohost_axi.rvalid, platform_axi.rvalid, sram_axi.rvalid }),
    .M_AXI_RREADY({ tohost_axi.rready, platform_axi.rready, sram_axi.rready })
);

axi4lite ifetch_axi();
axi4lite data_axi();
wire mtime_int;
core #(
    .RESET_PC(RESET_PC),
    .UNCACHEABLE_ADDR_MASK({4'b1111, {(`ALEN-4){1'b0}}})
) core (
    .clk,
    .rst,

    .ifetch_port(ifetch_axi),
    .data_port(data_axi),

    .mtime_int,
    .platform_ints({`PLATFORM_INTR_LEN{1'b0}}),

    .fetch_instr,
    .reg_pc,
    .reg_read_sel,
    .reg_read_data
);

axi4lite sram_axi();
assign sram_axi.aclk = clk;
assign sram_axi.aresetn = !rst;
axi4lite_sram #(
    .ADDR_MASK({4'b0000, {(`ALEN-4){1'b1}}}),
    .SIZE_KB(SRAM_SIZE_KB),
    .MEM_INIT_FILE(SRAM_INIT_FILE)
) axi4lite_sram (
    .bus(sram_axi)
);

axi4lite platform_axi();
assign platform_axi.aclk = clk;
assign platform_axi.aresetn = !rst;
axi4lite_platform #(
    .ADDR_MASK({4'b0000, {(`ALEN-4){1'b1}}}),
    .NUM_OUTPUTS(GPIO_OUTPUTS)
) axi4lite_platform (
    .bus(platform_axi),
    .mtime_clk(clk),
    .mtime_int,
    .outputs(gpio_outputs)
);

axi4lite tohost_axi();
assign tohost_axi.aclk = clk;
assign tohost_axi.aresetn = !rst;
axi4lite_tohost #(
    .ADDR_MASK({3'b000, {(`ALEN-3){1'b1}}})
) axi4lite_tohost (
    .bus(tohost_axi)
);

endmodule
