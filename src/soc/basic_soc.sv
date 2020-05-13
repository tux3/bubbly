`include "../core/params.svh"
`include "../axi/axi4lite.svh"

module basic_soc(
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
    output [`XLEN-1:0] reg_pc,
    input [4:0] reg_read_sel,
    output [`XLEN-1:0] reg_read_data
);

axilxbar #(
    .C_AXI_DATA_WIDTH(64),
    .C_AXI_ADDR_WIDTH(`ALEN),
    .NM(2),
    .NS(2)
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
    .M_AXI_AWADDR({ bram_axi.awaddr, flash_axi.awaddr }),
    .M_AXI_AWPROT({ bram_axi.awprot, flash_axi.awprot }),
    .M_AXI_AWVALID({ bram_axi.awvalid, flash_axi.awvalid }),
    .M_AXI_AWREADY({ bram_axi.awready, flash_axi.awready }),
    
    .M_AXI_WDATA({ bram_axi.wdata, flash_axi.wdata }),
    .M_AXI_WSTRB({ bram_axi.wstrb, flash_axi.wstrb }),
    .M_AXI_WVALID({ bram_axi.wvalid, flash_axi.wvalid }),
    .M_AXI_WREADY({ bram_axi.wready, flash_axi.wready }),
    
    .M_AXI_BRESP({ bram_axi.bresp, flash_axi.bresp }),
    .M_AXI_BVALID({ bram_axi.bvalid, flash_axi.bvalid }),
    .M_AXI_BREADY({ bram_axi.bready, flash_axi.bready }),
    
    .M_AXI_ARADDR({ bram_axi.araddr, flash_axi.araddr }),
    .M_AXI_ARPROT({ bram_axi.arprot, flash_axi.arprot }),
    .M_AXI_ARVALID({ bram_axi.arvalid, flash_axi.arvalid }),
    .M_AXI_ARREADY({ bram_axi.arready, flash_axi.arready }),
    
    .M_AXI_RDATA({ bram_axi.rdata, flash_axi.rdata }),
    .M_AXI_RRESP({ bram_axi.rresp, flash_axi.rresp }),
    .M_AXI_RVALID({ bram_axi.rvalid, flash_axi.rvalid }),
    .M_AXI_RREADY({ bram_axi.rready, flash_axi.rready })
);

axi4lite ifetch_axi();
axi4lite data_axi();
core core(
    .clk,
    .rst,

    .ifetch_port(ifetch_axi),
    .data_port(data_axi),

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

axi4lite bram_axi();
assign bram_axi.aclk = clk;
assign bram_axi.aresetn = !rst;
// TODO: Add a BRAM axi device
assign bram_axi.arready = '0;
assign bram_axi.rvalid = '0;
assign bram_axi.awready = '0;
assign bram_axi.wready = '0;
assign bram_axi.bvalid = '0;

endmodule