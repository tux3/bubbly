`include "../core/params.svh"

interface axi4lite #(ADDR_WIDTH = `ALEN, DATA_WIDTH = 64)();
    // Control
    logic aclk;
    logic aresetn;

    // Adress Read channel
    logic [ADDR_WIDTH-1:0] araddr;
    logic [2:0] arprot; // Usually 000
    logic arvalid;
    logic arready;

    // Read data channel
    logic [DATA_WIDTH-1:0] rdata;
    logic [1:0] rresp;
    logic rvalid;
    logic rready;

    // Adress Write channel
    logic [ADDR_WIDTH-1:0] awaddr;
    logic [2:0] awprot; // Usually 000
    logic awvalid;
    logic awready;

    // Write data channel
    logic [DATA_WIDTH-1:0] wdata;
    logic [DATA_WIDTH/8-1:0] wstrb;
    logic wvalid;
    logic wready;

    // Write response channel
    logic [1:0] bresp;
    logic bvalid;
    logic bready;

    modport master(
        output aclk,
        output aresetn,

        output araddr,
        output arprot,
        output arvalid,
        input arready,

        input rdata,
        input rresp,
        input rvalid,
        output rready,

        output awaddr,
        output awprot,
        output awvalid,
        input awready,

        output wdata,
        output wstrb,
        output wvalid,
        input wready,

        input bresp,
        input bvalid,
        output bready
    );

    modport slave(
        input aclk,
        input aresetn,

        input araddr,
        input arprot,
        input arvalid,
        output arready,

        output rdata,
        output rresp,
        output rvalid,
        input rready,

        input awaddr,
        input awprot,
        input awvalid,
        output awready,

        input wdata,
        input wstrb,
        input wvalid,
        output wready,

        output bresp,
        output bvalid,
        input bready
    );

endinterface
