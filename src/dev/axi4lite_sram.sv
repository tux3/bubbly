`include "../core/params.svh"
`include "../axi/axi4lite.svh"

module axi4lite_sram #(
    parameter SIZE_KB = 4,
    parameter ADDR_MASK = {`ALEN{1'b1}},
    parameter string MEM_INIT_FILE = ""
) (
    axi4lite.slave bus
);

// Note: We don't support misaligned read/writes. We could, but instead let's let the busmasters take care of it for all the devices.

localparam data_width = 64;
localparam mem_num_entries = (SIZE_KB * 1024) / (data_width/8);
localparam mem_addr_width = $clog2(SIZE_KB * 1024) - $clog2(data_width/8);
localparam read_after_write = 1;

generate
    if (`ALEN < mem_addr_width)
        $error("`ALEN too small for a SIZE_KB SRAM");
    if (data_width != 64)
        $error("Data width not fully parametrized. It must also match the AXI4 data width.");
endgenerate

logic [data_width-1:0] mem [mem_num_entries-1:0];

`ifndef SYNTHESIS
initial begin
    if (MEM_INIT_FILE != "") begin
        automatic int mem_init_bytes_read;
        automatic int init_fd = $fopen(MEM_INIT_FILE, "rb");  // Open in binary read mode
        if (init_fd == 0) begin
            $fatal("Failed to open axi4lite SRAM memory init file.");
        end
        mem_init_bytes_read = $fread(mem, init_fd);
        $fclose(init_fd);
    end else begin
        for (int i = 0; i<mem_num_entries; i = i+1)
            mem[i] = '0;
    end
end
`endif

wire clk = bus.aclk;
wire rst = !bus.aresetn;

reg read_pending;
reg [`ALEN-1:0] raddr_buf;
wire [`ALEN-1:0] bus_araddr_masked = bus.araddr & ADDR_MASK;
wire [`ALEN-1:0] raddr = ((bus.arvalid && bus.arready) ? bus_araddr_masked : raddr_buf);

wire [(`ALEN-$clog2(data_width/8))-1:0] mem_read_index = raddr[`ALEN-1:$clog2(data_width/8)];
wire [(`ALEN-$clog2(data_width/8))-1:0] mem_buf_read_index = raddr_buf[`ALEN-1:$clog2(data_width/8)];

reg rdata_available;
reg [data_width-1:0] rdata_buf;
reg [data_width-1:0] rdata_pending_buf;
logic [data_width-1:0] rdata;
wire invalid_read_index = mem_read_index >= mem_num_entries;
wire misaligned_read = |raddr[0 +: $clog2(data_width/8)];

assign bus.arready = !read_pending;

// Note: The bram output is registered, so this is comb
always_comb begin
    if (read_pending)
        bus.rdata = rdata_pending_buf;
    else if (rdata_available)
        bus.rdata = rdata;
    else
        bus.rdata = rdata_buf;
end

always_ff @(posedge clk) begin
    if (rst) begin
        rdata_available <= '0;
        raddr_buf <= 'x;
        rdata_buf <= 'x;
        rdata_pending_buf <= 'x;
    end else begin
        rdata_available <= bus.arready && bus.arvalid;
        if (bus.arvalid && bus.arready)
            raddr_buf <= bus_araddr_masked;

        if (bus.rvalid && !bus.rready && bus.arvalid && bus.arready)
            rdata_pending_buf <= rdata_available ? rdata : rdata_buf;

        if (rdata_available) begin
            if (read_pending) begin
                rdata_buf <= rdata;
            end else if (bus.rvalid && !bus.rready) begin
                rdata_buf <= rdata;
            end else begin
                rdata_buf <= rdata;
            end
        end
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        bus.rvalid <= '0;
        bus.rresp <= 'x;
    end else if (bus.rvalid && !bus.rready) begin
        // Keep read outputs stable
    end else if (read_pending || (bus.arready && bus.arvalid)) begin
        bus.rvalid <= '1;
        bus.rresp <= (invalid_read_index || misaligned_read) ? AXI4LITE_RESP_SLVERR : AXI4LITE_RESP_OKAY;
    end else begin
        bus.rvalid <= '0;
        bus.rresp <= 'x;
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        read_pending <= '0;
    end else if (bus.rvalid && !bus.rready) begin
        if (bus.arvalid && bus.arready) begin
            read_pending <= '1;
        end
    end else if (bus.rvalid && bus.rready) begin
        read_pending <= '0;
    end
end

logic awpending;
logic wpending;
wire awhandshaked = (bus.awvalid && bus.awready) || awpending;
wire whandshaked = (bus.wvalid && bus.wready) || wpending;

reg [(`ALEN-$clog2(data_width/8))-1:0] waddr_buf;
reg [data_width-1:0] wdata_buf;
reg [data_width/8-1:0] wstrb_buf;
wire [`ALEN-1:0] waddr = (awpending ? waddr_buf : bus.awaddr) & ADDR_MASK;
wire [data_width-1:0] wdata = wpending ? wdata_buf : bus.wdata;
wire [data_width/8-1:0] wstrb = wpending ? wstrb_buf : bus.wstrb;

wire [(`ALEN-$clog2(data_width/8))-1:0] mem_write_index = waddr[`ALEN-1:$clog2(data_width/8)];

wire invalid_write_index = mem_write_index >= mem_num_entries;
wire misaligned_write = |waddr[0 +: $clog2(data_width/8)];
wire write_error = invalid_write_index || misaligned_write;

wire write_enable = awhandshaked && whandshaked && !(awpending && wpending) && !write_error;
assign bus.awready = !awpending;
assign bus.wready = !wpending;

always_ff @(posedge clk) begin
    if (rst) begin
        awpending <= '0;
        wpending <= '0;
        waddr_buf <= 'x;
        wdata_buf <= 'x;
        wstrb_buf <= 'x;
    end else if (awhandshaked && whandshaked && !(awpending && wpending)) begin
        if (bus.bvalid && !bus.bready) begin
            awpending <= '1;
            wpending <= '1;
            waddr_buf <= bus.awaddr;
            wdata_buf <= bus.wdata;
            wstrb_buf <= bus.wstrb;
        end else begin
            awpending <= '0;
            wpending <= '0;
            waddr_buf <= 'x;
            wdata_buf <= 'x;
            wstrb_buf <= 'x;
        end
    end else begin
        if (bus.awvalid && bus.awready) begin
            awpending <= '1;
            waddr_buf <= bus.awaddr;
        end else if (bus.bvalid && bus.bready) begin
            awpending <= '0;
            waddr_buf <= 'x;
        end

        if (bus.wvalid && bus.wready) begin
            wdata_buf <= bus.wdata;
            wstrb_buf <= bus.wstrb;
            wpending <= '1;
        end else if (bus.bvalid && bus.bready) begin
            wpending <= '0;
            wdata_buf <= 'x;
            wstrb_buf <= 'x;
        end
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        bus.bvalid <= '0;
        bus.bresp <= 'x;
    end else if (bus.bvalid && !bus.bready) begin
        // Hold outputs stable
    end else if (awhandshaked && whandshaked) begin
        bus.bvalid <= '1;
        bus.bresp <= write_error ? AXI4LITE_RESP_SLVERR : AXI4LITE_RESP_OKAY;
    end else begin
        bus.bvalid <= '0;
        bus.bresp <= 'x;
    end
end

genvar i;
generate
    if (read_after_write) begin
        reg rw_conflict;
        reg [data_width-1:0] written_data;
        reg [data_width-1:0] rdata_reg;
        assign rdata = rw_conflict ? written_data : rdata_reg;
        
        always_ff @(posedge bus.aclk)
            rw_conflict <= write_enable && mem_read_index == mem_write_index;

        for (i=0; i<data_width/8; i=i+1) begin
            always_ff @(posedge bus.aclk)
                rdata_reg[i * 8 +: 8] <= mem[mem_read_index][(7-i) * 8 +: 8];
        
            always @(posedge bus.aclk) begin
                if (write_enable && wstrb[i]) begin
                    mem[mem_write_index][(7-i) * 8 +: 8] <= wdata[i * 8 +: 8];
                    written_data[i * 8 +: 8] <= wdata[i * 8 +: 8];
                end
            end
        end
    end else begin
        for (i=0; i<data_width/8; i=i+1) begin
            always_ff @(posedge bus.aclk)
                rdata[i * 8 +: 8] <= mem[mem_read_index][(7-i) * 8 +: 8];
            
            always @(posedge bus.aclk)
                if (write_enable && wstrb[i])
                    mem[mem_write_index][(7-i) * 8 +: 8] <= wdata[i * 8 +: 8];
        end
    end
endgenerate

`ifndef SYNTHESIS
initial assert (data_width == $bits(bus.rdata));

always @(posedge bus.aclk) begin
    assert property (@(posedge bus.aclk) bus.arready && bus.arvalid |=> rdata_available);
    assert property (@(posedge bus.aclk) rdata_available |-> bus.rvalid);
    assert property (@(posedge bus.aclk) write_enable |-> !$isunknown(waddr));
end
`endif

endmodule
