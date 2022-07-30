`include "../core/params.svh"
`include "../axi/axi4lite.svh"

module axi4lite_sram #(
    parameter SIZE_KB = 4,
    parameter ADDR_MASK = {`ALEN{1'b1}}
) (
    axi4lite.slave bus
);

// Note: We don't support misaligned read/writes. We could, but instead let's let the busmasters take care of it for all the devices.

// Each BRAM block is 512B and 8-bit wide (on iCE40), we need 64bit wide ports
localparam data_width = 64;
localparam bram_block_size_bits = 4096; // iCE40 BRAM
localparam bram_block_data_width = 8;
localparam bram_block_addr_width = $clog2(bram_block_size_bits / bram_block_data_width);
localparam bram_addr_width = bram_block_addr_width;
localparam per_bram_blocks = data_width / bram_block_data_width;
localparam per_bram_bits = per_bram_blocks * bram_block_size_bits;
localparam per_bram_full_addr_width = $clog2(per_bram_bits / 8);
localparam total_bram_count = SIZE_KB*1024*8 / per_bram_bits;

generate
	if ((SIZE_KB * 1024 * 8) % per_bram_bits != 0)
		$error("SRAM size must be a multiple of per_bram_bits");
    if (`ALEN < per_bram_full_addr_width + $clog2(total_bram_count))
        $error("`ALEN too small for a SIZE_KB SRAM");
    if (bram_addr_width != per_bram_full_addr_width-$clog2(data_width/8))
        $error("Inconsistent BRAM addr width");
    if (bram_block_data_width != 8)
        $error("AXI4 write strobes (per-byte) won't work with BRAM block size != 8");
endgenerate

wire [data_width-1:0] bram_rdata [total_bram_count-1:0];

wire clk = bus.aclk;
wire rst = !bus.aresetn;

reg read_pending;
reg [`ALEN-1:0] raddr_buf;
wire [`ALEN-1:0] bus_araddr_masked = bus.araddr & ADDR_MASK;
wire [`ALEN-1:0] raddr = ((bus.arvalid && bus.arready) ? bus_araddr_masked : raddr_buf);

wire [(`ALEN-per_bram_full_addr_width)-1:0] bram_read_index = raddr[`ALEN-1:per_bram_full_addr_width];
wire [(`ALEN-per_bram_full_addr_width)-1:0] bram_buf_read_index = raddr_buf[`ALEN-1:per_bram_full_addr_width];
wire [bram_addr_width-1:0] bram_read_addr = bus_araddr_masked[per_bram_full_addr_width-1:$clog2(data_width/8)];

reg rdata_available;
reg [data_width-1:0] rdata_buf;
reg [data_width-1:0] rdata_pending_buf;
wire [data_width-1:0] rdata = bram_rdata[bram_buf_read_index];
wire invalid_read_index = bram_read_index >= total_bram_count;
wire misaligned_read = |raddr[0 +: $clog2(data_width/8)];

assign bus.arready = !read_pending;

// Note: The BRAM output is registered, so this is comb
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

reg [`ALEN-1:0] waddr_buf;
reg [data_width-1:0] wdata_buf;
reg [data_width/8-1:0] wstrb_buf;
wire [`ALEN-1:0] waddr = (awpending ? waddr_buf : bus.awaddr) & ADDR_MASK;
wire [data_width-1:0] wdata = wpending ? wdata_buf : bus.wdata;
wire [data_width/8-1:0] wstrb = wpending ? wstrb_buf : bus.wstrb;

wire [(`ALEN-per_bram_full_addr_width)-1:0] bram_write_index = waddr[`ALEN-1:per_bram_full_addr_width];
wire [bram_addr_width-1:0] bram_write_addr = waddr[per_bram_full_addr_width-1:$clog2(data_width/8)];

wire invalid_write_index = bram_write_index >= total_bram_count;
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
generate for (i=0; i<total_bram_count; i=i+1) begin
    bram #(
        .read_after_write(1),
        .blocks(per_bram_blocks),
        .block_addr_width(bram_block_addr_width),
        .block_data_width(bram_block_data_width)
    ) bram_slice (
        .clk(bus.aclk),
    	.write_mask(wstrb & {per_bram_blocks{write_enable && bram_write_index == i}}),
        .waddr(bram_write_addr),
        .raddr(bram_read_addr),
        .wdata(wdata),
        .rdata(bram_rdata[i])
    );
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
