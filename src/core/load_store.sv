`include "params.svh"
`include "../axi/axi4lite.svh"

// There is no stall_next, we instead require users to wait for !stall_next before starting a load/store
// In other words, do not try to start load/stores in parallel.
// In exchange we can move buffers internally, users can forward to comb inputs directly since we never stall_prev
module load_store(
    input clk, rst,
	input prev_stalled,
    output logic stall_next,

    input [basic_cache_params::aligned_addr_size-1:0] addr,
    output logic access_fault,

    input do_load,
    output logic [`XLEN-1:0] load_data,

    input do_store,
    input [`XLEN-1:0] store_data,
    input [(`XLEN/8)-1:0] store_mask,

    axi4lite.master data_bus
);

reg [basic_cache_params::aligned_addr_size-1:0] addr_buf;
reg [`XLEN-1:0] store_data_buf;
reg [(`XLEN/8)-1:0] store_mask_buf;

generate
	if (basic_cache_params::data_size != 64)
		$error("dcache's data_size must be 64bit (required by load/store unit)");
endgenerate

always @(posedge clk) begin
    if (rst) begin
        addr_buf <= 'x;
        store_data_buf <= 'x;
        store_mask_buf <= 'x;
    end else if (!prev_stalled) begin
        addr_buf <= addr;
        store_data_buf <= store_data;
        store_mask_buf <= store_mask;
    end
end

logic dcache_write_enable;
wire [basic_cache_params::aligned_addr_size-1:0] dcache_waddr = addr_buf;
logic [basic_cache_params::data_size-1:0] dcache_wdata;
wire [basic_cache_params::aligned_addr_size-1:0] dcache_raddr = !prev_stalled ? addr : addr_buf;
wire [basic_cache_params::data_size-1:0] dcache_rdata;
wire dcache_lookup_valid;

basic_cache dcache(
	.clk,
	.rst,
	.write_enable(dcache_write_enable),
	.waddr(dcache_waddr),
	.wdata(dcache_wdata),
	.raddr(dcache_raddr),
	.rdata(dcache_rdata),
	.lookup_valid(dcache_lookup_valid)
);

enum bit[3:0] {
	STATE_IDLE,
    STATE_LOAD_CHECK_CACHE,
	STATE_LOAD_PENDING,
    STATE_STORE_CHECK_CACHE,
    STATE_STORE_PENDING
} state;

logic awpending;
logic wpending;
wire awhandshaked = (data_bus.awvalid && data_bus.awready) || awpending;
wire whandshaked = (data_bus.wvalid && data_bus.wready) || wpending;

integer mask_idx;
always_comb begin
    mask_idx = 'x;
    if (state == STATE_LOAD_PENDING) begin
        dcache_write_enable = data_bus.rvalid;
        dcache_wdata = data_bus.rdata;
    end else if (state == STATE_STORE_CHECK_CACHE) begin
        dcache_write_enable = dcache_lookup_valid;
        for (mask_idx=0; mask_idx<$size(dcache_wdata)/8; mask_idx+=1)
            dcache_wdata[mask_idx*8 +: 8] = store_mask_buf[mask_idx] ? dcache_rdata[mask_idx*8 +: 8] : store_data_buf[mask_idx*8 +: 8];
    end else begin
        dcache_write_enable = '0;
        dcache_wdata = 'x;
    end
end

always_comb begin
	if (rst) begin
        stall_next = '1;
		load_data = 'x;
		access_fault = 'x;
	end else begin
        stall_next = '1;
        access_fault = '0;
        load_data = 'x;

        unique case (state)
    	STATE_IDLE:
            stall_next = '1;
        STATE_LOAD_CHECK_CACHE: begin
            stall_next = !dcache_lookup_valid;
            load_data = dcache_rdata;
        end
    	STATE_LOAD_PENDING: begin
            stall_next = !data_bus.rvalid;
            access_fault = data_bus.rresp != AXI4LITE_RESP_OKAY;
            load_data = data_bus.rdata;
    	end
        STATE_STORE_CHECK_CACHE:
            stall_next = !(awhandshaked && whandshaked);
        STATE_STORE_PENDING:
            stall_next = !(awhandshaked && whandshaked);
    	endcase
    end
end

always @(posedge clk) begin
	if (rst) begin
		state <= STATE_IDLE;
	end else unique case (state)
	STATE_IDLE: begin
        if (!prev_stalled && do_load) begin
            state <= STATE_LOAD_CHECK_CACHE;
        end else if (!prev_stalled && do_store) begin
            state <= STATE_STORE_CHECK_CACHE;
        end
	end
    STATE_LOAD_CHECK_CACHE: begin
        if (!dcache_lookup_valid) begin
            state <= STATE_LOAD_PENDING;
        end else if (prev_stalled) begin
            state <= STATE_IDLE;
        end else if (do_load) begin
            // Stay for the next cache check
        end else if (do_store) begin
            state <= STATE_STORE_CHECK_CACHE;
        end
    end
	STATE_LOAD_PENDING: begin
        if (data_bus.rvalid) begin
            if (prev_stalled) begin
                state <= STATE_IDLE;
            end else if (do_load) begin
                state <= STATE_LOAD_CHECK_CACHE;
            end else if (do_store) begin
                state <= STATE_STORE_CHECK_CACHE;
            end
        end
	end
    STATE_STORE_CHECK_CACHE: begin
        if (awhandshaked && whandshaked) begin
            if (prev_stalled) begin
                state <= STATE_IDLE;
            end else if (do_load) begin
                state <= STATE_LOAD_CHECK_CACHE;
            end else if (do_store) begin
                // Stay for the next cache check
            end else begin
                state <= STATE_STORE_PENDING;
            end
        end
    end
    STATE_STORE_PENDING: begin
        if (awhandshaked && whandshaked) begin
            if (prev_stalled) begin
                state <= STATE_IDLE;
            end else if (do_load) begin
                state <= STATE_LOAD_CHECK_CACHE;
            end else if (do_store) begin
                state <= STATE_STORE_CHECK_CACHE;
            end
        end
    end
	endcase
end

always @(posedge clk) begin
	if (rst) begin
        data_bus.awvalid <= '0;
        data_bus.wvalid <= '0;
    end else if (!prev_stalled && do_store) begin
        data_bus.awvalid <= '1;
        data_bus.wvalid <= '1;
    end else begin
        if (data_bus.awready)
            data_bus.awvalid <= '0;
        if (data_bus.wready)
            data_bus.wvalid <= '0;
    end
end

always @(posedge clk) begin
	if (rst) begin
        awpending <= '0;
        wpending <= '0;
    end else if (awhandshaked && whandshaked) begin
        awpending <= '0;
        wpending <= '0;
    end else begin
        if (data_bus.awvalid && data_bus.awready)
            awpending <= '1;
        if (data_bus.wvalid && data_bus.wready)
            wpending <= '1;
    end
end

assign data_bus.aclk = clk;
assign data_bus.aresetn = !rst;

assign data_bus.arvalid = state == STATE_LOAD_CHECK_CACHE && !dcache_lookup_valid;
assign data_bus.araddr = {addr_buf, 3'b000};
assign data_bus.arprot = 'b000;

assign data_bus.rready = state == STATE_LOAD_PENDING;

assign data_bus.awaddr = {addr_buf, 3'b000};
assign data_bus.awprot = 'b000;

assign data_bus.wdata = store_data_buf;
assign data_bus.wstrb = store_mask_buf;
assign data_bus.bready = 1;

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (!prev_stalled |-> do_load ^ do_store);
    assert property (!prev_stalled |-> !$isunknown(addr));
    assert property (!prev_stalled && do_store |-> !$isunknown(store_data));
    assert property (!prev_stalled && do_store |-> !$isunknown(store_mask));
    assert property (data_bus.awvalid |-> !$isunknown(data_bus.awaddr));
    assert property (data_bus.arvalid |-> !$isunknown(data_bus.araddr));
    assert property (data_bus.bvalid |-> data_bus.bresp == AXI4LITE_RESP_OKAY);
end
`endif

endmodule
