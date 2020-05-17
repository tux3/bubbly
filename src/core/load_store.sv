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

assign data_bus.aclk = clk;
assign data_bus.aresetn = !rst;

assign data_bus.arvalid = state == STATE_CHECK_CACHE_LOAD && !dcache_lookup_valid;
assign data_bus.araddr = {addr_buf, 3'b000};
assign data_bus.arprot = 'b000;

assign data_bus.rready = state == STATE_LOAD_PENDING;

assign data_bus.awaddr = 'x;
assign data_bus.awprot = 'x;
assign data_bus.awvalid = 0;

assign data_bus.wdata = 'x;
assign data_bus.wstrb = 'x;
assign data_bus.wvalid = 0;
assign data_bus.bready = 0;

reg [basic_cache_params::aligned_addr_size-1:0] addr_buf;

generate
	if (basic_cache_params::data_size != 64)
		$error("dcache's data_size must be 64bit (required by load/store unit)");
endgenerate

always @(posedge clk) begin
    if (rst)
        addr_buf <= 'x;
    else if (!prev_stalled)
        addr_buf <= addr;
end

logic dcache_write_enable;
wire [basic_cache_params::aligned_addr_size-1:0] dcache_waddr = addr_buf;
logic [basic_cache_params::data_size-1:0] dcache_wdata;
wire [basic_cache_params::aligned_addr_size-1:0] dcache_raddr = !prev_stalled ? addr : addr_buf;
wire [basic_cache_params::data_size-1:0] dcache_rdata;
wire dcache_lookup_valid;

basic_cache dcache(
	.clk,
	.write_enable(dcache_write_enable),
	.waddr(dcache_waddr),
	.wdata(dcache_wdata),
	.raddr(dcache_raddr),
	.rdata(dcache_rdata),
	.lookup_valid(dcache_lookup_valid)
);

always_comb begin
    if (state == STATE_LOAD_PENDING) begin
        dcache_write_enable = data_bus.rvalid;
        dcache_wdata = data_bus.rdata;
    end else begin
        dcache_write_enable = '0;
        dcache_wdata = 'x;
    end
end

enum bit[3:0] { 
	STATE_IDLE,
    STATE_CHECK_CACHE_LOAD,
	STATE_LOAD_PENDING
} state;

always_comb begin
	if (rst) begin
        stall_next = '1;
		load_data = 'x;
		access_fault = 'x;
	end else begin
        stall_next = '1;
        load_data = 'x;
        access_fault = 'x;
    
        unique case (state)
    	STATE_IDLE: begin
            stall_next = '1;
    	end
        STATE_CHECK_CACHE_LOAD: begin
            stall_next = !dcache_lookup_valid;
            access_fault = '0;
            load_data = dcache_rdata;
        end
    	STATE_LOAD_PENDING: begin
            stall_next = !data_bus.rvalid;
            access_fault = data_bus.rresp != AXI4LITE_RESP_OKAY;
            load_data = data_bus.rdata;
    	end
    	endcase
    end
end

always @(posedge clk) begin
	if (rst) begin
		state <= STATE_IDLE;
	end else unique case (state)
	STATE_IDLE: begin
        if (!prev_stalled && do_load) begin
            state <= STATE_CHECK_CACHE_LOAD;            
        end
	end
    STATE_CHECK_CACHE_LOAD: begin
        if (!dcache_lookup_valid) begin
            state <= STATE_LOAD_PENDING;
        end else if (prev_stalled) begin
            state <= STATE_IDLE;
        end else if (do_load) begin
            // Stay for the next cache check
        end else begin
            `ifndef SYNTHESIS
            $error("Unimplemented store-after-load-cache-hit state");
            `endif
        end
    end
	STATE_LOAD_PENDING: begin
        if (data_bus.rvalid) begin
            if (prev_stalled) begin
                state <= STATE_IDLE;
            end else if (do_load) begin
                state <= STATE_CHECK_CACHE_LOAD;
            end else begin
                `ifndef SYNTHESIS
                $error("Unimplemented store-after-load-from-mem state");
                `endif
            end
            
        end
	end
	endcase
end

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (!prev_stalled |-> do_load ^ do_store);
    assert property (!prev_stalled |-> !$isunknown(addr));
    assert property (!prev_stalled && do_store |-> !$isunknown(store_data));
    assert property (!prev_stalled && do_store |-> !$isunknown(store_mask));
end
`endif

endmodule
