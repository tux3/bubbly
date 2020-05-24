timeunit 1ns;
timeprecision 100ps;

`include "../../axi/axi4lite.svh"

module axi4lite_sram_tb;

    bit clk = 1;
    bit rst = 0;

    localparam data_width = 64;
    localparam strb_width = data_width/8;
    localparam size_kB = 8;
    localparam size_bytes = size_kB*1024;
    localparam size_bits = size_bytes*8;
    localparam addr_bits = $clog2(size_bytes);
    localparam bus_addr_bits = addr_bits+1; // Lets us test out-of-bound read errors

    axi4lite #(.ADDR_WIDTH(bus_addr_bits), .DATA_WIDTH(data_width)) bus();
    axi4lite_sram #(.SIZE_KB(size_kB)) axi4lite_sram(
        .bus
    );

    assign bus.aclk = clk;
    assign bus.aresetn = !rst;

    bit [size_bits-1:0] shadow_buf;

    initial assert(std::randomize(shadow_buf) == 1);

    initial begin
        #0 rst = 1;
        #3 rst = 0;
    end

    initial begin
        forever
            #0.5 clk = !clk;
    end

    // Reset master side of bus to idle values
    task master_reset_to_idle();
        // Resetting the master side while a reply's pending is a bug
        assert(bus.rvalid == 0);
        assert(bus.bvalid == 0);

        bus.araddr = '0;
        bus.arprot = 'b000;
        bus.arvalid = 0;
        bus.rready = 0;

        bus.awaddr = '0;
        bus.awprot = 'b000;
        bus.awvalid = 0;

        bus.wdata = '0;
        bus.wstrb = 'b1111_1111;
        bus.wvalid = 0;
        bus.bready = 0;
    endtask

    task automatic simple_write_and_read_back(input [addr_bits-1:0] addr, input [data_width-1:0] data, input [strb_width-1:0] strb);
        bit [data_width-1:0] new_data;

        bus.bready <= '1;
        bus.awaddr <= addr;
        bus.awvalid <= '1;
        bus.wdata <= data;
        bus.wstrb <= strb;
        bus.wvalid <= '1;

        fork
            forever @(posedge clk) begin
                if (bus.awready) begin
                    bus.awvalid <= '0;
                    bus.awaddr <= 'x;
                    break;
                end
            end

            forever @(posedge clk) begin
                if (bus.wready) begin
                    bus.wvalid <= '0;
                    bus.wdata <= 'x;
                    bus.wstrb <= {strb_width{1'b1}};
                    break;
                end
            end

            forever @(posedge clk) begin
                if ((bus.awready || !bus.awvalid) && (bus.wready || !bus.wvalid)) begin
                    bus.araddr <= addr;
                    bus.arvalid <= '1;
                    bus.rready <= '1;
                    break;
                end
            end
        join

        fork
            // Once the write is handshaked, we consider it done before the start of next cycle (so let's negedge it)
            begin
                @(negedge clk) begin
                    for (int i=0; i<strb_width; i+=1) begin
                        new_data[i*8 +: 8] = strb[i] ? data[i*8 +: 8] : shadow_buf[(addr+i)*8 +: 8];
                    end
                    shadow_buf[addr*8 +: data_width] = new_data;
                end
                @(posedge clk);
            end

            begin
                while (!bus.bvalid)
                    @(posedge clk);
                bus.bready <= '0;
                assert(bus.bresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected AXI4LITE_RESP_OKAY write, but got %h", $time, bus.bresp);
            end

            forever @(posedge clk) begin
                if (bus.arready) begin
                    bus.arvalid <= '0;
                    bus.araddr <= 'x;
                    break;
                end
            end
        join

        while (!bus.rvalid)
            @(posedge clk);
        bus.rready <= '0;
        assert(bus.rresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected AXI4LITE_RESP_OKAY read, but got %h", $time, bus.rresp);
        assert(bus.rdata == new_data) else $error("[%t] Expected %h data after readback at %h, but got %h", $time, new_data, addr, bus.rdata);
    endtask

    task automatic fill_and_readback_sram();
        for (int addr = 0; addr <= size_bytes-8; addr += 8) begin
            simple_write_and_read_back(.addr, .data(shadow_buf[addr*8 +: data_width]), .strb({strb_width{1'b1}}));
        end
    endtask

    task automatic simple_read_expect_resp(input [1:0] resp, input [bus_addr_bits-1:0] addr);
        @(posedge clk) begin
            bus.araddr <= addr;
            bus.arvalid <= '1;
        end

        forever @(posedge clk) begin
            if (bus.arready) begin
                bus.rready <= '1;
                bus.arvalid <= '0;
                bus.araddr <= 'x;
                break;
            end
        end

        while (!(bus.rvalid && bus.rready))
            @(posedge clk);
        bus.rready <= '0;
        assert(bus.rresp == resp) else $error("[%t] Expected rresp %h for read at %h, but got %h", $time, resp, addr, bus.rresp);
    endtask

    task automatic simple_write_expect_resp(input [1:0] resp, input [bus_addr_bits-1:0] addr);
        @(posedge clk) begin
            bus.awaddr <= addr;
            bus.awvalid <= '1;
            bus.wdata <= addr; // Whatever, we don't care about the shadow buf yet
            bus.wvalid <= '1;
            bus.bready <= '1;
        end

        @(posedge clk);

        fork
            begin
                while (!bus.awready)
                    @(posedge clk);
                bus.awvalid <= '0;
                bus.awaddr <= 'x;
            end

            begin
                while (!bus.wready)
                    @(posedge clk);
                bus.wvalid <= '0;
                bus.wdata <= 'x;
            end
        join

        while (!(bus.bvalid && bus.bready))
            @(posedge clk);
        bus.bready <= '0;
        assert(bus.bresp == resp) else $error("[%t] Expected bresp %h for write at %h, but got %h", $time, resp, addr, bus.bresp);
    endtask

    task automatic test_errors();
        simple_read_expect_resp(.resp(AXI4LITE_RESP_OKAY), .addr('h0)); // Aligned read
        simple_read_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr('h1)); // Misaligned read
        simple_read_expect_resp(.resp(AXI4LITE_RESP_OKAY), .addr(size_bytes-(data_width/8))); // Read last line
        simple_read_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr(size_bytes-1)); // Misaligned in-bounds read
        simple_read_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr(size_bytes)); // Out of bounds read
        simple_read_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr(size_bytes+1)); // Misaligned out of bounds read
        simple_read_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr(size_bytes+(data_width/8))); // Out of bounds read

        simple_write_expect_resp(.resp(AXI4LITE_RESP_OKAY), .addr('h0)); // Aligned
        simple_write_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr('h1)); // Misaligned
        simple_write_expect_resp(.resp(AXI4LITE_RESP_OKAY), .addr(size_bytes-(data_width/8))); // Last line
        simple_write_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr(size_bytes-1)); // Misaligned in-bounds
        simple_write_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr(size_bytes)); // Out of bounds
        simple_write_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr(size_bytes+1)); // Misaligned out of bounds
        simple_write_expect_resp(.resp(AXI4LITE_RESP_SLVERR), .addr(size_bytes+(data_width/8))); // Out of bounds
    endtask

    task automatic write_strobe_and_readback(input int iterations);
        localparam data_width_bytes = data_width/8;
        localparam data_width_addr_bits = $clog2(data_width_bytes);
        bit [data_width-1:0] data_random;
        bit [data_width/8-1:0] strb_random;
        bit [addr_bits-data_width_addr_bits-1:0] addr_random;
        bit [addr_bits-1:0] addr;

        for (int i=0; i<iterations; i += 1) begin
            assert(std::randomize(data_random));
            assert(std::randomize(strb_random));
            assert(std::randomize(addr_random));
            addr = {addr_random, {data_width_addr_bits{1'b0}}};

            simple_write_and_read_back(.addr, .data(data_random), .strb(strb_random));
        end
    endtask

    // This function does NOT touch bready, callers must take care of it
    task automatic async_write_no_bready(input [addr_bits-1:0] addr, input [data_width-1:0] data);
        start_async_write_no_bready(.addr, .data);

        forever @(posedge clk) begin
            if (bus.bvalid && bus.bready) begin
                assert(bus.bresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected AXI4LITE_RESP_OKAY write, but got %h", $time, bus.bresp);
                break;
            end
        end
    endtask

    // This function does NOT touch bready, callers must take care of it
    task automatic start_async_write_no_bready(input [addr_bits-1:0] addr, input [data_width-1:0] data);
        bus.awaddr <= addr;
        bus.awvalid <= '1;
        bus.wdata <= data;
        bus.wvalid <= '1;

        @(posedge clk);

        fork
            begin
                while (!bus.awready)
                    @(posedge clk);
                bus.awvalid <= '0;
                bus.awaddr <= 'x;
            end

            begin
                while (!bus.wready)
                    @(posedge clk);
                bus.wvalid <= '0;
                bus.wdata <= 'x;
            end
        join

        // NOTE: We assume that as soon as we get the {a,}w{valid,ready} handshakes the write is done, though AXI only guarantees the write is done when we get bvalid
        shadow_buf[addr*8 +: 64] = data;
    endtask

    // This function does NOT touch rready, callers must take care of it
    task automatic async_read_no_rready(input [addr_bits-1:0] addr);
        bit [data_width-1:0] expected_data;

        start_async_read_no_rready(.addr);

        expected_data = shadow_buf[addr*8 +: 64];

        while (!(bus.rvalid && bus.rready))
            @(posedge clk);
        assert(bus.rresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected AXI4LITE_RESP_OKAY read, but got %h", $time, bus.rresp);
        assert(bus.rdata == expected_data) else $error("[%t] Expected %h at %h, but got %h", $time, expected_data, addr, bus.rdata);
    endtask

    // This function does NOT touch rready, callers must take care of it
    task automatic start_async_read_no_rready(input [addr_bits-1:0] addr);
        bus.araddr <= addr;
        bus.arvalid <= '1;

        forever @(posedge clk) begin
            if (bus.arready) begin
                bus.arvalid <= '0;
                bus.araddr <= 'x;
                break;
            end
        end
    endtask

    task automatic random_rw_first_64_byte(input int iterations);
        localparam data_width_bytes = data_width/8;
        localparam data_width_addr_bits = $clog2(data_width_bytes);
        localparam addr_random_bits = $clog2(64/data_width_bytes);
        bit reads_done = '0;
        bit writes_done = '0;
        bit rready_rand;
        bit bready_rand;

        bus.bready = '0;
        bus.rready = '0;

        fork
            begin
                for (int i=0; i<iterations; i += 1) begin
                    bit [data_width-1:0] data_random;
                    bit [addr_random_bits-1:0] addr_random;
                    bit [data_width_addr_bits+addr_random_bits-1:0] waddr;
                    assert(std::randomize(data_random));
                    assert(std::randomize(addr_random));
                    waddr = {addr_random, {data_width_addr_bits{1'b0}}};

                    async_write_no_bready(.addr(waddr), .data(data_random));
                end
                writes_done = '1;
            end

            while (!writes_done) begin
                @(posedge(clk)) begin
                    assert(std::randomize(bready_rand));
                    bus.bready <= bready_rand;
                end
            end

            begin
                for (int i=0; i<iterations; i += 1) begin
                    bit [addr_random_bits-1:0] addr_random;
                    bit [data_width_addr_bits+addr_random_bits-1:0] raddr;
                    assert(std::randomize(addr_random));
                    raddr = {addr_random, {data_width_addr_bits{1'b0}}};

                    async_read_no_rready(.addr(raddr));
                end
                reads_done = '1;
            end

            while (!reads_done) begin
                @(posedge(clk)) begin
                    assert(std::randomize(rready_rand));
                    bus.rready <= rready_rand;
                end
            end
        join

        @(posedge clk) begin
            assert(!bus.rvalid);
            assert(!bus.bvalid);
            bus.bready <= '0;
            bus.rready <= '0;
        end
    endtask

    task automatic random_rw_async(input int iterations);
        localparam data_width_bytes = data_width/8;
        localparam data_width_addr_bits = $clog2(data_width_bytes);
        bit reads_done = '0;
        bit writes_done = '0;
        bit rready_rand;
        bit bready_rand;

        bit [addr_bits-1:0] expected_read_addrs[$];
        bit [data_width-1:0] expected_read_values[$];

        bus.bready = '0;
        bus.rready = '0;

        fork
            // Writes
            for (int i=0; i<iterations; i += 1) begin
                bit [data_width-1:0] data_random;
                bit [addr_bits-data_width_addr_bits-1:0] addr_random;
                bit [addr_bits-1:0] waddr;
                assert(std::randomize(data_random));
                assert(std::randomize(addr_random));
                waddr = {addr_random, {data_width_addr_bits{1'b0}}};

                start_async_write_no_bready(.addr(waddr), .data(data_random));
            end

            begin
                for (int i=0; i<iterations; i += 1) begin
                    forever @(posedge clk) begin
                        if (bus.bvalid && bus.bready) begin
                            assert(bus.bresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected AXI4LITE_RESP_OKAY for write %d, but got %h", $time, i, bus.bresp);
                            break;
                        end
                    end
                end
                writes_done = '1;
            end

            while (!writes_done) begin
                @(posedge(clk)) begin
                    assert(std::randomize(bready_rand));
                    bus.bready <= bready_rand;
                end
            end

            // Reads
            for (int i=0; i<iterations; i += 1) begin
                bit [addr_bits-data_width_addr_bits-1:0] addr_random;
                bit [addr_bits-1:0] raddr;
                assert(std::randomize(addr_random));
                raddr = {addr_random, {data_width_addr_bits{1'b0}}};

                start_async_read_no_rready(.addr(raddr));

                expected_read_addrs.push_back(raddr);
                expected_read_values.push_back(shadow_buf[raddr*8 +: 64]);
            end

            begin
                for (int i=0; i<iterations; i += 1) begin
                    forever @(posedge clk) begin
                        if (bus.rvalid && bus.rready) begin
                            bit [addr_bits-1:0] expected_addr = expected_read_addrs.pop_front();
                            bit [data_width-1:0] expected_data = expected_read_values.pop_front();
                            assert(bus.rresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected AXI4LITE_RESP_OKAY for read %d, but got %h", $time, i, bus.rresp);
                            assert(bus.rdata == expected_data) else $error("[%t] Expected %h at %h, but got %h", $time, expected_data, expected_addr, bus.rdata);
                            break;
                        end
                    end
                end
                reads_done = '1;
            end

            while (!reads_done) begin
                @(posedge(clk)) begin
                    assert(std::randomize(rready_rand));
                    bus.rready <= rready_rand;
                end
            end
        join

        bus.bready = '0;
        bus.rready = '0;
    endtask

    initial begin
        @(negedge rst);
        @(posedge clk);

        master_reset_to_idle();

        @(posedge clk);
        $display("[%t] # Test expected errors", $time);
        test_errors();

        @(posedge clk);
        $display("[%t] # Filling SRAM with random and reading back", $time);
        fill_and_readback_sram();

        @(posedge clk);
        $display("[%t] # Simple writes with strobe and readback", $time);
        write_strobe_and_readback(.iterations(4096));

        @(posedge clk);
        $display("[%t] # Concurrent and random read/writes in the first 64 bytes", $time);
        random_rw_first_64_byte(.iterations(4096));

        @(posedge clk);
        $display("[%t] # Concurrent, random, and async read/writes over the whole SRAM", $time);
        random_rw_async(.iterations(32 * 1024));

        $finish();
    end

endmodule