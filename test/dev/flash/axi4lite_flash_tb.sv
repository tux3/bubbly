`include "axi/axi4lite.svh"

module axi4lite_flash_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    wire cs, sclk, si, so, wp, hold;

    axi4lite #(.ADDR_WIDTH(24)) bus();
    axi4lite_flash #(.USE_SB_IO(0)) axi4lite_flash(
        .bus,

        .cs,
        .sclk,
        .si,
        .so,
        .wp,
        .hold
    );
    qspi_flash_pattern_mock qspi_flash_mock(
        .*
    );
    
    assign bus.aclk = clk;
    assign bus.aresetn = !rst;

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
        bus.wstrb = '0;
        bus.wvalid = 0;
        bus.bready = 0;
    endtask

    function automatic logic [63:0] expected_bytes(input int addr, input int count);
        logic [23:0] running_addr = addr;
        logic [63:0] expected_value;
        
        for (int i=0; i<count; i++) begin
            expected_value[i*8 +: 8] = {running_addr[0+:8] ^ running_addr[8+:8] ^ running_addr[16+:8]};
            running_addr++;
        end
        return expected_value;
    endfunction

    task automatic master_read_one(input [23:0] addr, bit defer_rready = 0, bit delay_rready = 0);
        $display("[%t] ### STARTING READ, DEFER: %b, DELAY: %b, ADDR: %h", $time, defer_rready, delay_rready, addr);
        @(posedge clk) begin
            bus.araddr <= addr;
            bus.arvalid <= 1;

            if (!defer_rready && !delay_rready) begin
                if (delay_rready)
                    #2;
                bus.rready <= 1;
            end
        end

        if (!bus.arready) begin
            @(posedge bus.arready);
        end

        @(posedge clk) begin
            bus.araddr <= 'x;
            bus.arvalid <= 0;
        end

        if (!defer_rready && delay_rready)
            #2 bus.rready <= 1;

        @(posedge clk)
            assert(bus.rvalid == 0);
        @(posedge bus.rvalid);
        if (defer_rready) begin
            if (delay_rready)
                #1.5 @(posedge clk);
            bus.rready <= 1;
        end

        @(posedge clk);
        assert(bus.rdata == expected_bytes(addr, 8)) else $error("[%t] Expected data %h, but got %h", $time, expected_bytes(addr, 8), bus.rdata);
        bus.rready <= 0;
    endtask

    task automatic master_read_overlapped(input [23:0] addr1, input [23:0] addr2, input [23:0] addr3);
        $display("[%t] ### STARTING OVERLAPPED READS", $time);

        // Start read 1
        @(posedge clk) begin
            bus.araddr <= addr1;
            bus.arvalid <= 1;
            bus.rready <= 1;
        end

        // Request read 2
        $display("[%t] # STARTED OVERLAPPED READ 1", $time);
        @(posedge clk) begin
            bus.araddr <= addr2;
        end

        fork
            // Ack read 2 started, request read 3
            @(posedge bus.arready) begin
                $display("[%t] # STARTED OVERLAPPED READ 2", $time);
                @(posedge clk)
                    bus.araddr <= addr3;
            end

            // Finish read 1
            @(posedge bus.rvalid) begin
                @(posedge clk);
                $display("[%t] # FINISH OVERLAPPED READ 1", $time);
                assert(bus.rdata == expected_bytes(addr1, 8)) else $error("[%t] Expected read 1 data %h, but got %h", $time, expected_bytes(addr1, 8), bus.rdata);
            end
        join

        fork
            // Ack read 3 started
            @(posedge bus.arready) begin
                $display("[%t] # STARTED OVERLAPPED READ 3", $time);
                @(posedge clk) begin
                    bus.araddr <= 'x;
                    bus.arvalid <= 'b0;
                end
            end

            // Finish read 2
            @(posedge bus.rvalid) begin
                @(posedge clk);
                $display("[%t] # FINISH OVERLAPPED READ 2", $time);
                assert(bus.rdata == expected_bytes(addr2, 8)) else $error("[%t] Expected read 2 data %h, but got %h", $time, expected_bytes(addr2, 8), bus.rdata);
            end
        join

        // Finish read 3
        @(posedge bus.rvalid) begin
            @(posedge clk);
            $display("[%t] # FINISH OVERLAPPED READ 3", $time);
            assert(bus.rdata == expected_bytes(addr3, 8)) else $error("[%t] Expected read 3 data %h, but got %h", $time, expected_bytes(addr3, 8), bus.rdata);
            bus.rready <= 0;
        end
    endtask

    task automatic master_write_simple(input [23:0] addr);
        $display("[%t] ### STARTING SIMPLE WRITE AT %h", $time, addr);

        // Write address and data simultaneously
        @(posedge clk) begin
            bus.awaddr <= addr;
            bus.awvalid <= 1;

            bus.wdata <= 'hDA7A_0000_0000_Da7a;
            bus.wstrb <= 'b00_00_00_00;
            bus.wvalid <= 'b1;

            bus.bready <= 1;
        end

        fork
            @(posedge bus.awready) begin
                @(posedge clk) begin
                    bus.awaddr <= 'x;
                    bus.awvalid <= 'b0;
                end
            end

            @(posedge bus.wready) begin
                @(posedge clk) begin
                    bus.wdata <= 'x;
                    bus.wstrb <= 'x;
                    bus.wvalid <= 'b0;
                end
            end
        join

        // Expect error
        @(posedge bus.bvalid) begin
            @(posedge clk);
            assert(bus.bresp == AXI4LITE_RESP_SLVERR) else $error("[%t] Expected SLVERR write error, but got %h", $time, bus.bresp);
            bus.bready <= 0;
        end
    endtask

    task automatic master_write_addr_first(input [23:0] addr);
        $display("[%t] ### STARTING ADDR FIRST WRITE AT %h", $time, addr);

        // Write address
        @(posedge clk) begin
            bus.awaddr <= addr;
            bus.awvalid <= 1;
        end

        #5;

        // Write data
        @(posedge clk) begin
            bus.wdata <= 'hDA7A_0000_0000_Da7a;
            bus.wstrb <= 'b00_00_00_00;
            bus.wvalid <= 'b1;
        end

        fork
            @(posedge bus.awready) begin
                @(posedge clk) begin
                    bus.awaddr <= 'x;
                    bus.awvalid <= 'b0;
                end
            end

            @(posedge bus.wready) begin
                @(posedge clk) begin
                    bus.wdata <= 'x;
                    bus.wstrb <= 'x;
                    bus.wvalid <= 'b0;
                end
            end
        join

        @(posedge clk)
            bus.bready <= 1;

        // Expect error
        if (!bus.bvalid)
            @(posedge bus.bvalid);
        @(posedge clk);
        assert(bus.bresp == AXI4LITE_RESP_SLVERR) else $error("[%t] Expected SLVERR write error, but got %h", $time, bus.bresp);
        bus.bready <= 0;
    endtask

    task automatic master_write_data_first(input [23:0] addr);
        $display("[%t] ### STARTING DATA FIRST WRITE AT %h", $time, addr);

        // Write data
        @(posedge clk) begin
            bus.wdata <= 'hDA7A_0000_0000_Da7a;
            bus.wstrb <= 'b00_00_00_00;
            bus.wvalid <= 'b1;
        end

        #5;

        // Write address
        @(posedge clk) begin
            bus.awaddr <= addr;
            bus.awvalid <= 1;
        end

        fork
            @(posedge bus.awready) begin
                @(posedge clk) begin
                    bus.awaddr <= 'x;
                    bus.awvalid <= 'b0;
                end
            end

            @(posedge bus.wready) begin
                @(posedge clk) begin
                    bus.wdata <= 'x;
                    bus.wstrb <= 'x;
                    bus.wvalid <= 'b0;
                end
            end
        join

        @(posedge clk)
            bus.bready <= 1;

        // Expect error
        if (!bus.bvalid)
            @(posedge bus.bvalid);
        @(posedge clk);
        assert(bus.bresp == AXI4LITE_RESP_SLVERR) else $error("[%t] Expected SLVERR write error, but got %h", $time, bus.bresp);
        bus.bready <= 0;
    endtask

    initial begin
        // Wait for reset on the other side to propagate so our asserts don't fail
        @(negedge (bus.rvalid | bus.bvalid));

        master_reset_to_idle();
        @(negedge rst);

        // Simple read while waiting for setup
        master_read_one(.addr('hAABBCC));

        // Slower reads
        #2;
        master_read_one(.addr('h123456), .defer_rready(1), .delay_rready(1));
        master_read_one(.addr('h23456), .defer_rready(1));
        master_read_one(.addr('h3456), .delay_rready(1));

        // Request multiple reads in parallel
        #2;
        master_read_overlapped(.addr1('hAA), .addr2('hCC), .addr3('hEE));

        $finish();
    end

    initial begin
        @(negedge rst);

        master_write_simple('h414141);

        #5;
        master_write_addr_first('h1031);

        #5;
        master_write_data_first('h1039);
    end

endmodule