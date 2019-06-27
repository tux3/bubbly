timeunit 100ns;
timeprecision 10ns;

module flash_reader_tb;

    bit clk = 0;
    bit rst = 1;

    logic [23:0] addr = 0;
    logic start_read = 0;
    logic keep_reading = 0;
    logic [7:0] data;
    logic data_ready;

    wire cs, sclk, si, so, wp, hold;

    qspi_flash_mock flash(
        .*
    );

    flash_reader flash_reader(
            .*
    );

    task start_read_task(input reset, input [23:0] read_addr);
    begin
        @(posedge clk) begin
            addr <= read_addr;
            if (reset)
               keep_reading <= 0;
            start_read <= 1;
        end

        @(posedge clk) begin
            start_read <= 0;
            keep_reading <= 1;
        end
    end
    endtask

    task expect_byte_value(input [7:0] expected_byte);
        @(posedge data_ready)
            assert(expected_byte == data) else $error("[%t] Expected data %h, but got %h", $time, expected_byte, data);
    endtask

    task expect_bytes(input int count);
        logic [23:0] running_addr;
        running_addr = addr;
        while (count--) begin
            expect_byte_value(running_addr[0+:8] ^ running_addr[8+:8] ^ running_addr[16+:8]);
            running_addr++;
        end
    endtask

    task finish_subtest;
        @(posedge clk);
        keep_reading <= 0;
        addr <= 'x;
        #2 @(posedge clk);
    endtask

    initial begin
        #0 rst = 0;
        #1.5 rst = 1;
        forever
            #0.5 clk = !clk;
    end

    initial begin
        @(posedge rst);

        $display("[%t] 1. Start new simple 4 byte read", $time);
        start_read_task(.reset(0), .read_addr('h4389E1));
        expect_bytes(4);
        finish_subtest();

        $display("[%t] 2. Schedule second read", $time);
        start_read_task(.reset(0), .read_addr('hA00C));
        #3
        start_read_task(.reset(0), .read_addr('hA17D6B));
        expect_byte_value('hAC); // Byte of first read
        expect_bytes(3);
        finish_subtest();

        $display("[%t] 3. Preempt read", $time);
        start_read_task(.reset(0), .read_addr('hA00C));
        #5
        start_read_task(.reset(1), .read_addr('hA17D6B));
        expect_bytes(4);
        finish_subtest();

        $display("[%t] 4. Start new reads every cycle", $time);
        start_read_task(.reset(0), .read_addr('h123456));
        start_read_task(.reset(0), .read_addr('h778899));
        start_read_task(.reset(0), .read_addr('h987654));
        start_read_task(.reset(0), .read_addr('h412351));
        start_read_task(.reset(1), .read_addr('hAABBCC));
        start_read_task(.reset(0), .read_addr('hFFFFFF));
        start_read_task(.reset(0), .read_addr('hC126A7));
        start_read_task(.reset(1), .read_addr('h445566));
        start_read_task(.reset(1), .read_addr('h556677));
        expect_bytes(2);
        finish_subtest();

        $display("[%t] 5. Race new read just before data_ready", $time);
        start_read_task(.reset(1), .read_addr('h11));
        #14
        start_read_task(.reset(0), .read_addr('h22));
        fork
            @(negedge clk) assert(data_ready);
            expect_byte_value('h11); // First read
        join
        expect_byte_value('h22); // Second read
        expect_byte_value('h23); // Second read
        finish_subtest();

        $display("[%t] 6. Race new with data_ready", $time);
        start_read_task(.reset(0), .read_addr('h33));
        #15
        fork
            @(negedge clk) assert(data_ready);
            start_read_task(.reset(0), .read_addr('h44));
            expect_byte_value('h33); // First read
        join
        expect_byte_value('h44); // Second read
        expect_byte_value('h45); // Second read
        finish_subtest();

        $display("[%t] 7. Various reads", $time);
        start_read_task(.reset(1), .read_addr('hC1));
        #8
        start_read_task(.reset(0), .read_addr('h0));
        expect_byte_value('hC1); // First read
        start_read_task(.reset(0), .read_addr('hD9));
        expect_byte_value('h00); // Second read
        expect_bytes('h2);
        start_read_task(.reset(0), .read_addr('hC8));
        #5
        start_read_task(.reset(1), .read_addr('hA5));
        expect_bytes('h4);
        start_read_task(.reset(0), .read_addr('hFFFFE0));
        expect_byte_value('hA9); // Previous read
        expect_bytes('h110); // Long read

        $finish();
    end
endmodule
