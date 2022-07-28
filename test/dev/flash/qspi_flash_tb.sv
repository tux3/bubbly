module qspi_flash_tb();

timeunit 100ns;
timeprecision 10ns;

bit clk = 0;
bit rst = 0;

reg [23:0] addr;
reg do_read;
wire setup_done;
wire data_ready;
wire [7:0] data;

wire cs, sclk, si, so, wp, hold, capture_clk;

qspi_flash_pattern_mock flash_mock(
    .*
);

qspi_flash #(.USE_SB_IO(0)) flash(
    .clk(clk),
    .rst(rst),
    .addr(addr),
    .do_read(do_read),
    .setup_done(setup_done),
    .data_ready(data_ready),
    .data(data),
    .cs(cs),
    .sclk(sclk),
    .capture_clk(capture_clk),
    .si(si),
    .so(so),
    .wp(wp),
    .hold(hold)
);

// Main clock
initial
begin
    #0 rst = 1;
    #0.5 clk = 1;
    #0.5 clk = 0;
    #0.5 clk = 1;
    #0.3 // Pretend we just barely meet release timing (for some reason?)
    rst = 0;
    #0.2 clk = 0;

    forever begin
        #0.5 clk = !clk;
    end
end

task assert_read_byte;
input [7:0] expected;
begin
    integer i;
    reg [7:0] read_buf;
    for (i = 0; i < 8; ++i) begin
        @(posedge sclk) begin
            read_buf = {read_buf[6:0], si};
        end
    end
    assert(read_buf == expected) else $error("[%t] Expected to read byte %b, but got %b", $time, expected, read_buf);
end
endtask

task assert_reply_byte;
input [7:0] expected;
begin
    integer i;
    reg [7:0] read_buf;
    for (i = 0; i < 8; ++i) begin
        @(posedge sclk) begin
            read_buf = {read_buf[6:0], so};
        end
    end
    assert(read_buf == expected) else $error("[%t] Expected to get reply byte %b, but got %b", $time, expected, read_buf);
end
endtask

task assert_read_quad_byte;
input [7:0] expected;
begin
    reg [7:0] quad_read_buf;
    @(posedge sclk)
        quad_read_buf = {quad_read_buf[3:0], hold, wp, so, si};
    @(posedge sclk)
        quad_read_buf = {quad_read_buf[3:0], hold, wp, so, si};
    assert(quad_read_buf == expected) else $error("[%t] Expected to quad-read byte %b, but got %b", $time, expected, quad_read_buf);
end
endtask

task assert_read_quad_high_impedance;
begin
    @(posedge sclk)
        assert({hold, wp, so, si} === 4'bzzzz) else $error("[%t] Expected high-Z, but got %b", $time, {hold, wp, so, si});
    @(posedge sclk)
        assert({hold, wp, so, si} === 4'bzzzz) else $error("[%t] Expected high-Z, but got %b", $time, {hold, wp, so, si});
    #0.5;
end
endtask

task assert_transfer_quad_byte;
input [7:0] byte_to_send;
begin
    #0.1 @(posedge sclk);
    @(negedge sclk);
    @(posedge sclk) begin
        @(posedge capture_clk);
        #0.1
        assert(data_ready == 1'b1) else $error("[%t] Expected data_ready to go high", $time);
        assert(data == byte_to_send) else $error("[%t] Expected xfered byte %b, but got %b", $time, byte_to_send, data);
    end
end
endtask

task assert_cs_goes_up;
begin
    @(negedge capture_clk)
        #0.1 assert(cs == 'b1) else $fatal(1, "[%t] Expected cs to go up", $time);
end
endtask

// Our mock always returns the xor'd addr as data
function [7:0] expected_reply(input [23:0] addr);
    expected_reply = addr[23:16] ^ addr[15:8] ^ addr[7:0];
endfunction

// Init and wait for setup to be done
initial
begin
    do_read <= 'b0;
    addr <= 24'h8F428F;

    @(posedge setup_done)
        #2;
    @(posedge clk)
        do_read <= 'b1;
end

// Read asserts
initial
begin
    $display("[%t] 1. Check setup", $time);

	// Wake-up (missing all the required delay!)
    @(negedge cs);
    assert_read_byte('hAB); // Wake up from deep sleep opcode
    assert_cs_goes_up();

    // Check this is one of our Adesto chip with quand-send mode
    @(negedge cs);
    assert_read_byte('h9F); // Read Manucturere and Device ID
    assert_reply_byte('h1F); // Adesto
    assert_reply_byte('h85); // AT25SF081
    assert_cs_goes_up();

    // Write-enable
    @(negedge cs);
    assert_read_byte('h06); // Write-enable opcode
    assert_cs_goes_up();

    // Set QE bit to enable quad-mode
    @(negedge cs);
    assert_read_byte('h01); // Write status reg opcode
    assert_read_byte('h80); // Disable most protections
    assert_read_byte('h02); // Disable most protections, set QE bit for quad-read
    assert_cs_goes_up();

    // Write-disable
    @(negedge cs);
    assert_read_byte('h04); // Write-disable opcode
    assert_cs_goes_up();

    // Start quad-read continuous read-mode
    @(negedge cs);
    assert_read_byte('hEB); // Quad-read IO opcode
    assert_read_quad_byte('h00); // Addr
    assert_read_quad_byte('h00); // Addr
    assert_read_quad_byte('h00); // Addr
    assert_read_quad_byte('h20); // Mode (continuous read)
    assert_read_quad_high_impedance();  // Dummy byte
    assert_read_quad_high_impedance();  // Dummy byte
    assert_cs_goes_up();

    assert(setup_done == 1'b1) else $error("[%t] Expected setup_done to go high after setup", $time);
    assert(cs == 1'b1) else $error("[%t] Expected cs to go high after setup", $time);
    assert(data_ready == 1'b0) else $error("[%t] Expected data_ready to stay low after setup", $time);

    $display("[%t] 2. Check data transfer", $time);

    @(negedge cs);
    assert_read_quad_byte(addr[23:16]); // Addr
    assert_read_quad_byte(addr[15:8]); // Addr
    assert_read_quad_byte(addr[7:0]); // Addr
    assert_read_quad_byte('h20); // Mode (continuous read)
    assert_read_quad_high_impedance();  // Dummy byte
    assert_read_quad_high_impedance();  // Dummy byte

    // Start data transfer and check that we receive it correctly
    assert_transfer_quad_byte(expected_reply(addr));
    assert_transfer_quad_byte(expected_reply(addr+1));
    assert_transfer_quad_byte(expected_reply(addr+2));
    assert_transfer_quad_byte(expected_reply(addr+3));

    // Stop reading for a short time
    do_read <= 'b0;
    #0.5
    
    $display("[%t] 3. Restart from second address", $time);

    // Restart reading from different addresss
    @(posedge clk);
    addr <= ~addr;
    do_read <= 'b1;

    @(negedge cs);
    assert_read_quad_byte(addr[23:16]); // Addr
    assert_read_quad_byte(addr[15:8]); // Addr
    assert_read_quad_byte(addr[7:0]); // Addr
    assert_read_quad_byte('h20); // Mode (continuous read)
    assert_read_quad_high_impedance();  // Dummy byte
    assert_read_quad_high_impedance();  // Dummy byte
    assert_transfer_quad_byte(expected_reply(addr));
    assert_transfer_quad_byte(expected_reply(addr+1));
    assert_transfer_quad_byte(expected_reply(addr+2));
    assert_transfer_quad_byte(expected_reply(addr+3));

    // Stop reading for a long time, at an odd cycle
    @(posedge clk);
    do_read <= 'b0;
    #4
    
    $display("[%t] 4. Restart from third address", $time);

    // Restart reading from different addresss
    @(posedge clk);
    addr <= addr ^ (addr <<< 3) + 'hABCD;
    do_read <= 'b1;

    @(negedge cs);
    assert_read_quad_byte(addr[23:16]); // Addr
    assert_read_quad_byte(addr[15:8]); // Addr
    assert_read_quad_byte(addr[7:0]); // Addr
    assert_read_quad_byte('h20); // Mode (continuous read)
    assert_read_quad_high_impedance();  // Dummy byte
    assert_read_quad_high_impedance();  // Dummy byte
    assert_transfer_quad_byte(expected_reply(addr));
    assert_transfer_quad_byte(expected_reply(addr+1));
    assert_transfer_quad_byte(expected_reply(addr+2));
    assert_transfer_quad_byte(expected_reply(addr+3));

    // Stop
    do_read <= 0;
    addr <= 'bx;

    #10 $finish;

end

endmodule
