module qspi_flash_tb();

reg clk;
reg rst;

reg [31:0] data_to_send = 'h0201FF7A;
reg [7:0] size_to_send = $bits(data_to_send);
reg [7:0] to_send_pos = size_to_send;

reg [23:0] addr;
reg do_read;
wire setup_done;
wire data_ready;
wire [7:0] data;

wire cs = 1'bz;
wire sclk = 1'bz;
wire si = to_send_pos >= size_to_send ? 1'bz : data_to_send[to_send_pos];
wire so = to_send_pos >= size_to_send ? 1'bz : data_to_send[to_send_pos+1];
wire wp = to_send_pos >= size_to_send ? 1'bz : data_to_send[to_send_pos+2];
wire hold = to_send_pos >= size_to_send ? 1'bz : data_to_send[to_send_pos+3];

qspi_flash flash(
    .clk(clk),
    .rst(rst),
    .addr(addr),
    .do_read(do_read),
    .setup_done(setup_done),
    .data_ready(data_ready),
    .data(data),
    .cs(cs),
    .sclk(sclk),
    .si(si),
    .so(so),
    .wp(wp),
    .hold(hold)
);

// Main clock
initial
begin
    clk = 0;
    rst = 1;
    #50 clk = 1;
    #50 clk = 0;
    #50 clk = 1;
    #35 // Inconveniently short up level.
    rst = 0;
    #15 clk = 0;

    forever begin
        #50 clk = !clk;
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
    #50;
end
endtask

task assert_transfer_quad_byte;
input [7:0] byte_to_send;
begin
    to_send_pos -= 4;
    #1 @(posedge sclk);
    @(negedge sclk) begin
        to_send_pos -= 4;
    end
    @(posedge sclk) begin
        #1
        assert(data_ready == 1'b1) else $error("[%t] Expected data_ready to go high", $time);
        assert(data == byte_to_send) else $error("[%t] Expected xfered byte %b, but got %b", $time, byte_to_send, data);
    end
end
endtask

task assert_cs_goes_up;
begin
    @(negedge sclk)
        #1 assert(cs == 'b1);
end
endtask

// Init and wait for setup to be done
initial
begin
    do_read <= 'b0;
    addr <= 24'h8F428F;

    @(posedge setup_done)
        #200;
    @(posedge clk)
        do_read <= 'b1;
end

// Read asserts
initial
begin
    // I. Check setup

	// Wake-up (missing all the required delay!)
	@(negedge cs);
    assert_read_byte('hAB); // Wake up from deep sleep opcode
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

    // II. Check data transfer

    @(negedge cs);
    assert_read_quad_byte(addr[23:16]); // Addr
    assert_read_quad_byte(addr[15:8]); // Addr
    assert_read_quad_byte(addr[7:0]); // Addr
    assert_read_quad_byte('h20); // Mode (continuous read)
    assert_read_quad_high_impedance();  // Dummy byte
    assert_read_quad_high_impedance();  // Dummy byte

    // Start data transfer and check that we receive it correctly
    assert_transfer_quad_byte(data_to_send[31:24]);
    assert_transfer_quad_byte(data_to_send[23:16]);
    assert_transfer_quad_byte(data_to_send[15:8]);
    assert_transfer_quad_byte(data_to_send[7:0]);

    // Stop reading for a short time
    do_read <= 'b0;
    to_send_pos <= size_to_send;
    #50

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
    assert_transfer_quad_byte(data_to_send[31:24]);
    assert_transfer_quad_byte(data_to_send[23:16]);
    assert_transfer_quad_byte(data_to_send[15:8]);
    assert_transfer_quad_byte(data_to_send[7:0]);

    // Stop reading for a long time, at an odd cycle
    @(posedge clk);
    do_read <= 'b0;
    to_send_pos <= size_to_send;
    #400

    // Restart reading from different addresss
    @(posedge clk);
    addr <= addr ^ (addr <<< 3);
    do_read <= 'b1;

    @(negedge cs);
    assert_read_quad_byte(addr[23:16]); // Addr
    assert_read_quad_byte(addr[15:8]); // Addr
    assert_read_quad_byte(addr[7:0]); // Addr
    assert_read_quad_byte('h20); // Mode (continuous read)
    assert_read_quad_high_impedance();  // Dummy byte
    assert_read_quad_high_impedance();  // Dummy byte
    assert_transfer_quad_byte(data_to_send[31:24]);
    assert_transfer_quad_byte(data_to_send[23:16]);
    assert_transfer_quad_byte(data_to_send[15:8]);
    assert_transfer_quad_byte(data_to_send[7:0]);

    // Stop
    do_read <= 0;
    addr <= 'bx;
    to_send_pos <= size_to_send;

    #1000 $finish;

end

endmodule
