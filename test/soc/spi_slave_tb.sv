module spi_slave_tb();

bit ext_clk = 0;
bit rst = 0;

reg led;

reg sclk = 0;
reg mosi = 0;
wire miso;
reg ss = 1;

reg [7:0] send_data;
wire send_ready;
wire [7:0] recv_data;
wire recv_ready;

reg [31:0] MOSI_TO_SEND = 'h0201FF03; // Sent from MSB to LSB
reg [7:0] MOSI_TX_COUNT = $bits(MOSI_TO_SEND) - 1;

spi_slave spi(
    .ext_clk(ext_clk),
    .rst(rst),
    .sclk(sclk),
    .mosi(mosi),
    .miso(miso),
    .ss(ss),
    .send_data(send_data),
    .send_ready(send_ready),
    .recv_data(recv_data),
    .recv_ready(recv_ready)
);

// Initial top regs
initial
begin
    led = 1;
    send_data = 1;
end

// Main clock
initial
begin
    #0 rst = 1;
    #50 ext_clk = 1;
    #50 ext_clk = 0;
    rst = 0;

    forever begin
        #50 ext_clk = !ext_clk;
    end
end

// SPI clock and ss
initial
begin: spiloop
    integer i;
    integer j;

    ss = 1;
    mosi = MOSI_TO_SEND[MOSI_TX_COUNT];
    MOSI_TX_COUNT--;
    sclk = 0;

    for (j = 0; j < 16; ++j) begin
        #425 ss = 0;

        for (i = 0; i < 8*2; i++) begin
            #503 sclk = !sclk;
        end

        #431 ss = 1;
        #1000;
    end

    #1000 $finish;
end

always @(negedge sclk)
begin
    mosi = MOSI_TO_SEND[MOSI_TX_COUNT];
    if (MOSI_TX_COUNT > 0)
        MOSI_TX_COUNT--;
end

// Handle received SPI commands
always @(posedge ext_clk)
begin: set_led
    reg next_led_val;

    if (rst) begin
        led <= 1;
    end else if (recv_ready) begin
        $display("-- Read SPI data: %h", recv_data);
        case (recv_data)
            8'h00: next_led_val = led;
            8'h01: next_led_val = 1;
            8'h02: next_led_val = 0;
            8'h03: next_led_val = !led;
            default: next_led_val = led;
        endcase
        if (send_ready) begin
            send_data = {send_data, send_data[7]};
            $display("-- Sending SPI data: %h", send_data);
        end
        led <= next_led_val;
    end
end

endmodule
