// Simple SPI test

module top(
    input CLK_16MHZ,
    input RESETN,
    input SPI_CLK,
    input SPI_MOSI,
    output SPI_MISO,
    input SPI_SS,
	output FLASH_CS,
	output FLASH_CLK,
	inout FLASH_MOSI,
	inout FLASH_MISO,
	inout FLASH_WP,
	inout FLASH_HOLD,
	output PROBE_1,
	output PROBE_2,
	output PROBE_3,
	output PROBE_4,
	output PROBE_5,
	output PROBE_6,
    output reg LED
);

//assign PROBE_1 = FLASH_CS;
//assign PROBE_2 = FLASH_CLK;
//assign PROBE_3 = FLASH_MOSI;
//assign PROBE_4 = FLASH_MISO;
//assign PROBE_5 = FLASH_WP;
//assign PROBE_6 = FLASH_HOLD;

assign PROBE_1 = SPI_SS;
assign PROBE_2 = SPI_CLK;
assign PROBE_3 = SPI_MOSI;
assign PROBE_4 = SPI_MISO;

wire clk;
wire rst;

pll pll(
    .clk_in(CLK_16MHZ),
    .resetb_in(RESETN),
    .clk_out(clk),
    .reset_out(rst)
);

reg [7:0] send_data;
wire send_ready;
wire [7:0] recv_data;
wire recv_ready;

spi_slave spi(
    .ext_clk(clk),
    .rst(rst),
    .sclk(SPI_CLK),
    .mosi(SPI_MOSI),
    .miso(SPI_MISO),
    .ss(SPI_SS),
    .send_data(send_data),
    .send_ready(send_ready),
    .recv_data(recv_data),
    .recv_ready(recv_ready)
);

reg [23:0] flash_addr;
reg flash_do_read;
wire flash_setup_done;
wire flash_data_ready;
wire [7:0] flash_data;

qspi_flash flash(
    .clk(clk),
    .rst(rst),
    .addr(flash_addr),
    .do_read(flash_do_read),
    .setup_done(flash_setup_done),
    .data_ready(flash_data_ready),
    .data(flash_data),
    .cs(FLASH_CS),
    .sclk(FLASH_CLK),
    .si(FLASH_MOSI),
    .so(FLASH_MISO),
    .wp(FLASH_WP),
    .hold(FLASH_HOLD)
);

/* reg [7:0] waddr; */
/* reg [7:0] raddr; */
/* reg [255:0] din; */
/* reg write_en; */
/* reg [255:0] dout; */
/* bram bram( */
/*     .waddr(waddr), */
/*     .raddr(raddr), */
/*     .din(din), */
/*     .write_en(write_en), */
/*     .wclk(clk), */
/*     .rclk(clk), */
/*     .dout(dout) */
/* ); */

// Yosys doesn't support enums yet =/
// TODO: Fix Yosys!
localparam FLASH_SETUP = 0;
localparam FLASH_IDLE = 1;
localparam FLASH_WAIT_ADDR = 2;
localparam FLASH_READING = 3;
reg [1:0] flash_state;

localparam DBG_IDLE = 0;
localparam DBG_READ_ADDR = 1;
localparam DBG_WAIT_FLASH = 2;
localparam DBG_REPLYING = 3;
localparam DBG_ECHO = 4;
reg [2:0] dbg_state;

reg [23:0] addr_to_read;
reg [7:0] data_read;
reg [1:0] dbg_read_addr_count;
reg dbg_reply_signaled;

// Read from Flash when requested by SPI command
always @(posedge clk, posedge rst)
begin
	if (rst) begin
		flash_state <= FLASH_SETUP;
		flash_do_read <= 0;
		flash_addr <= 0;
		data_read <= 0;
	end else if (flash_setup_done) begin
		if (flash_state == FLASH_SETUP)
			flash_state <= FLASH_IDLE;
		if (flash_data_ready) begin
			data_read <= flash_data;
			flash_do_read <= 0;
        end

        if (flash_state == FLASH_READING && dbg_state != DBG_WAIT_FLASH) begin
            flash_state <= FLASH_IDLE;
		end else if (flash_state == FLASH_IDLE && dbg_state == DBG_WAIT_FLASH) begin
			flash_addr <= addr_to_read;
			flash_do_read <= 1;
			flash_state <= FLASH_READING;
		end
	end
end

// Handle received SPI commands
always @(posedge clk, posedge rst)
begin: set_led
    if (rst) begin
        LED <= 0;
        send_data <= 0;
		addr_to_read <= 0;
		dbg_state <= DBG_IDLE;
		dbg_reply_signaled <= 0;
		dbg_read_addr_count = 0;
    end else if (recv_ready) begin
		if (dbg_state == DBG_IDLE) begin
			if (recv_data == 8'h00) begin
				send_data <= 0;
			end else if (recv_data == 8'h01) begin
				dbg_state <= DBG_READ_ADDR;
				dbg_read_addr_count = 'b11;
				send_data <= dbg_read_addr_count;
			end else if (recv_data == 8'h02)begin
				LED <= ~LED;
				send_data <= 'hAB;
			end else if (recv_data == 8'h10) begin
				send_data <= flash_addr[7:0];
			end else if (recv_data == 8'h11) begin
				send_data <= flash_addr[15:8];
			end else if (recv_data == 8'h12) begin
				send_data <= flash_addr[23:16];
			end else if (recv_data == 8'hCC) begin
				send_data <= 'hCC;
			end else if (recv_data == 8'hCD) begin
				send_data <= 'hCD;
				dbg_state <= DBG_ECHO;
			end else begin
				send_data <= 'h00;
			end
		end else if (dbg_state == DBG_ECHO) begin
			send_data <= recv_data;
			dbg_state <= DBG_IDLE;
		end else if (dbg_state == DBG_READ_ADDR) begin
			if (dbg_read_addr_count == 'b01) begin
				dbg_state <= DBG_WAIT_FLASH;
			end
			addr_to_read <= {addr_to_read[15:0], recv_data[7:0]};
			dbg_read_addr_count = dbg_read_addr_count - 1;
			send_data <= dbg_read_addr_count;
		end else if (dbg_state == DBG_WAIT_FLASH) begin
			if (flash_state == FLASH_IDLE) begin
				if (dbg_reply_signaled == 0) begin
					send_data <= 'hFF;
					dbg_reply_signaled <= 1;
				end else begin
					send_data <= data_read;
					dbg_reply_signaled <= 0;
					dbg_state <= DBG_IDLE;
				end
			end else begin
				send_data <= 'hFE;
			end
		end else begin
			send_data <= 'hBB;
			LED <= 1;
		end
	end
end

endmodule
