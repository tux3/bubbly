`include "../core/params.svh"

module spi_flash_soc(
    input clk,
    input rst,
    input SPI_CLK,
    input SPI_MOSI,
    output SPI_MISO,
    input SPI_SS,
    output FLASH_CS,
    output FLASH_CLK,
    input FLASH_CAPTURE_CLK,
    inout FLASH_MOSI,
    inout FLASH_MISO,
    inout FLASH_WP,
    inout FLASH_HOLD,
    output PROBE_0,
    output PROBE_1,
    output PROBE_2,
    output PROBE_3,
    output PROBE_4,
    output PROBE_5,
    output reg LED
);

assign PROBE_0 = FLASH_CLK;
assign PROBE_1 = FLASH_CS;
assign PROBE_2 = FLASH_MOSI;
assign PROBE_3 = FLASH_MISO;
assign PROBE_4 = FLASH_WP;
assign PROBE_5 = FLASH_HOLD;

bit core_clk_enable, core_clk_pulse;
reg core_clk_enable_reg, core_clk_pulse_reg;
logic gated_core_clk = clk & core_clk_enable_reg;

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

wire [`XLEN-1:0] reg_pc;
wire [`XLEN-1:0] core_reg_read_data;

basic_soc basic_soc(
    .clk(gated_core_clk),
    .rst,

    // The flash is driven by the spi debug here, CPU won't be running
    .cs(),
    .sclk(),
    .si(),
    .capture_clk(),
    .so(),
    .wp(),
    .hold(),

    .fetch_instr(),
    .reg_pc,
    .reg_read_sel(recv_data[4:0]),
    .reg_read_data(core_reg_read_data),
    .gpio_outputs()
);

reg [23:0] flash_addr;
reg flash_do_read;
wire flash_setup_done;
wire flash_data_ready;
wire [7:0] flash_data;

qspi_flash #(.USE_SB_IO(0)) flash(
    .clk(clk),
    .rst(rst),
    .addr(flash_addr),
    .do_read(flash_do_read),
    .setup_done(flash_setup_done),
    .data_ready(flash_data_ready),
    .data(flash_data),
    .cs(FLASH_CS),
    .sclk(FLASH_CLK),
    .capture_clk(FLASH_CAPTURE_CLK),
    .si(FLASH_MOSI),
    .so(FLASH_MISO),
    .wp(FLASH_WP),
    .hold(FLASH_HOLD)
);

enum {FLASH_SETUP, FLASH_IDLE, FLASH_WAIT_ADDR, FLASH_READING} flash_state;
reg [23:0] addr_to_read;
reg [7:0] data_read;
reg [1:0] dbg_read_addr_count;
reg dbg_reply_signaled;

localparam DBG_IDLE = 0;
localparam DBG_REPLYING = 1;
localparam DBG_ECHO = 2;
localparam DBG_READ_REG = 3;
localparam DBG_FLASH_READ_ADDR = 4;
localparam DBG_FLASH_REPLYING = 5;

localparam DBG_CMD_NOP = 'h00;
localparam DBG_CMD_ECHO = 'h01;
localparam DBG_CMD_TOGGLE_LED = 'h02;
localparam DBG_CMD_ENABLE_CLOCK = 'h03;
localparam DBG_CMD_DISABLE_CLOCK = 'h04;
localparam DBG_CMD_STEP_CLOCK = 'h05;
localparam DBG_CMD_GET_PC = 'h06;
localparam DBG_CMD_GET_REG = 'h07;
localparam DBG_CMD_READ_FLASH = 'h08;
localparam DBG_CMD_ECHO_CC = 'hCC;
logic [2:0] dbg_state;

logic [63:0] send_buf;
logic [3:0] send_buf_count;

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
			flash_state <= FLASH_IDLE;
		end else if (flash_state == FLASH_IDLE && dbg_state == DBG_FLASH_READ_ADDR) begin
			flash_state <= FLASH_WAIT_ADDR;
		end else if (flash_state == FLASH_WAIT_ADDR && dbg_state == DBG_FLASH_REPLYING) begin
			flash_addr <= addr_to_read;
			flash_do_read <= 1;
			flash_state <= FLASH_READING;
		end
	end
end

always @(negedge clk) begin
    if (rst) begin
        core_clk_enable_reg <= '0;
        core_clk_pulse_reg <= '0;
    end else begin
        core_clk_enable_reg <= core_clk_enable | (core_clk_pulse != core_clk_pulse_reg);
        core_clk_pulse_reg <= core_clk_pulse;
    end
end

reg led_buf;
always @(posedge clk)
    LED <= led_buf;

// Handle received SPI commands
always @(posedge clk)
begin: set_led
    if (rst) begin
        led_buf <= '0;
        send_data <= '0;
        send_buf <= 'x;
        send_buf_count <= '0;
        dbg_state <= DBG_IDLE;
        dbg_reply_signaled <= '0;
        core_clk_enable <= '0;
        core_clk_pulse <= '0;
    end else if (recv_ready) begin
        if (dbg_state == DBG_IDLE) begin
            if (recv_data == DBG_CMD_NOP) begin
                send_data <= '0;
                send_buf_count <= 'x;
            end else if (recv_data == DBG_CMD_ECHO) begin
                send_data <= DBG_CMD_ECHO;
                dbg_state <= DBG_ECHO;
                send_buf_count <= 'x;
            end else if (recv_data == DBG_CMD_TOGGLE_LED)begin
                send_data <= '0;
                send_buf_count <= 'x;
                led_buf <= ~led_buf;
            end else if (recv_data == DBG_CMD_ENABLE_CLOCK) begin
                // Cannot enable CPU without FLASH
                //core_clk_enable <= '1;
                send_data <= 'hFF;
                send_buf_count <= 'x;
            end else if (recv_data == DBG_CMD_DISABLE_CLOCK) begin
                core_clk_enable <= '0;
                send_data <= '0;
                send_buf_count <= 'x;
            end else if (recv_data == DBG_CMD_STEP_CLOCK) begin
                // Cannot enable CPU without FLASH
                //core_clk_pulse <= !core_clk_pulse;
                send_data <= 'hFF;
                send_buf_count <= 'x;
            end else if (recv_data == DBG_CMD_GET_PC) begin
                send_buf <= reg_pc;
                send_buf_count <= 8;
                dbg_state <= DBG_REPLYING;
                send_data <= send_buf_count;
            end else if (recv_data == DBG_CMD_GET_REG) begin
                send_data <= '0;
                send_buf_count <= 'x;
                dbg_state <= DBG_READ_REG;
            end else if (recv_data == DBG_CMD_READ_FLASH) begin
				dbg_state <= DBG_FLASH_READ_ADDR;
				dbg_read_addr_count = 'b11;
				send_data <= dbg_read_addr_count;
            end else if (recv_data == DBG_CMD_ECHO_CC) begin
                send_data <= 'hCC;
                send_buf_count <= 'x;
            end else begin
                send_data <= 'hFF;
                send_buf_count <= 'x;
            end
        end else if (dbg_state == DBG_ECHO) begin
            send_data <= recv_data;
            dbg_state <= DBG_IDLE;
        end else if (dbg_state == DBG_READ_REG) begin
            send_buf <= core_reg_read_data;
            send_buf_count <= 8;
            dbg_state <= DBG_REPLYING;
            send_data <= '0;
        end else if (dbg_state == DBG_REPLYING) begin
            send_data <= send_buf[send_buf_count*8-1 -: 8];
            if (send_buf_count == 1)
                dbg_state <= DBG_IDLE;
            send_buf_count <= send_buf_count-1;
        end else if (dbg_state == DBG_FLASH_READ_ADDR) begin
			if (dbg_read_addr_count == 'b01) begin
				dbg_state <= DBG_FLASH_REPLYING;
			end
			addr_to_read <= {addr_to_read[15:0], recv_data[7:0]};
			dbg_read_addr_count = dbg_read_addr_count - 1;
			send_data <= dbg_read_addr_count;
		end else if (dbg_state == DBG_FLASH_REPLYING) begin
			if (flash_state == FLASH_IDLE) begin
				if (dbg_reply_signaled == 0) begin
					send_data <= 'hFD;
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
            send_data <= 'hFF;
        end
    end
end

endmodule
