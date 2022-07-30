`include "../core/params.svh"

module spi_soc#(
    parameter RESET_PC = `RESET_PC,
    parameter PROBE_OUTPUTS = 10,
    parameter LED_OUTPUTS = 3
) (
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
    input [0:0] SWITCH,
    output [PROBE_OUTPUTS-1:0] PROBE,
    output reg [LED_OUTPUTS-1:0] LED,
    
    // Ethernet
    input ETH_COL,
    input ETH_CRS,
    input ETH_REF_CLK,
    output ETH_RSTN,
    input ETH_RX_CLK,
    input ETH_RX_DV,
    input [3:0] ETH_RXD,
    input ETH_RXERR,
    input ETH_TX_CLK,
    output ETH_TX_EN,
    output [3:0] ETH_TXD
);

//assign PROBE[0] = FLASH_CS;
//assign PROBE[1] = flash_capture_clk_gated;
//assign PROBE[2] = FLASH_MOSI;
//assign PROBE[3] = FLASH_MISO;
//assign PROBE[4] = FLASH_WP;
//assign PROBE[5] = FLASH_HOLD;
//assign PROBE[6] = FLASH_CLK;
//assign PROBE[7] = rst;

//assign PROBE[0] = gated_core_clk;
//assign PROBE[1] = eth_soc.core.ifetch_stall_next;
//assign PROBE[2] = eth_soc.core.ifetch_exception;
//assign PROBE[3] = eth_soc.core.decode_stall_next;
//assign PROBE[4] = eth_soc.core.decode_next_stalled;
//assign PROBE[5] = eth_soc.core.decode_exception;
//assign PROBE[6] = eth_soc.core.exec_stall_next;
//assign PROBE[7] = eth_soc.core.exec_exception;
//assign PROBE[8] = eth_soc.core.exec_is_reg_write;
//assign PROBE[9] = eth_soc.core.exec_is_trap;

assign PROBE = '0;

bit core_clk_enable, core_clk_pulse;
reg core_clk_enable_reg, core_clk_pulse_reg;
// We have synchronous resets, so the gated clock must run during rst!
wire gated_core_clk;
BUFGCE gated_core_clk_bufgce (
    .I(clk),
    .O(gated_core_clk),
    .CE(rst || (SWITCH & core_clk_enable_reg))
);
assign FLASH_CLK = gated_core_clk;

wire flash_capture_clk_gated;
BUFGCE flash_capture_clk_gated_bufgce (
    .I(FLASH_CAPTURE_CLK),
    .O(flash_capture_clk_gated),
    .CE(rst || (SWITCH & core_clk_enable_reg))
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

wire [`ALEN+`ILEN-1:0] fetch_instr;
wire [`XLEN-1:0] reg_pc;
wire [`XLEN-1:0] core_reg_read_data;
wire [$bits(LED)-1:0] led_gpio;

eth_soc #(
    .RESET_PC(RESET_PC),
    .GPIO_OUTPUTS($bits(LED))
) eth_soc (
    .clk(gated_core_clk),
    .rst,

    .cs(FLASH_CS),
    .sclk(),
    .capture_clk(flash_capture_clk_gated),
    .si(FLASH_MOSI),
    .so(FLASH_MISO),
    .wp(FLASH_WP),
    .hold(FLASH_HOLD),
    
    .eth_rx_clk(ETH_RX_CLK),
    .eth_rxd(ETH_RXD),
    .eth_rx_dv(ETH_RX_DV),
    .eth_rx_er(ETH_RXERR),
    .eth_tx_clk(ETH_TX_CLK),
    .eth_txd(ETH_TXD),
    .eth_tx_en(ETH_TX_EN),
    .eth_col(ETH_COL),
    .eth_crs(ETH_CRS),
    .eth_reset_n(ETH_RSTN),

    .fetch_instr,
    .reg_pc,
    .reg_read_sel(recv_data[4:0]),
    .reg_read_data(core_reg_read_data),
    .gpio_outputs(led_gpio)
);


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
localparam DBG_CMD_GET_FETCHED_INSTR = 'h09;
localparam DBG_CMD_ECHO_CC = 'hCC;
logic [2:0] dbg_state;

logic [127:0] send_buf;
logic [3:0] send_buf_count;

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
    LED <= led_gpio | led_buf;

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
        core_clk_enable <= '1;
        core_clk_pulse <= '0;
    end else if (recv_ready) begin
//        if (dbg_state == DBG_IDLE) begin
//            if (recv_data == DBG_CMD_NOP) begin
//                send_data <= '0;
//                send_buf_count <= 'x;
//            end else if (recv_data == DBG_CMD_ECHO) begin
//                send_data <= DBG_CMD_ECHO;
//                dbg_state <= DBG_ECHO;
//                send_buf_count <= 'x;
//            end else if (recv_data == DBG_CMD_TOGGLE_LED)begin
//                send_data <= '0;
//                send_buf_count <= 'x;
//                led_buf <= ~led_buf;
//            end else if (recv_data == DBG_CMD_ENABLE_CLOCK) begin
//                core_clk_enable <= '1;
//                send_data <= '0;
//                send_buf_count <= 'x;
//            end else if (recv_data == DBG_CMD_DISABLE_CLOCK) begin
//                core_clk_enable <= '0;
//                send_data <= '0;
//                send_buf_count <= 'x;
//            end else if (recv_data == DBG_CMD_STEP_CLOCK) begin
//                core_clk_pulse <= !core_clk_pulse;
//                send_data <= '0;
//                send_buf_count <= 'x;
//            end else if (recv_data == DBG_CMD_GET_PC) begin
//                send_buf <= reg_pc;
//                send_buf_count <= 8;
//                dbg_state <= DBG_REPLYING;
//                send_data <= '0;
//            end else if (recv_data == DBG_CMD_GET_REG) begin
//                send_data <= '0;
//                send_buf_count <= 'x;
//                dbg_state <= DBG_READ_REG;
//            end else if (recv_data == DBG_CMD_READ_FLASH) begin
//                // Flash is in use by the CPU
//				//dbg_state <= DBG_FLASH_READ_ADDR;
//				//dbg_read_addr_count = 'b11;
//				send_data <= 'hFF;
//                send_buf_count <= 'x;
//            end else if (recv_data == DBG_CMD_ECHO_CC) begin
//                send_data <= 'hCC;
//                send_buf_count <= 'x;
//            end else if (recv_data == DBG_CMD_GET_FETCHED_INSTR) begin
//                send_buf <= fetch_instr;
//                send_buf_count <= 14;
//                dbg_state <= DBG_REPLYING;
//                send_data <= '0;
//            end else begin
//                send_data <= 'hFF;
//                send_buf_count <= 'x;
//            end
//        end else if (dbg_state == DBG_ECHO) begin
//            send_data <= recv_data;
//            dbg_state <= DBG_IDLE;
//        end else if (dbg_state == DBG_READ_REG) begin
//            send_buf <= core_reg_read_data;
//            send_buf_count <= 8;
//            dbg_state <= DBG_REPLYING;
//            send_data <= '0;
//        end else if (dbg_state == DBG_REPLYING) begin
//            send_data <= send_buf[send_buf_count*8-1 -: 8];
//            if (send_buf_count == 1)
//                dbg_state <= DBG_IDLE;
//            send_buf_count <= send_buf_count-1;
//        end else begin
//            send_data <= 'hFF;
//        end
    end
end

endmodule
