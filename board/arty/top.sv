`include "core/params.svh"

// Location of the boot code in flash (4MiB)
`define FLASH_TEXT_ADDR 'h400000

module top(
    input CLK100MHZ,
    input RSTN,

    // SPI_CLK is on a non-CCIO pin, it can't be routed to a BUFG...
    (* clock_buffer_type = "BUFR" *)
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
    
    input ETH_COL,
    input ETH_CRS,
    output ETH_REF_CLK,
    output ETH_RSTN,
    input ETH_RX_CLK,
    input ETH_RX_DV,
    input [3:0] ETH_RXD,
    input ETH_RXERR,
    input ETH_TX_CLK,
    output ETH_TX_EN,
    output [3:0] ETH_TXD,

    input [3:0] SWITCH,
    output [9:0] PROBE,
    output PROBE_GND_34,
    output reg [3:0] LED
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

//assign PROBE[0] = rst;
//assign PROBE[1] = eth_soc.axi4lite_ethernet.tx_eth_hdr_ready;
//assign PROBE[2] = eth_soc.axi4lite_ethernet.tx_eth_hdr_valid;
//assign PROBE[3] = eth_soc.axi4lite_ethernet.tx_eth_payload_axis_tready;
//assign PROBE[4] = eth_soc.axi4lite_ethernet.tx_eth_payload_axis_tvalid;
//assign PROBE[5] = eth_soc.axi4lite_ethernet.eth_tx_writing_first_data;
//assign PROBE[6] = eth_soc.axi4lite_ethernet.eth_tx_writing;
//assign PROBE[7] = clk;

assign PROBE = '0;
assign PROBE_GND_34 = '0;

wire clk, rst;
wire flash_capture_clk;
wire eth_ref_clk;
assign ETH_REF_CLK = eth_ref_clk;
pll pll(
    .CLK100MHZ,
    .RSTN,
    .clk,
    .rst,
    .flash_capture_clk,
    .eth_ref_clk
);

reg [$bits(SWITCH)-1:0] switch_sync1;
reg [$bits(SWITCH)-1:0] switch_reg;
always_ff @(posedge flash_capture_clk) begin
    switch_sync1 <= SWITCH;
    switch_reg <= switch_sync1;
end

eth_soc #(
    .RESET_PC(`FLASH_TEXT_ADDR),
    .GPIO_OUTPUTS($bits(LED)-1)
) eth_soc (
    .clk,
    .rst,

    .cs(FLASH_CS),
    .sclk(FLASH_CLK),
    .capture_clk(flash_capture_clk),
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

    .gpio_outputs(LED[3:1])
);

logic [24:0] counter;
assign LED[0] = counter[$bits(counter)-1] && switch_reg;

always_ff @(posedge clk) begin
    if (rst)
        counter <= '0;
    else
        counter <= counter + 1;
end

endmodule
