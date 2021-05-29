`include "../../core/params.svh"

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
    output PROBE_0,
    output PROBE_1,
    output PROBE_2,
    output PROBE_3,
    output PROBE_4,
    output PROBE_5,
    output reg LED
);

logic clk;
logic rst;

pll pll(
    .clk_in(CLK_16MHZ),
    .resetb_in(RESETN),
    .clk_out(clk),
    .reset_out(rst)
);

spi_soc spi_soc(
    .clk,
    .rst,

    .*
);

endmodule
