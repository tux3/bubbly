`include "../../core/params.svh"

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

    output [9:0] PROBE,

    output PROBE_GND_34,

    output reg [3:0] LED
    );

wire clk, rst;
pll pll(
    .CLK100MHZ,
    .RSTN,
    .clk,
    .rst
);

spi_soc #(.RESET_PC(`FLASH_TEXT_ADDR)) spi_soc(
    .clk,
    .rst,

    .PROBE,
    .LED(LED[3:1]),

    .*
);

assign PROBE_GND_34 = '0;

logic [23:0] counter;
assign LED[0] = counter[$bits(counter)-1];

always_ff @(posedge clk) begin
    if (rst)
        counter <= '0;
    else
        counter <= counter + 1;
end

endmodule
