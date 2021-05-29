`include "../../core/params.svh"

// Location of the boot code in flash
`define FLASH_TEXT_ADDR 4 * 1024 * 1024

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
    
    output PROBE_0,
    output PROBE_1,
    output PROBE_2,
    output PROBE_3,
    output PROBE_4,
    output PROBE_5,
    
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
    
    .LED(LED[0]),
    
    .*
);

logic [25:0] counter;
assign LED[3:1] = counter[$bits(counter)-1 -: 3];

always_ff @(posedge clk) begin
    if (rst)
        counter <= '0;
    else
        counter <= counter + 1;
end

endmodule
