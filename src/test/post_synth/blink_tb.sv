`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module blink_tb;
    timeunit 10ns;
    timeprecision 1ns;

    bit clk = 0;
    bit rst = 0;

    logic [3:0] LED;
    bit [3:0] SWITCH = '1;

    bit [64-1:0] gpio_addr = {{64-`ALEN{1'b0}}, 3'b010, {`ALEN-3{1'b0}}};
    const logic [14*32-1:0] code_buf = {<<32{
    'h14a64485, 'h99b74905, 'h899b0098, 'h80236809, 'h49130124, 'h19fd0019, 'hfe099fe3, 'hffffb7ed,
//        'b000000110000_00000_000_00001_0010011, // ADDI r1, r0, gpio_ptr_ptr
//        'b000000000000_00001_011_00001_0000011, // LD r1, r1, 0
//        'b111111111111_00000_000_00100_0010011, // ADDI r4, r0, -1
//        'b000000000010_00000_000_00011_0010011, // ADDI r3, r0, 2
//        'b000000000001_00000_000_00010_0010011, // ADDI r2, r0, 1

//        'b0000000_00100_00001_011_00000_0100011, // SD r1, r4, 0
//        'b0000000_00000_00001_010_00100_0100011, // SW r1, r0, 4
//        'b0000000_00011_00001_000_00000_0100011, // SB r1, r3, 0
        'b0000000_00011_00001_000_00010_0100011, // SB r1, r3, 2
        'b0000000_00011_00001_000_00011_0100011, // SB r1, r3, 3
        'b0000000_00010_00001_000_00110_0100011, // SB r1, r2, 6

        'b11111111110111111111_00000_1101111,   // Inf. loop
         gpio_addr[31:0], gpio_addr[63:32]     // gpio ptr
    }};

    wire cs, sclk, si, so, wp, hold;
    serial_spi_flash_buffer_mock #(.BUFFER_SIZE($bits(code_buf))) qspi_flash_mock(
        .*,
        .buffer(code_buf)
    );

    wire SPI_CLK = '0;
    wire SPI_MOSI = '0;
    wire SPI_MISO = '0;
    wire SPI_SS = '0;

    top sim_top(
        .CLK100MHZ(clk),
        .RSTN(!rst),

        .SPI_CLK,
        .SPI_MOSI,
        .SPI_MISO,
        .SPI_SS,

        .FLASH_CS(cs),
        .FLASH_CLK(sclk),
        .FLASH_MOSI(si),
        .FLASH_MISO(so),
        .FLASH_WP(wp),
        .FLASH_HOLD(hold),

        .SWITCH,
        .LED
    );

    initial begin
        #0 rst = 1;
        #2 rst = 0;
    end

    initial forever
        #0.5 clk = !clk;
endmodule
