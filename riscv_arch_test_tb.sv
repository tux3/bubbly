`include "core/params.svh"
`include "axi/axi4lite.svh"

module riscv_arch_test_tb #(
    parameter BIN_BASE_VADDR    = '0,
    parameter BIN_SIZE          = '0,
    parameter ENTRY_POINT_VADDR = '0,
    parameter INPUT_FILE        = "riscv_arch_test_loaded.bin",
    parameter INPUT_FILE        = "riscv_arch_test_output_sig.bin"
) ();
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    initial begin
        #0 rst = 1;
        #2 rst = 0;
    end

    initial forever
    #0.5 clk = !clk;

    logic [BIN_SIZE*8-1:0] mem_buf;
    initial
    $readmemb(INPUT_FILE, mem_buf);

    // We're not using the ROM, but let's just declare _something_
    wire cs, sclk, si, so, wp, hold, capture_clk;
    qspi_flash_pattern_mock qspi_flash_mock(
        .*
    );

    wire [`XLEN-1:0] reg_pc;
    wire [4:0] reg_read_sel;
    wire [`XLEN-1:0] reg_read_data;

    // We map the SRAM at whatever the default crossbar addr is for it!
    // For basic_soc this happens to be this particular value (SRAM is the 2nd device on the bus)
    const bit [64-1:0] SRAM_ADDR = {{64-`ALEN{1'b0}}, 4'b0001, {`ALEN-4{1'b0}}};
    assert SRAM_ADDR == BIN_BASE_VADDR

    basic_soc #(
        .RESET_PC    (ENTRY_POINT_VADDR),
        .SRAM_SIZE_KB(BIN_SIZE/1024 + 1)
    ) soc(
        .clk,
        .rst,

        .cs,
        .sclk,
        .capture_clk,
        .si,
        .so,
        .wp,
        .hold,

        .reg_pc,
        .reg_read_sel,
        .reg_read_data,
        .fetch_instr (),
        .gpio_outputs()
    );


endmodule
