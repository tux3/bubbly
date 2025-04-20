`include "core/params.svh"
`include "axi/axi4lite.svh"

module rust_test_tb #(
    parameter BIN_BASE_VADDR    = 64'h0,
    parameter ENTRY_POINT_VADDR = 64'h0,
    parameter BIN_SIZE          = 64'h8000,
    parameter INPUT_FILE        = "test_loaded.bin"
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

    // We're not using the ROM, but let's just declare _something_
    wire cs, sclk, si, so, wp, hold, capture_clk;
    qspi_flash_pattern_mock qspi_flash_mock(
        .*
    );

    wire [`XLEN-1:0] reg_pc;
    wire [4:0] reg_read_sel;
    wire [`XLEN-1:0] reg_read_data;
    wire success_gpio, fail_gpio;

    test_soc #(
        .RESET_PC      (ENTRY_POINT_VADDR     ),
        .GPIO_OUTPUTS  (2                     ),
        .SRAM_SIZE_KB  (BIN_SIZE/1024 + 1 + 32),
        .SRAM_INIT_FILE(INPUT_FILE            )
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
        .gpio_outputs({success_gpio, fail_gpio})
    );

    initial begin
        #2;
        @(posedge clk);

        // This will be considered a timeout
        #1_000_000;
        $error("Rust test FAIL by timeout");
        $finish();
    end

    integer sig_fd;
    always @(posedge clk) begin
        if (fail_gpio)
            $error("Rust test signaled FAIL");
        if (fail_gpio || success_gpio)
            $finish();
    end
endmodule
