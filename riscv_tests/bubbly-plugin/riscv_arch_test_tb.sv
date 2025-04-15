`include "core/params.svh"
`include "axi/axi4lite.svh"

module riscv_arch_test_tb #(
    parameter BIN_BASE_VADDR    = 64'h8000000000,
    parameter ENTRY_POINT_VADDR = 64'h8000000000,
    parameter BIN_SIZE          = 64'h0,
    parameter SIG_START_VADDR   = 64'h0,
    parameter SIG_END_VADDR     = 64'h0,
    parameter INPUT_FILE        = "riscv_arch_test_loaded.bin",
    parameter OUTPUT_SIG_FILE   = "riscv_arch_test_output_sig.bin"
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
    wire halt_gpio;

    // We still have this silly constraint on SRAM size being a multiple of 4kB (ice40 BRAM size)
    basic_soc #(
        .RESET_PC    (ENTRY_POINT_VADDR),
        .GPIO_OUTPUTS(1),
        .SRAM_SIZE_KB((BIN_SIZE/1024/4 + 1) * 4),
        .SRAM_INIT_FILE(INPUT_FILE)
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
        .gpio_outputs(halt_gpio)
    );

    initial begin
        #2; @(posedge clk);

        // This will be considered a timeout
        #1_000_000;
        $finish();
    end

    integer sig_fd;
    always @(posedge halt_gpio) begin
        @(posedge clk);

        sig_fd = $fopen(OUTPUT_SIG_FILE, "wb");
        if (sig_fd == 0) begin
            $display("ERROR: Could not open output signature file.");
            $finish;
        end

        for (int i = SIG_START_VADDR; i < SIG_END_VADDR; i++) begin
            automatic int cur_addr = i - BIN_BASE_VADDR;
            automatic int swizzle = 4 - (cur_addr & 4);
            if (i > SIG_START_VADDR && i % 4 == 0)
                $fwrite(sig_fd, "\n");
            $fwriteh(sig_fd, soc.axi4lite_sram.mem[cur_addr/8][((cur_addr % 4) + swizzle)*8 +: 8]);
        end
        $fwrite(sig_fd, "\n");
        $fclose(sig_fd);

        $finish();
    end
endmodule
