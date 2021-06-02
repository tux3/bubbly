`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module func_store_tb;
    timeunit 100ns;
    timeprecision 10ns;
    
    bit clk = 0;
    bit rst = 0;

    bit [64-1:0] sram_addr = {{64-`ALEN{1'b0}}, 4'b0001, {`ALEN-4{1'b0}}};
    const logic [22*32-1:0] code_buf = {<<32{
        'b000001000000_00000_000_00001_0010011, // ADDI r1, r0, sram_ptr_ptr
        'b000000010000_00001_011_00011_0000011, // LD r3, r1, h10
        'b000000001000_00001_011_00010_0000011, // LD r2, r1, 8
        'b000000000000_00001_011_00001_0000011, // LD r1, r1, 0

        'b0000000_00010_00001_011_00000_0100011, // SD r1, r2, 0
        'b0000000_00011_00001_011_01000_0100011, // SD r1, r3, 8
        'b0000000_00010_00001_011_10000_0100011, // SD r1, r2, h10

        'b0000000_00011_00001_010_10100_0100011, // SW r1, r3, h14
        'b0000000_00011_00001_001_00010_0100011, // SH r1, r3, h2
        'b0000000_00010_00001_000_00001_0100011, // SB r1, r2, h1

        'b0000000_00011_00001_000_11000_0100011, // SB r1, r3, h18
        'b0000000_00010_00001_000_11001_0100011, // SB r1, r2, h19
        'b0000000_00011_00001_001_11010_0100011, // SH r1, r3, h1A
        'b0000000_00010_00001_010_11100_0100011, // SW r1, r2, h1C
        'b0000000_00011_00001_000_11111_0100011, // SB r1, r3, h1F

        'b11111111110111111111_00000_1101111,   // Inf. loop
         sram_addr[31:0], sram_addr[63:32],     // sram ptr
         'hAABBCCDD, 'hAAEEBBFF,                // misc data
         'h11223344, 'h55667788                 // misc data
    }};

    wire cs, sclk, si, so, wp, hold;
    qspi_flash_buffer_mock #(.BUFFER_SIZE($bits(code_buf))) qspi_flash_mock(
        .*,
        .buffer(code_buf)
    );

    wire [`XLEN-1:0] reg_pc;
    wire [4:0] reg_read_sel;
    wire [`XLEN-1:0] reg_read_data;

    basic_soc soc(
        .clk,
        .rst,

        .cs,
        .sclk,
        .si,
        .so,
        .wp,
        .hold,

        .reg_pc,
        .reg_read_sel,
        .reg_read_data
    );

    initial begin
        #0 rst = 1;
        #2 rst = 0;
    end

    initial forever
        #0.5 clk = !clk;

    task axi4_read_expect_data(input [`ALEN-1:0] addr, input [64-1:0] data);
        @(posedge clk);
        @(posedge clk) begin
            assert(soc.data_axi.arvalid == '0); // Otherwise, this is going to get messy!
            force soc.data_axi.araddr = addr;
            force soc.data_axi.arvalid = '1;
        end

        forever @(posedge clk) begin
            if (soc.data_axi.arready) begin
                force soc.data_axi.rready = '1;
                release soc.data_axi.arvalid;
                release soc.data_axi.araddr;
                break;
            end
        end

        while (!(soc.data_axi.rvalid && soc.data_axi.rready))
            @(posedge clk);
        assert(soc.data_axi.rresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected rresp OKAY for read at %h, but got %h", $time, addr, soc.data_axi.rresp);
        assert(soc.data_axi.rdata == data) else $error("[%t] Expected to read %h at %h, but got %h", $time, data, addr, soc.data_axi.rdata);
        @(posedge clk);
        release soc.data_axi.rready;
    endtask

    initial begin
        #2; @(posedge clk);

        #1000;

        assert(soc.core.regs.xreg[1] == sram_addr);
        assert(soc.core.regs.xreg[2] == 'hAAEEBBFFAABBCCDD);
        assert(soc.core.regs.xreg[3] == 'h5566778811223344);

        axi4_read_expect_data(.addr(sram_addr), .data('hAAEEBBFF3344DDDD));
        axi4_read_expect_data(.addr(sram_addr+'h8), .data('h5566778811223344));
        axi4_read_expect_data(.addr(sram_addr+'h10), .data('h11223344AABBCCDD));
        axi4_read_expect_data(.addr(sram_addr+'h18), .data('h44BBCCDD3344DD44));
        $finish();
    end
endmodule