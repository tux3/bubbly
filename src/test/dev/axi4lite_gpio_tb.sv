`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module axi4lite_gpio_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    logic [6:0] outputs;

    bit [64-1:0] gpio_addr = {{64-`ALEN{1'b0}}, 3'b010, {`ALEN-3{1'b0}}};
    const logic [14*32-1:0] code_buf = {<<32{
        'b000000110000_00000_000_00001_0010011, // ADDI r1, r0, gpio_ptr_ptr
        'b000000000000_00001_011_00001_0000011, // LD r1, r1, 0
        'b111111111111_00000_000_00100_0010011, // ADDI r4, r0, -1
        'b000000000010_00000_000_00011_0010011, // ADDI r3, r0, 2
        'b000000000001_00000_000_00010_0010011, // ADDI r2, r0, 1

        'b0000000_00100_00001_011_00000_0100011, // SD r1, r4, 0
        'b0000000_00000_00001_010_00100_0100011, // SW r1, r0, 4
        'b0000000_00011_00001_000_00000_0100011, // SB r1, r3, 0
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

    wire [`XLEN-1:0] reg_pc;
    wire [4:0] reg_read_sel;
    wire [`XLEN-1:0] reg_read_data;

    // Note: Only 7 since we want to test the "out of bounds" gpio is still addressable (just disconnected)
    basic_soc #(.GPIO_OUTPUTS(7)) soc(
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
        .reg_read_data,
        .gpio_outputs(outputs)
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

        assert(outputs == 'b100_0010);
        axi4_read_expect_data(.addr(gpio_addr), .data('h00010000_00000100));
        $finish();
    end
endmodule
