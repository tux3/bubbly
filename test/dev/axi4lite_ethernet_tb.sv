`include "core/params.svh"
`include "axi/axi4lite.svh"

module axi4lite_ethernet_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    // For now this just tests that we can write and read back our ethernet MMIO regs 0 and 1
    bit [64-1:0] eth_addr = {{64-`ALEN{1'b0}}, 3'b011, {`ALEN-3{1'b0}}};
    const logic [22*32-1:0] code_buf = {<<32{
        'b000001010000_00000_000_00001_0010011, // ADDI r1, r0, mmio_ptr_ptr
        'b000000000000_00001_011_00001_0000011, // LD r1, r1, 0
        
        // li x2, 0x0242fd4152a1
        'b00100100001011111101000100110111,
        'b01000001010100010000000100011011,
        'b00000000110000010001000100010011,
        'b00101010000100010000000100010011,
        
        // li x3, 0x6d169d272206
        'b00000000001101101001000110110111,
        'b10110100111100011000000110011011,
        'b00000000110000011001000110010011,
        'b10010011100100011000000110010011,
        'b00000000110100011001000110010011,
        'b00100000011000011000000110010011,
        
        'b00000000000000001011001000000011, // ld x4, 0(x1)
        'b00000000100000001011001010000011, // ld x5, 8(x1)
        'b00000000001000001011000000100011, // sd x2, 0(x1)
        'b00000000001100001011010000100011, // sd x3, 8(x1)
        'b00000000000000001011001100000011, // ld x6, 0(x1)
        'b00000000100000001011001110000011, // ld x7, 8(x1) 

        'b00000000000000000000_00000_0010011,  // Pad/align
        'b11111111110111111111_00000_1101111,    // Inf. loop
         eth_addr[31:0], eth_addr[63:32]         // mmio ptr
    }};

    wire cs, sclk, si, so, wp, hold, capture_clk;
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
        .capture_clk,
        .si,
        .so,
        .wp,
        .hold,

        .reg_pc,
        .reg_read_sel,
        .reg_read_data,
        .fetch_instr(),
        .gpio_outputs()
    );

    initial begin
        #0 rst = 1;
        #2 rst = 0;
    end

    initial forever
        #0.5 clk = !clk;

    task axi4_read_expect_data(input [`ALEN-1:0] addr, input [64-1:0] data);
        assert(soc.data_axi.arvalid == '0); // Otherwise, this is going to get messy!
        force soc.data_axi.rready = '0;
        force soc.data_axi.araddr = addr;
        force soc.data_axi.arvalid = '1;

        forever @(posedge clk) begin
            if (soc.data_axi.arready) begin
                force soc.data_axi.rready = '1;
                force soc.data_axi.arvalid = '0;
                force soc.data_axi.araddr = 'x;
                break;
            end
        end

        @(posedge clk);
        while (!(soc.data_axi.rvalid && soc.data_axi.rready))
            @(posedge clk);
        assert(soc.data_axi.rvalid && soc.data_axi.rready) else $error("[%t] ????", $time);
        assert(soc.data_axi.rresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected rresp OKAY for read at %h, but got %h", $time, addr, soc.data_axi.rresp);
        assert(soc.data_axi.rdata == data) else $error("[%t] Expected to read %h at %h, but got %h", $time, data, addr, soc.data_axi.rdata);
        force soc.data_axi.rready = '0;
    endtask

    initial begin
        #2; @(posedge clk);

        #750;
        @(posedge clk);

        assert(soc.core.regs.xreg[1] == eth_addr);
        assert(soc.core.regs.xreg[2] == 'h0242fd4152a1);
        assert(soc.core.regs.xreg[3] == 'h6d169d272206);
        assert(soc.core.regs.xreg[4] == 'h0);
        assert(soc.core.regs.xreg[5] == 'h0);
        assert(soc.core.regs.xreg[6] == 'h0242fd4152a1);
        assert(soc.core.regs.xreg[7] == 'h6d169d272206);

        axi4_read_expect_data(.addr(eth_addr), .data('h0242fd4152a1));
        axi4_read_expect_data(.addr(eth_addr+8), .data('h6d169d272206));
        $finish();
    end
endmodule
