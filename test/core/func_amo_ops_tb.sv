`include "core/params.svh"
`include "axi/axi4lite.svh"

module func_amo_ops_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    bit [64-1:0] sram_addr = {{64-`ALEN{1'b0}}, 4'b0001, {`ALEN-4{1'b0}}};
    const logic [50*32-1:0] code_buf = {<<{
        {<<{32'h0b800093}}, //     li  x1,184
        {<<{32'h1000b12f}}, //     lr.d    x2,(x1)
        {<<{16'h00a1}}, //         addi    x1,x1,8
        {<<{32'h1000a1af}}, //     lr.w    x3,(x1)
        {<<{16'h10e1}}, //         addi    x1,x1,-8
        {<<{32'h0a000293}}, //     li  x5,160
        {<<{16'h928a}}, //         add x5,x5,x2
        {<<{32'h1a43c237}}, //     lui x4,0x1a43c
        {<<{32'h20f2021b}}, //     addiw   x4,x4,527 # 1a43c20f <.sram_ptr_ptr+0x1a43c169>
        
        // 000000000000001e <.prepare_mem>:
        {<<{32'h0042b023}}, //     sd  x4,0(x5)
        {<<{16'h12e1}}, //         addi    x5,x5,-8
        {<<{32'hfe22dde3}}, //     bne x5,x2,1e <.prepare_mem>
        
        {<<{32'hf980c237}}, //     lui     x4,0xf980c
        {<<{32'h4a12021b}}, //     addiw   x4,x4,1185 # fffffffff980c4a1 <.sram_ptr_ptr+0xfffffffff980c3ef>
        {<<{16'h0232}}, //         slli    x4,x4,0xc
        {<<{32'h1a320213}}, //     addi    x4,x4,419 # 1a3 <.sram_ptr_ptr+0xf1>
        {<<{16'h0232}}, //         slli    x4,x4,0xc
        {<<{32'he3b20213}}, //     addi    x4,x4,-453 # fffffffffffffe3b <.sram_ptr_ptr+0xfffffffffffffd89>
        {<<{16'h0232}}, //         slli    x4,x4,0xc
        {<<{32'h5f420213}}, //     addi    x4,x4,1524 # 5f4 <.sram_ptr_ptr+0x542>
        {<<{16'h828a}}, //         mv  x5,x2
        
        // run
        {<<{32'h0c42a52f}}, //     amoswap.w.aq    x10,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h0442a5af}}, //     amoadd.w.aq x11,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h6442a62f}}, //     amoand.w.aq x12,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h4442a6af}}, //     amoor.w.aq  x13,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h2442a72f}}, //     amoxor.w.aq x14,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'ha442a7af}}, //     amomax.w.aq x15,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'he442a82f}}, //     amomaxu.w.aq    x16,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h8442a8af}}, //     amomin.w.aq x17,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'hc442a92f}}, //     amominu.w.aq    x18,x4,(x5)
        
        {<<{32'h05010293}}, //     addi    x5,x2,80
        {<<{32'h0c42ba2f}}, //     amoswap.d.aq    x20,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h0442baaf}}, //     amoadd.d.aq x21,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h6442bb2f}}, //     amoand.d.aq x22,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h4442bbaf}}, //     amoor.d.aq  x23,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h2442bc2f}}, //     amoxor.d.aq x24,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'ha442bcaf}}, //     amomax.d.aq x25,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'he442bd2f}}, //     amomaxu.d.aq    x26,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'h8442bdaf}}, //     amomin.d.aq x27,x4,(x5)
        {<<{16'h02a1}}, //         addi    x5,x5,8
        {<<{32'hc442be2f}}, //     amominu.d.aq    x28,x4,(x5)
        {<<{32'h0000006f}}, //     j   a2 <.run+0x6c> (Infinite loop)
        
        {<<{32'hA0A0A0A0}},                                // align 8B
        {<<{sram_addr[31:0]}}, {<<{sram_addr[63:32]}},     // sram ptr
        {<<{32'hAABBCCDD}}, {<<{32'hAABBCCDD}}             // misc data
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
        @(posedge clk);
        @(posedge clk) begin
            assert(soc.data_axi.arvalid == '0) else $error("[%t] Expected !arvalid for read at %h", $time, addr); // Otherwise, this is going to get messy!
            force soc.data_axi.araddr = addr;
            force soc.data_axi.arvalid = '1;
        end

        forever @(posedge clk) begin
            if (soc.data_axi.arready) begin
                force soc.data_axi.rready = '1;
                force soc.data_axi.arvalid = '0;
                release soc.data_axi.araddr;
                break;
            end
        end

        while (!(soc.data_axi.rvalid && soc.data_axi.rready))
            @(posedge clk);
        release soc.data_axi.arvalid;
        assert(soc.data_axi.rresp == AXI4LITE_RESP_OKAY) else $error("[%t] Expected rresp OKAY for read at %h, but got %h", $time, addr, soc.data_axi.rresp);
        assert(soc.data_axi.rdata == data) else $error("[%t] Expected to read %h at %h, but got %h", $time, data, addr, soc.data_axi.rdata);
        @(posedge clk);
        release soc.data_axi.rready;
    endtask

    initial begin
        #2; @(posedge clk);

        #2000;

        assert(soc.core.regs.xreg[1] == 'hB8);
        assert(soc.core.regs.xreg[2] == sram_addr);
        assert(soc.core.regs.xreg[3] == 'hFFFFFFFFAABBCCDD);
        assert(soc.core.regs.xreg[4] == 'h980C4A11A2E3B5F4);
        assert(soc.core.regs.xreg[5] == sram_addr + 'h90);
        assert(soc.core.regs.xreg[6] == 'h0);
        assert(soc.core.regs.xreg[7] == 'h0);
        assert(soc.core.regs.xreg[8] == 'h0);
        assert(soc.core.regs.xreg[9] == 'h0);
        for (int i=10; i<19; i+=1)
            assert(soc.core.regs.xreg[i] == 'h1A43C20F);
        assert(soc.core.regs.xreg[19] == 'h0);
        for (int i=20; i<29; i+=1)
            assert(soc.core.regs.xreg[i] == 'h1A43C20F);

        axi4_read_expect_data(.addr(sram_addr+'h00), .data('hA2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h08), .data('h1A43C20F + 'hA2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h10), .data('h1A43C20F & 'hA2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h18), .data('h1A43C20F | 'hA2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h20), .data('h1A43C20F ^ 'hA2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h28), .data('h1A43C20F));
        axi4_read_expect_data(.addr(sram_addr+'h30), .data('hA2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h38), .data('hA2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h40), .data('h1A43C20F));
        
        axi4_read_expect_data(.addr(sram_addr+'h50), .data('h980C4A11A2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h58), .data('h1A43C20F + 'h980C4A11A2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h60), .data('h1A43C20F & 'h980C4A11A2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h68), .data('h1A43C20F | 'h980C4A11A2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h70), .data('h1A43C20F ^ 'h980C4A11A2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h78), .data('h1A43C20F));
        axi4_read_expect_data(.addr(sram_addr+'h80), .data('h980C4A11A2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h88), .data('h980C4A11A2E3B5F4));
        axi4_read_expect_data(.addr(sram_addr+'h90), .data('h1A43C20F));
        $finish();
    end
endmodule
