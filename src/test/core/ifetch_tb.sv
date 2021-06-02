`include "../../core/params.svh"
`include "../../axi/axi4lite.svh"

module ifetch_tb;
    timeunit 100ns;
    timeprecision 10ns;

    bit clk = 0;
    bit rst = 0;

    wire cs, sclk, si, so, wp, hold;

    axi4lite #(.ADDR_WIDTH(24)) bus();
    axi4lite_flash #(.USE_SB_IO(0)) axi4lite_flash(
        .bus,

        .cs,
        .sclk,
        .si,
        .so,
        .wp,
        .hold
    );
    qspi_flash_pattern_mock qspi_flash_mock(
        .*
    );

    logic [`XLEN-1:0] source_addr = 'x;
    wire [`ILEN-1:0] instruction;
    wire [`ALEN-1:0] instruction_addr;
    wire [`ALEN-1:0] instruction_next_addr;
    wire ifetch_exception;
    wire [3:0] ifetch_trap_cause;
    wire ifetch_stall_next;
	wire next_stalled = '0;
    wire flush = '0;
    ifetch ifetch(
        .clk,
        .rst,
        .flush,

        .pc(source_addr),
        .instruction,
        .instruction_addr,
        .instruction_next_addr,
        .ifetch_exception,
        .ifetch_trap_cause,
		.next_stalled(next_stalled),
        .stall_next(ifetch_stall_next),

        .sys_bus(bus)
    );

    initial begin
        #0 rst = 1;
    end

    initial forever
        #0.5 clk = !clk;

    function automatic logic [63:0] expected_bytes(input int addr, input int count);
        logic [23:0] running_addr = addr;
        logic [63:0] expected_value = '0;
        for (int i=0; i<count; i++) begin
            expected_value[i*8 +: 8] = {running_addr[0+:8] ^ running_addr[8+:8] ^ running_addr[16+:8]};
            running_addr++;
        end
        return expected_value;
    endfunction

    task automatic read_instr_simple(input [`ALEN-1:0] addr);
        logic [7:0] expected_low_byte = expected_bytes(addr, 1);
        logic expect_exception = expected_low_byte[4:0] == 'b11111; // Check instr len > 32b exceptions
        logic is_compressed_instr = expected_low_byte[1:0] != 'b11;

        @(posedge clk) begin
            source_addr <= addr;
            rst <= 'b0;
        end

        @(posedge clk) begin
            source_addr <= 'x;
        end

        @(negedge ifetch_stall_next);
        if (expect_exception) begin
            assert(ifetch_exception);
            assert(instruction === 'x);
        end else begin
            assert(!ifetch_exception);
            assert(instruction_addr == addr);
            if (is_compressed_instr)
                assert(instruction[15:0] === expected_bytes(addr, 2)) else $error("[%t] At addr %h expected 0x%h, but got 0x%h", $time, addr, expected_bytes(addr, 2), instruction);
            else
                assert(instruction === expected_bytes(addr, `ILEN/8)) else $error("[%t] At addr %h expected 0x%h, but got 0x%h", $time, addr, expected_bytes(addr, `ILEN/8), instruction);
        end

        @(posedge clk) begin
            source_addr <= 'x;
            rst <= 'b1;
        end
    endtask

    localparam RAND_READ_COUNT = 8192;
    initial begin
        #2; @(posedge clk);

        $display("Starting manual unit tests");

        // 1. Simple reads (uncompressed instr)
        read_instr_simple(.addr('h300));
        read_instr_simple(.addr('h1122));
        read_instr_simple(.addr('h0E0D10));
        read_instr_simple(.addr('h253220));

        // 2. Simple reads (compressed instr)
        read_instr_simple(.addr('h0));
        read_instr_simple(.addr('h1234));
        read_instr_simple(.addr('hA1E00));
        read_instr_simple(.addr('h0FA390));

        // 3. Read that crosses a cache line, where the 2nd line is cached, but not the first
        read_instr_simple(.addr('hFFF8));
        read_instr_simple(.addr('hFFF6));

        // 4. Read that crosses a cache line, where both are in cache
        read_instr_simple(.addr('hFFF6));

        // 5. Instruction too long exception
        read_instr_simple(.addr('h3FC));

        // 6. Random reads
        $display("Starting random read tests, please stand by...");
        for (int i=0; i<RAND_READ_COUNT; ++i) begin: rand_read
            logic [`ALEN-1 - (basic_cache_params::tag_size-5):0] rand_addr; // NOTE: We're only keeping 5 tag bits to increase collisions!
            assert(std::randomize(rand_addr));
            rand_addr[0] = 0; // NOTE: Alignment exceptions are raised on the control flow instruction, the ifetch should never see a misaligned addr
            read_instr_simple(.addr(rand_addr));
        end

        $finish();
    end
endmodule