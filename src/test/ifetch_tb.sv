timeunit 100ns;
timeprecision 10ns;

`include "../core/params.svh"
`include "../axi4lite.svh"

module ifetch_tb;

    bit clk = 0;
    bit rst = 0;

    wire cs, sclk, si, so, wp, hold;

    axi4lite #(.ADDR_WIDTH(24)) bus(.aclk(clk), .aresetn(!rst));
    axi4lite_flash #(.USE_SB_IO(0)) axi4lite_flash(
        .bus,

        .cs,
        .sclk,
        .si,
        .so,
        .wp,
        .hold
    );
    qspi_flash_mock qspi_flash_mock(
        .*
    );

    logic [`ALEN-1:0] source_addr = 'x;
    wire [`ILEN-1:0] instruction;
    wire ifetch_exception;
    logic source_stall = 'b1;
    wire ifetch_stall_prev;
    wire ifetch_stall_next;
    ifetch ifetch(
        .clk,
        .rst,

        .addr(source_addr),
        .instruction,
        .ifetch_exception,
        .prev_stalled(source_stall),
        .stall_prev(ifetch_stall_prev),
        .stall_next(ifetch_stall_next),

        .sys_bus(bus)
    );

    initial begin
        #0 rst = 1;
        #3 rst = 0;
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
        logic expect_exception = addr[0]; // Must be 16bit aligned
    
        @(posedge clk) begin
            source_addr <= addr;
            source_stall <= 'b0;
        end

        if (ifetch_stall_prev)
            @(negedge ifetch_stall_prev);
        @(posedge clk) begin
            source_addr <= 'x;
            source_stall <= '1;
        end
        
        @(negedge ifetch_stall_next);
        if (expect_exception) begin
            assert(ifetch_exception);
            assert(instruction === 'x);
        end else begin
            assert(!ifetch_exception);
            assert(instruction === expected_bytes(addr, `ILEN/8)) else $error("[%t] At addr %h expected 0x%h, but got 0x%h", $time, addr, expected_bytes(addr, `ILEN/8), instruction);
        end
        @(posedge clk)
            #0.1 assert(ifetch_stall_next === 'b1);
    endtask
    
    task automatic start_fast_read(input [`ALEN-1:0] addr);
        // ifetch_stall_prev is not registered, it can spuriously go down
        forever @(posedge clk) begin
            #0.1;
            if (ifetch_stall_prev)
                continue;
            source_addr = addr;
            source_stall = 'b0;
            break;
        end
    endtask
    
    task automatic check_fast_read(input [`ALEN-1:0] addr);
        logic expect_exception = addr[0]; // Must be 16bit aligned
        
        forever @(posedge clk) begin
            #0.1;
            if (!ifetch_stall_next)
                break;
        end
        
        if (expect_exception) begin
            assert(ifetch_exception);
            assert(instruction === 'x);
        end else begin
            assert(!ifetch_exception);
            assert(instruction === expected_bytes(addr, `ILEN/8)) else $error("[%t] At addr %h expected data %h, but got %h", $time, addr, expected_bytes(addr, `ILEN/8), instruction);
        end
    endtask


    localparam RAND_READ_COUNT = 8192;
    initial begin
        @(negedge rst);
        
        $display("Starting manual unit tests");

        // 1. Simple reads
        read_instr_simple(.addr('h0));
        read_instr_simple(.addr('h1));
        read_instr_simple(.addr('h1234));
        read_instr_simple(.addr('hA1E));
        
        // 2. Read that crosses a cache line, where the 2nd line is cached, but not the first
        read_instr_simple(.addr('hCCC8));
        read_instr_simple(.addr('hCCC6));
        
        // 3. Read that crosses a cache line, where both are in cache
        read_instr_simple(.addr('hCCC6));
        
        // 4. Reads with unstalled source
        fork
            // Start reads
            begin
                start_fast_read(.addr('hAA0536));
                start_fast_read(.addr('hAA0536));
                start_fast_read(.addr('hAA0530));
                start_fast_read(.addr('hAA0530));
                start_fast_read(.addr('hCC));
                start_fast_read(.addr('hCD));
                start_fast_read(.addr('hCE));
                start_fast_read(.addr('hCF));
                start_fast_read(.addr('hD0));
                start_fast_read(.addr('hAA052E));
                
                @(posedge clk)
                    source_stall <= '1;
            end
            
            // Check results
            begin
                check_fast_read(.addr('hAA0536));
                check_fast_read(.addr('hAA0536));
                check_fast_read(.addr('hAA0530));
                check_fast_read(.addr('hAA0530));
                check_fast_read(.addr('hCC));
                check_fast_read(.addr('hCD));
                check_fast_read(.addr('hCE));
                check_fast_read(.addr('hCF));
                check_fast_read(.addr('hD0));
                check_fast_read(.addr('hAA052E));
            end
        join
        
        // 5. Random reads
        $display("Starting random read tests, please stand by...");
        for (int i=0; i<RAND_READ_COUNT; ++i) begin: rand_read
            logic [`ALEN-1 - (ifetch.icache_tag_size-5):0] rand_addr; // NOTE: We're only keeping 5 tag bits to increase collisions!
            assert(std::randomize(rand_addr));
            read_instr_simple(.addr(rand_addr));
        end    

        $finish();
    end
endmodule