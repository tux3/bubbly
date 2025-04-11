`include "core/params.svh"

`define EXEC_DIV_LOG2_CASE(N) else if (n[`XLEN-1:N] == 1'b1) exec_div_log2 = N+1

function [$clog2(`XLEN):0] exec_div_log2(input [`XLEN-1:0] n);
    unique0 if ('0) begin end
    `EXEC_DIV_LOG2_CASE(63); `EXEC_DIV_LOG2_CASE(62); `EXEC_DIV_LOG2_CASE(61); `EXEC_DIV_LOG2_CASE(60);
    `EXEC_DIV_LOG2_CASE(59); `EXEC_DIV_LOG2_CASE(58); `EXEC_DIV_LOG2_CASE(57); `EXEC_DIV_LOG2_CASE(56);
    `EXEC_DIV_LOG2_CASE(55); `EXEC_DIV_LOG2_CASE(54); `EXEC_DIV_LOG2_CASE(53); `EXEC_DIV_LOG2_CASE(52);
    `EXEC_DIV_LOG2_CASE(51); `EXEC_DIV_LOG2_CASE(50); `EXEC_DIV_LOG2_CASE(49); `EXEC_DIV_LOG2_CASE(48);
    `EXEC_DIV_LOG2_CASE(47); `EXEC_DIV_LOG2_CASE(46); `EXEC_DIV_LOG2_CASE(45); `EXEC_DIV_LOG2_CASE(44);
    `EXEC_DIV_LOG2_CASE(43); `EXEC_DIV_LOG2_CASE(42); `EXEC_DIV_LOG2_CASE(41); `EXEC_DIV_LOG2_CASE(40);
    `EXEC_DIV_LOG2_CASE(39); `EXEC_DIV_LOG2_CASE(38); `EXEC_DIV_LOG2_CASE(37); `EXEC_DIV_LOG2_CASE(36);
    `EXEC_DIV_LOG2_CASE(35); `EXEC_DIV_LOG2_CASE(34); `EXEC_DIV_LOG2_CASE(33); `EXEC_DIV_LOG2_CASE(32);
    `EXEC_DIV_LOG2_CASE(31); `EXEC_DIV_LOG2_CASE(30); `EXEC_DIV_LOG2_CASE(29); `EXEC_DIV_LOG2_CASE(28);
    `EXEC_DIV_LOG2_CASE(27); `EXEC_DIV_LOG2_CASE(26); `EXEC_DIV_LOG2_CASE(25); `EXEC_DIV_LOG2_CASE(24);
    `EXEC_DIV_LOG2_CASE(23); `EXEC_DIV_LOG2_CASE(22); `EXEC_DIV_LOG2_CASE(21); `EXEC_DIV_LOG2_CASE(20);
    `EXEC_DIV_LOG2_CASE(19); `EXEC_DIV_LOG2_CASE(18); `EXEC_DIV_LOG2_CASE(17); `EXEC_DIV_LOG2_CASE(16);
    `EXEC_DIV_LOG2_CASE(15); `EXEC_DIV_LOG2_CASE(14); `EXEC_DIV_LOG2_CASE(13); `EXEC_DIV_LOG2_CASE(12);
    `EXEC_DIV_LOG2_CASE(11); `EXEC_DIV_LOG2_CASE(10); `EXEC_DIV_LOG2_CASE(9);  `EXEC_DIV_LOG2_CASE(8);
    `EXEC_DIV_LOG2_CASE(7);  `EXEC_DIV_LOG2_CASE(6);  `EXEC_DIV_LOG2_CASE(5);  `EXEC_DIV_LOG2_CASE(4);
    `EXEC_DIV_LOG2_CASE(3);  `EXEC_DIV_LOG2_CASE(2);  `EXEC_DIV_LOG2_CASE(1);  `EXEC_DIV_LOG2_CASE(0);
    else exec_div_log2 = 'x;
endfunction

// We do not handle b_in == 0 or signed overflow special cases, user must handle those manually
module exec_div(
    input clk,
    input rst,
    input [`XLEN-1:0] a_in,
    input [`XLEN-1:0] b_in,
    // NOTE: If do_rem, we really output the re-multiplied (q * b_in) result in q_out
    output logic [`XLEN-1:0] q_out,
    // do_rem must be held valid until output_valid falling edge, even while !input_valid
    input do_rem,
    input input_valid,
    output logic output_valid
);
    logic [5:0] counter;
    wire [5:0] counter_max = do_rem ? 'h1F : 'h1D;
    always_ff @(posedge clk) begin
        if (rst) begin
            counter <= '0;
        end else if (input_valid) begin
            counter <= 1;
        end else if (counter == counter_max) begin
            counter <= 0;
        end else if (|counter) begin
            counter <= counter + 1;
        end
    end

    logic [65:0] mult_a;
    logic [127:0] mult_b;
    wire [127:0] mult_r;
    fixp_mult mult(.clk, .a(mult_a), .b(mult_b), .r(mult_r));

    logic [127:0] a;
    logic [127:0] b;
    logic [63:0] b_in_buf;
    wire [$clog2(`XLEN):0] b_log2 = exec_div_log2(b);
    always_ff @(posedge clk) begin
        if (rst) begin
            a <= 'x;
            b <= 'x;
            b_in_buf <= 'x;
        end else if (input_valid) begin
            a <= a_in;
            b <= b_in;
            b_in_buf <= b_in;
        end else if (counter == 'h1) begin
            a <= a << (64 - b_log2);
            b <= b << (64 - b_log2);
        end
    end

    logic [127:0] x;
    always_ff @(posedge clk) begin
        if (rst) begin
            x <= 'x;
        end else if (counter == 'h1) begin
            mult_a <= 'h1e1e1e1e1e1e1e1e1;
            mult_b <= b << (64 - b_log2);
            x <= 'x;
        end else if (counter == 'h3) begin
            // Initialize with approximate reciprocal 48/17 - 32/17 * b
            x <= 'h2d2d2d2d2d2d2d2d2 - mult_r;
            mult_a <= b;
            mult_b <= 'h2d2d2d2d2d2d2d2d2 - mult_r;
        end else if (counter == 'h1B) begin
            x <= 'x;
            mult_a <= x + mult_r;
            mult_b <= a;
        end else if (counter == 'h1D) begin
            // The `remultiplied = q * b` step for the REM (caller does the `rem = a - remultiplied` op)
            mult_a <= {mult_r[64 +: 64], 1'b0};
            mult_b <= {b_in_buf, 63'b0};
        end else if (counter[1:0] == 'b11) begin
            x <= x + mult_r;
            mult_a <= b;
            mult_b <= x + mult_r;
        end else begin
            mult_a <= x;
            mult_b <= 'h10000000000000000 - mult_r;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            output_valid <= '0;
            q_out <= 'x;
        end else begin
            output_valid <= counter == counter_max;
            if (counter == counter_max)
                q_out <= do_rem ? mult_r[0 +: 64] : mult_r[64 +: 64];
            else
                q_out <= 'x;
        end
    end

    `ifndef SYNTHESIS
    always @(posedge clk) begin
        assert property (input_valid |-> !$isunknown(a_in) && !$isunknown(b_in));
        assert property (input_valid |-> counter == 0);
    end
    `endif
endmodule
