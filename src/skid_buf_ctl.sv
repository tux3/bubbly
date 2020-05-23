// Simple skid buffer. The actual buffers are stored in skid_buf_data instances
module skid_buf_ctl (
    input clk,
    input rst,
    input prev_stalled,
    input next_stalled,
    output buf_full,
    output reg stall_prev,
    output reg stall_next
);

enum { EMPTY, FULL } state;
assign buf_full = state == FULL;

always_ff @(posedge clk) begin
    if (rst) begin
        stall_prev <= '0;
    end else if (!prev_stalled && next_stalled && !stall_next && !stall_prev) begin
        stall_prev <= '1;
    end else begin
        stall_prev <= state==FULL && next_stalled;
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        stall_next <= '1;
    end else begin
        stall_next <= (state == FULL || !prev_stalled) ? '0 : stall_next||!next_stalled;
    end
end    

always_ff @(posedge clk) begin
    if (rst) begin
        state <= EMPTY;
    end else unique case (state)
        EMPTY: begin
            if (!prev_stalled && next_stalled && !stall_next)
                state <= FULL;
        end
        FULL: begin
            if (!next_stalled)
                state <= EMPTY;
        end
    endcase
end

`ifndef SYNTHESIS
always @(posedge clk) begin
    assert property (state == EMPTY && !rst |-> !stall_prev); // Avoid underrun
    assert property (state == FULL |-> stall_prev && !stall_next); // Avoid overrun
    assert property (prev_stalled && !next_stalled && state == EMPTY |=> stall_next); // Ensure we don't output garbage if we have no inputs for next cycle
end
`endif

endmodule
