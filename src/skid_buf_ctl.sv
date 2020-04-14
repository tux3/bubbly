// This is a lightweight skid buffer, inputs are directly connected to outputs when possible, combinatorially.
// This slightly increases the delay, but it saves a buffer and a cycle after a fetch bubble.
// The actual buffers are stored in skid_buf_data instances
module skid_buf_ctl (
    input clk,
    input rst,
    input prev_stalled,
    input next_stalled,
    output buf_full,
    output logic stall_prev,
    output logic stall_next,
);

enum { EMPTY, FULL } state;
assign buf_full = state == FULL;
assign stall_prev = state == FULL; // Not really comb: state==FULL will be a single register of the FSM state

// Note how stall_prev is comb, so we can complete a handshake with prev immediately, but all our outputs are registered
always_ff @(posedge clk) begin
    if (rst) begin
        stall_next <= '1;
    end else begin
        stall_next <= (state == FULL) ? '0 : prev_stalled;
    end
end    

always_ff @(posedge clk) begin
    if (rst) begin
        state <= EMPTY;
    end else unique case (state)
        EMPTY: begin
            if (next_stalled && !prev_stalled)
                state <= FULL;
        end
        FULL: begin
            if (!next_stalled)
                state <= EMPTY;
        end
    endcase
end

endmodule
