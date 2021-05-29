// SPI Slave module
// - Read recv_data when recv_ready is high.
// - Write send_data when send_ready is high, and keep it stable when send_ready is low.

module spi_slave(
    input ext_clk,
    input rst,
    input sclk,
    input mosi,
    output miso,
    input ss,
    input [7:0] send_data,
    output logic send_ready,
    output logic [7:0] recv_data,
    output logic recv_ready
);

// ext_clk domain registers
reg recv_ready_sync1;
reg recv_ready_sync2;
reg recv_already_read;
reg ss_idle_sync1;
reg ss_idle_sync2;

// sclk domain registers
reg [2:0] txed_bits_count;
reg [7:0] recv_buf;
reg [7:0] send_buf;
wire tx_done_internal = txed_bits_count == 'b000;
wire send_ready_internal = ss_idle_sync2 || tx_done_internal; // If master doesn't release ss, we still have time to output send_ready on the same cycle as recv_ready and wait for a new send_data to stabilize


wire rst_or_ss = rst || ss_idle_sync2;

assign miso = !ss && send_buf[3'b111 - txed_bits_count];

// Register outputs
always_ff @(posedge ext_clk, posedge rst) begin
    if (rst) begin
        recv_data <= 'x;
        recv_ready <= '0;
        send_ready <= '0;
    end else begin
        recv_data <= recv_buf;
        recv_ready <= recv_ready_sync2 && recv_ready_sync1 && tx_done_internal && !recv_already_read;
        send_ready <= ss_idle_sync2 || recv_ready;
    end
end

// Shift in incoming data
always @(posedge sclk, posedge rst)
begin
    if (rst) begin
        recv_buf <= 0;
    end else if (!ss_idle_sync2) begin
        recv_buf <= {recv_buf[6:0], mosi};
    end
end

// Move in outgoing data
always @(negedge ext_clk, posedge rst)
begin
    if (rst) begin
        send_buf <= 0;
    end else begin
        send_buf <= send_data;
    end
end

// Keep transfered bits count (reset if ss abruptly goes up)
always @(negedge sclk, posedge rst)
begin
    if (rst) begin
        txed_bits_count <= 0;
    end else if (ss_idle_sync2) begin
        txed_bits_count <= 0;
    end else if (!ss) begin
        txed_bits_count <= txed_bits_count + 1;
    end
end

// Output recv_ready signal
always @(posedge ext_clk, posedge rst)
begin
    if (rst) begin
        recv_ready_sync1 <= 1;
        recv_ready_sync2 <= 1;
        recv_already_read <= 1;
    end else begin
        recv_ready_sync1 <= tx_done_internal;
        recv_ready_sync2 <= recv_ready_sync1 && tx_done_internal;
        recv_already_read <= recv_ready_sync2 && recv_ready_sync1 && tx_done_internal;
    end
end

// Sync ss_inactive. If we have any doubt of instability, immediately assume we are not idle
always @(posedge ext_clk)
begin
    ss_idle_sync1 <= ss;
    ss_idle_sync2 <= ss == ss_idle_sync1 ? ss_idle_sync1 : ss_idle_sync2;
end

endmodule
