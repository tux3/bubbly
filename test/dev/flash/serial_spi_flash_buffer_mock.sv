module serial_spi_flash_buffer_mock #(
    parameter BUFFER_SIZE = 1
) (
    input cs, sclk,
    output logic capture_clk,
    inout si, so, wp, hold,
    input [BUFFER_SIZE-1:0] buffer
);
timeunit 100ns;
timeprecision 10ns;

initial begin
    capture_clk = 0;
    #0.8;
    forever begin
        capture_clk = 1;
        #0.4 capture_clk = 0;
        #0.6;
    end
end

typedef enum { CMD_WAKEUP = 'hAB, CMD_FAST_READ = 'h0B, CMD_READ_ID = 'h9F } commands;
enum { DISABLED, ADDR_1, ADDR_2, ADDR_3, DUMMY, SEND } send_mode;

logic setup_done = 0;

logic [2:0] recv_count;
logic [7:0] recv_buf;
wire recv_got_byte = recv_count == 0;

logic [8:0] addr;
wire should_send = !cs && send_mode == SEND;
int send_pos;

logic send_id;
int send_id_pos;
wire [23:0] chip_identifier = 'h010000;
wire [7:0] reply_byte = buffer[addr*8 +: 8];

assign si = 'z;
assign so = send_id ? chip_identifier[send_id_pos] : (should_send ? reply_byte[send_pos] : 'z);
assign wp = 'z;
assign hold = 'z;

always @(negedge sclk, posedge cs) begin
    if (cs) begin
        addr <= 'x;
        recv_count <= 0;
        recv_buf <= 'x;
    end else begin
        recv_buf <= {recv_buf, si};
        recv_count <= recv_count + 1;
    end
end

always @(negedge sclk, posedge cs) begin
    if (cs) begin
        send_pos <= $bits(reply_byte)-1;
        send_id_pos <= $bits(chip_identifier)-1;
    end else begin
        if (should_send && send_pos > 0)
            send_pos <= send_pos -1;
        else
            send_pos <= $bits(reply_byte)-1;

        if (send_id) begin
            if (send_id_pos > 0)
                send_id_pos <= send_id_pos - 1;
            else
                send_id_pos <= $bits(chip_identifier)-1;
        end
    end
end

always @(posedge recv_got_byte, posedge cs) begin
    if (cs) begin
        send_mode <= DISABLED;
        send_id <= 0;
    end else if (send_mode == SEND) begin
        addr <= addr + 1;
    end else if (send_mode > DISABLED) begin
        send_mode <= send_mode.next();

        if (send_mode >= ADDR_1 && send_mode <= ADDR_3)
            addr <= {addr, recv_buf};
    end else if (send_mode == DISABLED && recv_got_byte) begin
        //$display("Got command: 0x%h", recv_buf);
        if (recv_buf == CMD_READ_ID) begin
            send_id <= 1;
        end else if (recv_buf == CMD_FAST_READ) begin
            setup_done <= 1;
            send_mode <= ADDR_1;
        end else if (recv_buf == CMD_WAKEUP || recv_buf === 'x) begin
            // OK
        end else begin
            $error("[%t] Received unknown command %h", $time, recv_buf);
        end
    end
end

endmodule