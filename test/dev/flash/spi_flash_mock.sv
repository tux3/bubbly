module qspi_flash_mock(
    input cs, sclk,
    inout si, so, wp, hold
);

typedef enum { CMD_QUAD_READ = 'hEB } commands;
enum { DISABLED, ADDR_1, ADDR_2, ADDR_3, MODE, DUMMY_1, DUMMY_2, SEND } quad_mode;

logic setup_done = 0;

logic [2:0] recv_count;
logic [7:0] recv_buf;
wire recv_got_byte = recv_count == 0;

logic [23:0] addr;
logic send_pos = 0;
wire should_send = !cs && quad_mode == SEND;

wire [7:0] reply_byte = addr[0 +: 8] ^ addr[8 +: 8] ^ addr[16 +: 8];

assign si = should_send ? reply_byte[4*recv_got_byte] : 'z;
assign so = should_send ? reply_byte[4*recv_got_byte+1] : 'z;
assign wp = should_send ? reply_byte[4*recv_got_byte+2] : 'z;
assign hold = should_send ? reply_byte[4*recv_got_byte+3] : 'z;

always @(posedge sclk, posedge cs) begin
    if (cs) begin
        addr <= 'x;
        send_pos <= 0;
        recv_count <= 0;
        recv_buf <= 'x;
    end else if (quad_mode > DISABLED) begin
        recv_buf <= {recv_buf, hold, wp, so, si};
        recv_count <= recv_count + 4;
    end else if (quad_mode == DISABLED) begin
        recv_buf <= {recv_buf, si};
        recv_count <= recv_count + 1;
    end
end

always @(posedge recv_got_byte, posedge cs) begin
    if (cs) begin
        quad_mode <= setup_done ? ADDR_1 : DISABLED;
        send_pos <= 1;
    end else if (quad_mode == SEND) begin
        addr <= addr + 1;
    end else if (quad_mode > DISABLED) begin
        quad_mode <= quad_mode.next();

        if (quad_mode >= ADDR_1 && quad_mode <= ADDR_3)
            addr <= {addr, recv_buf};
    end else if (quad_mode == DISABLED) begin
        //$display("Got command: 0x%h", recv_buf);
        if (recv_got_byte && recv_buf == CMD_QUAD_READ) begin
            setup_done <= 1;
            quad_mode <= ADDR_1;
        end
    end
end

endmodule