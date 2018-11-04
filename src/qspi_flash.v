// QSPI Flash reader, runs at the host clock speed!
// Wait for setup_done. Fill addr and hold do_read while you want to keep reading sequentially. On each data_ready, read data.
// To change addr, deassert do_read for a cycle, update addr and re-assert do_read.
//
// After reset, this module initializes the Flash chip to work in continous quad-read mode (XIP).

module qspi_flash(
    // Logic iface
    input clk,
    input rst,
    input [23:0] addr,
    input do_read,
    output setup_done,
    output reg data_ready,
    output reg [7:0] data,
    // Pins iface
    output reg cs,
    output sclk,
    inout si,
    inout so,
    inout wp,
    inout hold
);

localparam WRITE_PROTECT_WHEN_IDLE = 0; // Enable write-protect when not in use. Not really necessary.

reg read_data_mode; // True when reading a data byte, false during any other transmission
reg quad_send_mode; // True when {hold, wp, so, si} are used as outputs by the flash chip.
reg [1:0] cs_cooldown; // To respect timings we need to hold cs high at least two cycles before asserting it back down
reg [3:0] setup_counter;
reg [5:0] tx_counter;
reg [39:0] send_buf;

assign setup_done = !(|setup_counter);

wire is_dummy_byte = tx_counter < 16 && quad_send_mode; // For 16 bits (4 clocks) before a quad-read command starts sending data we have high-Z dummy bytes

assign sclk = !cs && clk;
assign si = !cs && !is_dummy_byte ? (setup_counter <= 1 ? send_buf[tx_counter - 16] : send_buf[tx_counter]) : 1'bz;
assign so = (!cs && quad_send_mode && !is_dummy_byte) ? send_buf[tx_counter+1-16] : 1'bz;
assign wp = (!cs || !WRITE_PROTECT_WHEN_IDLE) ? (quad_send_mode && !is_dummy_byte && cs == 0 ? send_buf[tx_counter+2-16] : 1'bz) : 1'b0;
assign hold = (!cs && quad_send_mode && !is_dummy_byte) ? send_buf[tx_counter+3-16] : 1'bz; // Hold is pulled-high by Flash, we can leave it floating

// Update tx_counter and quad_send_mode
always @(negedge clk, posedge rst)
begin
    if (rst) begin
        tx_counter <= 'h08;
        read_data_mode <= 'b0;
        quad_send_mode = 'b0;
    end else begin
        if (tx_counter != 0 && cs_cooldown == 0) begin
            if (setup_counter == 'h1 && tx_counter == 'h30)
                quad_send_mode = 'b1;

            if (quad_send_mode)
                tx_counter <= tx_counter - 4;
            else
                tx_counter <= tx_counter - 1;
        end else if (setup_done && !do_read) begin
            tx_counter <= 0;
            read_data_mode <= 'b0;
        end else if (tx_counter == 0) begin
			if (setup_counter == 'h05)
                tx_counter <= 'h08;
            else if (setup_counter == 'h04)
                tx_counter <= 'h18;
            else if (setup_counter == 'h03)
                tx_counter <= 'h08;
            else if (setup_counter == 'h02)
                tx_counter <= 'h38; // 8 opcode + 8*4 addr/mode + 4*4 dummy cycles
            else if (cs_cooldown) begin
                tx_counter <= 'h30; // 8*4 addr/mode + 4*4 dummy cycle
            end else begin
                tx_counter <= 'h4; // 2*4 data bits, no delay
                read_data_mode <= 'b1;
            end
        end
    end
end


// Update setup_counter
always @(negedge clk, posedge rst)
begin
    if (rst) begin
        setup_counter <= 'h5;
    end else if (!setup_done) begin
        if (tx_counter == 0)
            setup_counter <= setup_counter - 1;
    end
end

// Ensure CS stays up long enough between commands
always @(posedge clk, posedge rst)
begin
    if (rst) begin
        cs_cooldown <= 'b00;
    end else begin
        if (cs_cooldown != 0)
            cs_cooldown <= cs_cooldown - 1;
        if (!setup_done && tx_counter == 0)
            cs_cooldown <= 'b10;
        else if (setup_done && !do_read)
            cs_cooldown <= 'b01;
    end
end

// Prepare data to send
always @(negedge clk, posedge rst)
begin
    if (rst) begin
		send_buf <= {8'hAB}; // Wake opcode
    end else if (tx_counter == 0) begin
		if (setup_counter == 'h5)
            send_buf <= 'h06; // Write-enable opcode
        else if (setup_counter == 'h4)
            send_buf <= {8'h01, 8'b1000_0000, 8'b0000_0010}; // Write status register to disable irrelevant protections and set QE bit
        else if (setup_counter == 'h3)
            send_buf <= {8'h04}; // Write-disable opcode
        else if (setup_counter == 'h2)
            send_buf <= {8'hEB, 32'h00000020}; // Start quad-read in continuous mode
        else if (!read_data_mode)
            send_buf <= {addr, 8'h20};
        else
            send_buf <= 40'bZ;
    end
end

// Maintain cs
always @(negedge clk, posedge rst)
begin
    if (rst) begin
        cs <= rst;
    end else if (!setup_done) begin
        cs <= cs_cooldown != 0;
    end else begin
        cs <= !do_read || cs_cooldown != 0;
    end
end

// Receive data
always @(posedge clk, posedge rst)
begin
    if (rst) begin
        data_ready <= 'b0;
        data <= 'b0;
    end else if (setup_done) begin
        data_ready <= tx_counter == 0 && read_data_mode && !cs;
        if (read_data_mode)
            data <= {data[3:0], hold, wp, so, si};
    end
end

endmodule
