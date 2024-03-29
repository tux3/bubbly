// QSPI Flash reader, runs at the host clock speed!
// Wait for setup_done. Fill addr and hold do_read while you want to keep reading sequentially. On each data_ready, read data.
// To change addr, deassert do_read for a cycle, update addr and re-assert do_read.
//
// After reset, this module initializes the Flash chip to work in continous quad-read mode (XIP).

// The clock edge order is pos clk, pos capture_clk, neg clk, neg capture clk, pos clk, ...

module qspi_flash #(
    parameter USE_SB_IO = 0
) (
    // Logic iface
    input clk,
    input rst,
    input [23:0] addr,
    input do_read,
    output setup_done,
    output reg data_ready,
    output reg [7:0] data,
    // Pins iface
    output sclk,
    output cs,
    input capture_clk,
    inout si, so, wp, hold
);

localparam WRITE_PROTECT_WHEN_IDLE = 1; // Enable write-protect when not in use. Not really necessary.

wire [7:0] supported_qspi_vendor = 'h1F; // Adesto
wire [7:0] supported_qspi_models = 'b100_xxxxx; // AT25SFxxx

reg supports_quad_mode; // True if we saw the right manufacturer/device ID, otherwise we will issue serial Fast Read commands
reg read_data_mode; // True when reading a data byte, false during any other transmission
reg quad_send_mode; // True when {hold, wp, so, si} are used as outputs by the flash chip.
reg [1:0] cs_cooldown; // To respect timings we need to hold cs high at least two cycles before asserting it back down
reg cs_reg;
reg [3:0] setup_counter;
reg [5:0] tx_counter;
reg [0:39] sliding_send_buf;

reg serial_command_sent;

wire is_dummy_byte = (tx_counter[5:4] == 'b0) && quad_send_mode; // For 16 bits (4 clocks) before a quad-read command starts sending data we have high-Z dummy bytes
wire quad_should_send = !cs && quad_send_mode && !is_dummy_byte;
wire switch_to_quad_send_mode = setup_counter == 'h1 && tx_counter == 'h30;

wire si_in, so_in, wp_in, hold_in;

assign cs = cs_reg;
assign sclk = clk; // We set cs on negedge, there'll be enough CS high setup time before the next sclk posedge that we don't need to mask it
assign setup_done = !(|setup_counter);

logic capture_rst;
always @(negedge capture_clk)
    capture_rst <= rst;

generate
if (!USE_SB_IO) begin
	assign si = !cs && !is_dummy_byte ? (setup_counter == '0 && supports_quad_mode ? sliding_send_buf[3] : sliding_send_buf[0]) : 1'bz;
	assign so = quad_should_send ? sliding_send_buf[2] : 1'bz;
	assign wp = (!cs || !WRITE_PROTECT_WHEN_IDLE) ? (quad_send_mode && !is_dummy_byte && cs == 0 ? sliding_send_buf[1] : 1'bz) : 1'b0;
	assign hold = quad_should_send ? sliding_send_buf[0] : 1'bz; // Hold is pulled-high by Flash, we can leave it floating

	assign si_in = si;
	assign so_in = so;
	assign wp_in = wp;
	assign hold_in = hold;
end else begin
	wire si_enable = !cs && !is_dummy_byte;
	wire so_enable = quad_should_send;
	wire wp_enable = quad_should_send || (WRITE_PROTECT_WHEN_IDLE && cs);
	wire hold_enable = quad_should_send;

    wire si_out = setup_counter == '0 && supports_quad_mode ? sliding_send_buf[3] : sliding_send_buf[0];
    wire so_out = sliding_send_buf[2];
	wire wp_out = (!cs && quad_send_mode) ? sliding_send_buf[1] : 1'b0;
	wire hold_out = sliding_send_buf[0];

	SB_IO #(
	    .PIN_TYPE(6'b 1010_01)
	) quad_io[3:0] (
	    .PACKAGE_PIN({si, so, wp, hold}),
	    .OUTPUT_ENABLE({si_enable, so_enable, wp_enable, hold_enable}),
	    .D_OUT_0({si_out, so_out, wp_out, hold_out}),
	    .D_IN_0({si_in, so_in, wp_in, hold_in})
	);
end
endgenerate

// Update setup_counter
always @(negedge capture_clk)
begin
    if (rst) begin
        setup_counter <= 'h6;
    end else if (!setup_done && tx_counter == 0) begin
        if (!supports_quad_mode)
            setup_counter <= 0;
        else
            setup_counter <= setup_counter - 1;
    end
end

// Update serial_command_sent
always @(negedge capture_clk)
begin
    if (rst) begin
        serial_command_sent <= 'h0;
    end else begin
        if (cs || !do_read)
            serial_command_sent <= 'h0;
        else if (tx_counter == 1 && !supports_quad_mode && read_data_mode)
            serial_command_sent <= 'h1;
    end
end

// Update tx_counter and quad_send_mode
always @(negedge capture_clk)
begin
    if (rst) begin
        tx_counter <= 'h08;
        read_data_mode <= 'b0;
        quad_send_mode <= 'b0;
    end else begin
        if (setup_done && !do_read) begin
            tx_counter <= 0;
            read_data_mode <= 'b0;
        end

        else if (tx_counter != 0 && cs_cooldown == 0) begin
            if (switch_to_quad_send_mode)
                quad_send_mode <= 'b1;

            if (quad_send_mode || switch_to_quad_send_mode)
                tx_counter <= tx_counter - 4;
            else
                tx_counter <= tx_counter - 1;
        end else if (tx_counter == 0) begin
            if (!supports_quad_mode) begin
                if (serial_command_sent)
                    tx_counter <= 'h7; // 7 remaining data bits + current bit
                else
                    tx_counter <= 'h30; // 8 opcode + 8*3 addr + 8 dummy bits + read 8 data bits
                read_data_mode <= '1;
            end else if (setup_counter == 'h06)
                tx_counter <= 'h18;
            else if (setup_counter == 'h05)
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

// Prepare data to send
always @(negedge capture_clk)
begin
    if (rst) begin
		sliding_send_buf <= {8'hAB, {32{'x}}}; // Wake opcode
    end else if (tx_counter == 0) begin
        if (!supports_quad_mode)
            if (serial_command_sent)
                sliding_send_buf <= 'x;
            else
                sliding_send_buf <= {8'h0B, addr, {8{'x}}}; // Fast read command, addr and dummy byte
        else if (setup_counter == 'h6)
            sliding_send_buf <= {8'h9F, {32{'x}}}; // Read identification
        else if (setup_counter == 'h5)
            sliding_send_buf <= {8'h06, {32{'x}}}; // Write-enable opcode
        else if (setup_counter == 'h4)
            sliding_send_buf <= {8'h01, 8'b1000_0000, 8'b0000_0010, {16{'x}}}; // Write status register to disable irrelevant protections and set QE bit
        else if (setup_counter == 'h3)
            sliding_send_buf <= {8'h04, {32{'x}}}; // Write-disable opcode
        else if (setup_counter == 'h2)
            sliding_send_buf <= {8'hEB, 32'h00000020}; // Start quad-read in continuous mode
        else if (!read_data_mode)
            sliding_send_buf <= {addr, 8'h20, {8{'x}}};
        else
            sliding_send_buf <= 'x;
    end else if (!cs_reg) begin
        if (quad_send_mode)
            sliding_send_buf <= {sliding_send_buf[4 +: $size(sliding_send_buf)-4], 4'bx};
        else
            sliding_send_buf <= {sliding_send_buf[1 +: $size(sliding_send_buf)-1], 1'bx};
    end
end

// Check chip supports quad-send mode
always @(posedge capture_clk)
begin
    if (capture_rst) begin
        supports_quad_mode <= 'h1;
    end else if (setup_counter == 'h5) begin
        if (tx_counter == 'h08 && data != supported_qspi_vendor)
            supports_quad_mode <= 'h0;
        else if (tx_counter == 'h05 && data[2:0] != supported_qspi_models[7:5])
            supports_quad_mode <= 'h0;
    end
end

// Ensure CS stays up long enough between commands
always @(posedge clk)
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

// Maintain cs
always @(negedge capture_clk)
begin
    if (rst) begin
        cs_reg <= 'h1;
    end else if (!setup_done) begin
        cs_reg <= cs_cooldown != 0;
    end else begin
        cs_reg <= !do_read || cs_cooldown != 0;
    end
end

// Receive data
always @(posedge capture_clk)
begin
    if (capture_rst) begin
        data_ready <= 'b0;
        data <= 'x;
    end else if (setup_done) begin
        data_ready <= tx_counter == 0 && read_data_mode && !cs;
        if (read_data_mode)
            data <= supports_quad_mode ? {data[3:0], hold_in, wp_in, so_in, si_in} : {data[6:0], so_in};
    end else begin
        data_ready <= 'b0;
        data <= {data[6:0], so_in};
    end
end

endmodule
