`include "../params.svh"

module exec_mem(
    input clk,
    input rst,
    input [`ALEN-1:0] decode_instruction_addr,
    input [4:0] opcode,
    input [4:0] rd,
    input [2:0] funct3,
    input [4:0] rs1,
    input [4:0] rs2,
    input [`XLEN-1:0] rs1_data,
    input [`XLEN-1:0] rs2_data,
    input [6:0] funct7,
    input [31:20] i_imm,
    input [31:12] u_imm,
    
    input input_valid,
    input input_is_mem,
    
    output lsu_prev_stalled,
    input lsu_stall_next,
    output [basic_cache_params::aligned_addr_size-1:0] lsu_addr,
    input lsu_access_fault,
    output lsu_do_load,
    input [`XLEN-1:0] lsu_load_data,
    output lsu_do_store,
    output [`XLEN-1:0] lsu_store_data,
    output [(`XLEN/8)-1:0] lsu_store_mask,

    output wire exec_mem_output_valid,
    output wire exec_mem_exception,
    output wire [`XLEN-1:0] exec_mem_result
);

wire [`ALEN-1:0] memory_addr_comb = $signed(rs1_data) + $signed(i_imm);
wire [basic_cache_params::aligned_addr_size-1:0] cache_line_addr_comb = memory_addr_comb[`ALEN-1 -: basic_cache_params::aligned_addr_size];
wire [basic_cache_params::align_bits-1:0] cache_line_offset_comb = memory_addr_comb[0 +: basic_cache_params::align_bits];
reg [basic_cache_params::align_bits-1:0] cache_line_offset;

always_ff @(posedge clk) begin
    if (input_valid && input_is_mem) begin
        cache_line_offset <= cache_line_offset_comb;
    end
end

enum { 
	SIZE_BYTE = 'b00,
    SIZE_HALF = 'b01,
    SIZE_WORD = 'b10,
    SIZE_DWORD = 'b11
} access_size_e; // Non-constant bits apparently can't be cast to an enum in SV, only enum->int conversions allowed...
wire [1:0] access_size_comb = funct3[1:0];
reg [1:0] access_size;
reg access_unsigned;

always_ff @(posedge clk) begin
    if (input_valid && input_is_mem) begin
        access_size <= access_size_comb;
        access_unsigned <= funct3[2];
    end
end

generate
	if (basic_cache_params::align_bits != 3)
		$error("alignment and extraction code assumes cache_line_offset is 3 bits");
endgenerate

// NOTE: We reject any misaligned access, even if it does not cross the cache line (to simplify detection...)
wire is_read_misaligned = (access_size_comb == SIZE_HALF  && cache_line_offset_comb[0:0])
                       || (access_size_comb == SIZE_WORD  && cache_line_offset_comb[1:0])
                       || (access_size_comb == SIZE_DWORD && cache_line_offset_comb[2:0]);

// Instructions that go directly to the LSU
wire is_load_store = opcode == decode_types::OP_LOAD 
                  || opcode == decode_types::OP_STORE;

// NOTE: We do all this swizzling combinatorially for the loaded data output! This goes right into writeback stage input delay...
wire [7:0] loaded_byte = lsu_load_data[cache_line_offset[2:0] * 8 +: 8];
wire [15:0] loaded_half = lsu_load_data[cache_line_offset[2:1] * 16 +: 16];
wire [31:0] loaded_word = lsu_load_data[cache_line_offset[2:2] * 32 +: 32];
wire [63:0] loaded_dword = lsu_load_data;
logic [`XLEN-1:0] loaded_data;
always_comb begin
    unique case (access_size)
        SIZE_BYTE: loaded_data = access_unsigned ? loaded_byte : {{`XLEN-7{loaded_byte[7]}}, loaded_byte[6:0]};
        SIZE_HALF: loaded_data = access_unsigned ? loaded_half : {{`XLEN-15{loaded_half[15]}}, loaded_half[14:0]};
        SIZE_WORD: loaded_data = access_unsigned ? loaded_word : {{`XLEN-31{loaded_word[31]}}, loaded_word[30:0]};
        SIZE_DWORD: loaded_data = loaded_dword;
        default: loaded_data = 'x;
    endcase
end

assign lsu_prev_stalled = !(input_valid && input_is_mem && is_load_store) || is_read_misaligned;
assign lsu_addr = cache_line_addr_comb;
assign lsu_do_load = opcode == decode_types::OP_LOAD;
assign lsu_do_store = 'b0; // TODO: Stores

assign exec_mem_output_valid = exec_mem_output_valid_single_cycle || !lsu_stall_next;
reg exec_mem_output_valid_single_cycle;
always_ff @(posedge clk) begin
    if (rst)
        exec_mem_output_valid_single_cycle <= '0;
    else if (input_valid && input_is_mem && is_load_store)
        exec_mem_output_valid_single_cycle <= is_read_misaligned;
    else
        exec_mem_output_valid_single_cycle <= input_valid && input_is_mem && !is_load_store;
end   

assign exec_mem_exception = lsu_stall_next ? exec_mem_exception_reg : lsu_access_fault;
assign exec_mem_result = lsu_stall_next ? exec_mem_result_reg : loaded_data;
reg exec_mem_exception_reg;
reg [`XLEN-1:0] exec_mem_result_reg;
always_ff @(posedge clk) begin
    exec_mem_exception_reg <= '0;

    if (is_load_store) begin
        // NOTE: For actual load/stores we only output using those regs in case of misaligned exception, so result is 'x
        //       The other kinds of load/store results come from the load/store unit combinatorially
        exec_mem_exception_reg <= is_read_misaligned;
        exec_mem_result_reg <= 'x;
    end else if (opcode == decode_types::OP_MISC_MEM) begin
        exec_mem_result_reg <= 'x; // NOTE: We don't reorder anything, FENCE is a no-op
    end else begin
        exec_mem_exception_reg <= '1;
        exec_mem_result_reg <= 'x;
    end
end

endmodule