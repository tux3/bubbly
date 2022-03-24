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
    input [11:0] s_imm,

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
    output wire [3:0] exec_mem_trap_cause,
    output logic [`ALEN-1:0] exec_mem_fault_addr,
    output wire [`XLEN-1:0] exec_mem_result
);

// Instructions that go directly to the LSU
wire is_load_store = opcode == opcodes::LOAD
                  || opcode == opcodes::STORE
                  || opcode == opcodes::AMO;
wire amo_op_store_cycle = '0;
wire is_amo = opcode == opcodes::AMO;
wire amo_is_lr = funct7[6:2] == 'b00010;
wire amo_is_sc = funct7[6:2] == 'b00011;
wire store_bit = (opcode[3] && !opcode[1]) // when input_is_mem, that's STORE || STORE_FP
                 || (is_amo && (amo_is_sc || amo_op_store_cycle));

wire [11:0] mem_imm = is_amo ? '0 : {i_imm[31:25], store_bit ? s_imm[4:0] : i_imm[24:20]};
wire [`ALEN-1:0] memory_addr_comb = $signed(rs1_data) + $signed(mem_imm);
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
wire is_access_misaligned = (access_size_comb == SIZE_HALF  && cache_line_offset_comb[0:0])
                         || (access_size_comb == SIZE_WORD  && cache_line_offset_comb[1:0])
                         || (access_size_comb == SIZE_DWORD && cache_line_offset_comb[2:0]);

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

integer mask_idx;
logic [`XLEN-1:0] store_data;
logic [(`XLEN/8)-1:0] store_mask;

assign lsu_prev_stalled = !(input_valid && input_is_mem && is_load_store)
                        || (is_amo && amo_is_sc && !amo_has_reservation)
                        || is_access_misaligned;
assign lsu_addr = cache_line_addr_comb;
assign lsu_do_load = !store_bit;
assign lsu_do_store = store_bit;
assign lsu_store_data = store_data;
assign lsu_store_mask = store_mask;

always_comb begin
    mask_idx = 'x;
    unique case (access_size_comb)
        SIZE_BYTE: for (mask_idx=0; mask_idx*8<`XLEN; mask_idx+=1) begin
                       store_data[mask_idx*8 +: 8] = rs2_data[7:0];
                       store_mask[mask_idx*1 +: 1] = {1{cache_line_offset_comb[2:0] == mask_idx}};
                   end
        SIZE_HALF: for (mask_idx=0; mask_idx*16<`XLEN; mask_idx+=1) begin
                       store_data[mask_idx*16 +: 16] = rs2_data[15:0];
                       store_mask[mask_idx*2 +: 2] = {2{cache_line_offset_comb[2:1] == mask_idx}};
                   end
        SIZE_WORD: for (mask_idx=0; mask_idx*32<`XLEN; mask_idx+=1) begin
                       store_data[mask_idx*32 +: 32] = rs2_data[31:0];
                       store_mask[mask_idx*4 +: 4] = {4{cache_line_offset_comb[2] == mask_idx}};
                   end
        SIZE_DWORD: begin
            store_data = rs2_data;
            store_mask = {8{1'b1}};
        end
        default: store_mask = 'x;
    endcase
end

reg amo_has_reservation;
always_ff @(posedge clk) begin
    if (rst)
        amo_has_reservation <= '0;
    else if (input_valid && input_is_mem) begin
        if (store_bit)
            amo_has_reservation <= '0;
        else if (is_amo && amo_is_lr)
            amo_has_reservation <= !is_access_misaligned;
    end
end

reg exec_mem_output_valid_single_cycle;
assign exec_mem_output_valid = exec_mem_output_valid_single_cycle || !lsu_stall_next;
always_ff @(posedge clk) begin
    if (rst) begin
        exec_mem_output_valid_single_cycle <= '0;
    end else if (input_valid && input_is_mem && is_load_store) begin
        exec_mem_output_valid_single_cycle <= is_access_misaligned
                                          || (is_amo && amo_is_sc && !amo_has_reservation);
    end else begin
        exec_mem_output_valid_single_cycle <= input_valid && input_is_mem && !is_load_store;
    end
end

// Non LR AMO ops end with a write, so we can't just return loaded_data (that's 'x for a store!)
reg had_amo_write;
always_ff @(posedge clk) begin
    if (rst)
        had_amo_write <= '0;
    else if (input_valid && input_is_mem)
        had_amo_write <= is_amo && !amo_is_lr;
end

reg exec_mem_exception_reg;
reg [3:0] exec_mem_trap_cause_reg;
reg [`XLEN-1:0] exec_mem_result_reg;
assign exec_mem_exception = lsu_stall_next ? exec_mem_exception_reg : lsu_access_fault;
assign exec_mem_trap_cause = lsu_stall_next ? exec_mem_trap_cause_reg : trap_causes::EXC_LOAD_ACCESS_FAULT;
assign exec_mem_result = (lsu_stall_next || had_amo_write) ? exec_mem_result_reg : loaded_data;
always_ff @(posedge clk) begin
    exec_mem_exception_reg <= '0;
    exec_mem_trap_cause_reg <= 'x;
    exec_mem_fault_addr <= memory_addr_comb;

    unique if (is_load_store && is_amo) begin
        // NOTE: For actual load/stores we only output using those regs in case of misaligned exception, so result is 'x
        //       The other kinds of load/store results come from the load/store unit combinatorially
        exec_mem_exception_reg <= is_access_misaligned;
        exec_mem_trap_cause_reg <= store_bit ? trap_causes::EXC_STORE_ADDR_MISALIGNED : trap_causes::EXC_LOAD_ADDR_MISALIGNED;
        if (is_amo && amo_is_sc)
            exec_mem_result_reg <= !amo_has_reservation;
        else
            exec_mem_result_reg <= 'x;
    end else if (is_load_store && !is_amo) begin
        // NOTE: For actual load/stores we only output using those regs in case of misaligned exception, so result is 'x
        //       The other kinds of load/store results come from the load/store unit combinatorially
        exec_mem_exception_reg <= is_access_misaligned;
        exec_mem_trap_cause_reg <= store_bit ? trap_causes::EXC_STORE_ADDR_MISALIGNED : trap_causes::EXC_LOAD_ADDR_MISALIGNED;
        exec_mem_result_reg <= 'x;
    end else if (opcode == opcodes::MISC_MEM) begin
        // NOTE: Everything is already serialized, regular data FENCE is a no-op (but FENCE.I and others are not!)
        exec_mem_exception_reg <= funct3 != 'b000;
        exec_mem_trap_cause_reg <= trap_causes::EXC_ILLEGAL_INSTR;
        exec_mem_result_reg <= 'x;
    end else begin
        exec_mem_exception_reg <= '1;
        exec_mem_trap_cause_reg <= trap_causes::EXC_ILLEGAL_INSTR;
        exec_mem_result_reg <= 'x;
    end
end

endmodule