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

    output logic lsu_prev_stalled,
    input lsu_stall_next,
    output [basic_cache_params::aligned_addr_size-1:0] lsu_addr,
    input lsu_access_fault,
    output lsu_do_load,
    input [`XLEN-1:0] lsu_load_data,
    output lsu_do_store,
    output [`XLEN-1:0] lsu_store_data,
    output [(`XLEN/8)-1:0] lsu_store_mask,

    output logic exec_mem_output_valid,
    output logic exec_mem_exception,
    output logic [3:0] exec_mem_trap_cause,
    output logic [`ALEN-1:0] exec_mem_fault_addr,
    output logic [`XLEN-1:0] exec_mem_result
);

reg amo_op_store_cycle;

// Instructions that go directly to the LSU
wire is_load_store = opcode == opcodes::LOAD
                  || opcode == opcodes::STORE
                  || opcode == opcodes::AMO;
wire is_amo = opcode == opcodes::AMO;
wire amo_is_lr = funct7[6:2] == 'b00010;
wire amo_is_sc = funct7[6:2] == 'b00011;
wire amo_is_op = funct7[3] == 'b0;
wire store_bit = (opcode[3] && !opcode[1]) // when input_is_mem, that's STORE || STORE_FP
                 || (is_amo && amo_is_sc )
                 || amo_op_store_cycle;

wire [11:0] mem_imm = is_amo ? '0 : {i_imm[31:25], store_bit ? s_imm[4:0] : i_imm[24:20]};
wire [`ALEN-1:0] memory_addr_comb = $signed(rs1_data) + $signed(mem_imm);
wire [basic_cache_params::aligned_addr_size-1:0] cache_line_addr_comb = memory_addr_comb[`ALEN-1 -: basic_cache_params::aligned_addr_size];
reg [basic_cache_params::aligned_addr_size-1:0] cache_line_addr;
wire [basic_cache_params::align_bits-1:0] cache_line_offset_comb = memory_addr_comb[0 +: basic_cache_params::align_bits];
reg [basic_cache_params::align_bits-1:0] cache_line_offset;

always_ff @(posedge clk) begin
    if (rst) begin
        cache_line_addr <= 'x;
        cache_line_offset <= 'x;
    end else if (input_valid && input_is_mem) begin
        cache_line_addr <= cache_line_addr_comb;
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

// NOTE: We don't care that this read goes out of bounds, we've checked alignment, so we never actually use the OOB data
wire [31:0] loaded_uword = lsu_load_data[cache_line_offset[2:0] * 8 +: 32];
logic [`XLEN-1:0] loaded_data;
always_comb begin
    unique case (access_size)
        SIZE_BYTE: loaded_data = access_unsigned ? loaded_uword[7:0] : {{`XLEN-7{loaded_uword[7]}}, loaded_uword[6:0]};
        SIZE_HALF: loaded_data = access_unsigned ? loaded_uword[15:0] : {{`XLEN-15{loaded_uword[15]}}, loaded_uword[14:0]};
        SIZE_WORD: loaded_data = access_unsigned ? loaded_uword[31:0] : {{`XLEN-31{loaded_uword[31]}}, loaded_uword[30:0]};
        SIZE_DWORD: loaded_data = lsu_load_data[63:0];
        default: loaded_data = 'x;
    endcase
end

integer mask_idx;
logic [`XLEN-1:0] store_data;
logic [(`XLEN/8)-1:0] store_mask;

assign lsu_addr = amo_op_store_cycle ? cache_line_addr : cache_line_addr_comb;
assign lsu_do_load = !store_bit;
assign lsu_do_store = store_bit;
assign lsu_store_data = store_data;
assign lsu_store_mask = store_mask;

reg had_amo_write; // Non LR AMO ops end with a write, so we can't just return loaded_data (that's 'x for a store!)
reg waiting_amo_op_load;
always_ff @(posedge clk) begin
    if (rst) begin
        had_amo_write <= '0;
        waiting_amo_op_load <= '0;
        amo_op_store_cycle <= '0;
    end else if (input_valid && input_is_mem) begin
        had_amo_write <= is_amo && !amo_is_lr && !is_access_misaligned;
        waiting_amo_op_load <= is_amo && amo_is_op && !is_access_misaligned;
        amo_op_store_cycle <= '0;
    end else if (!lsu_stall_next) begin
        waiting_amo_op_load <= '0;
        amo_op_store_cycle <= waiting_amo_op_load;
    end else if (amo_op_store_cycle) begin
        amo_op_store_cycle <= '0;
    end
end

logic [4:0] amo_op_reg;
logic [`XLEN-1:0] amo_op_store_data;
always_ff @(posedge clk) begin
    if (rst) begin
        amo_op_reg <= 'x;
        amo_op_store_data <= 'x;
    end else if (input_valid && input_is_mem) begin
        amo_op_reg <= is_amo && amo_is_op ? funct7[6:2] : 'x;
        amo_op_store_data <= is_amo && amo_is_op ? rs2_data : 'x;
    end else if (waiting_amo_op_load && !lsu_stall_next) begin
        unique case (amo_op_reg)
            'b00001: amo_op_store_data <= amo_op_store_data; // AMOSWAP
            'b00000: amo_op_store_data <= amo_op_store_data + loaded_data; // AMOADD
            'b00100: amo_op_store_data <= amo_op_store_data ^ loaded_data; // AMOXOR
            'b01100: amo_op_store_data <= amo_op_store_data & loaded_data; // AMOAND
            'b01000: amo_op_store_data <= amo_op_store_data | loaded_data; // AMOOR
            'b10000: amo_op_store_data <= ($signed(amo_op_store_data) < $signed(loaded_data))
                                        ? amo_op_store_data : loaded_data; // AMOMIN
            'b10100: amo_op_store_data <= ($signed(amo_op_store_data) > $signed(loaded_data))
                                        ? amo_op_store_data : loaded_data; // AMOMAX
            'b11000: amo_op_store_data <= amo_op_store_data < loaded_data
                                        ? amo_op_store_data : loaded_data; // AMOMINU
            'b11100: amo_op_store_data <= amo_op_store_data > loaded_data
                                        ? amo_op_store_data : loaded_data; // AMOMAXU
            default: amo_op_store_data <= 'x;
        endcase
    end
end

always_comb begin
    mask_idx = 'x;
    unique case (amo_op_store_cycle ? access_size : access_size_comb)
        SIZE_BYTE: for (mask_idx=0; mask_idx*8<`XLEN; mask_idx+=1) begin
                       store_data[mask_idx*8 +: 8] = rs2_data[7:0];
                       store_mask[mask_idx*1 +: 1] = {1{cache_line_offset_comb[2:0] == mask_idx}};
                   end
        SIZE_HALF: for (mask_idx=0; mask_idx*16<`XLEN; mask_idx+=1) begin
                       store_data[mask_idx*16 +: 16] = rs2_data[15:0];
                       store_mask[mask_idx*2 +: 2] = {2{cache_line_offset_comb[2:1] == mask_idx}};
                   end
        SIZE_WORD: for (mask_idx=0; mask_idx*32<`XLEN; mask_idx+=1) begin
                       if (amo_op_store_cycle) begin
                           store_data[mask_idx*32 +: 32] = amo_op_store_data[31:0];
                           store_mask[mask_idx*4 +: 4] = {4{cache_line_offset[2] == mask_idx}};
                       end else begin
                           store_data[mask_idx*32 +: 32] = rs2_data[31:0];
                           store_mask[mask_idx*4 +: 4] = {4{cache_line_offset_comb[2] == mask_idx}};
                       end
                   end
        SIZE_DWORD: begin
            if (amo_op_store_cycle) begin
                store_data = amo_op_store_data;
            end else begin
                store_data = rs2_data;
            end
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

always_comb begin
    if (amo_op_store_cycle)
        lsu_prev_stalled = '0;
    else if (is_access_misaligned || (is_amo && amo_is_sc && !amo_has_reservation))
        lsu_prev_stalled = '1;
    else
        lsu_prev_stalled = !(input_valid && input_is_mem && is_load_store);
end

always_ff @(posedge clk) begin
    if (rst) begin
        exec_mem_output_valid <= '0;
    end else if (input_valid && input_is_mem) begin
        exec_mem_output_valid <= !is_load_store || is_access_misaligned
                                          || (is_amo && amo_is_sc && !amo_has_reservation);
    end else begin
        exec_mem_output_valid <= !lsu_stall_next && !waiting_amo_op_load;
    end
end

always_ff @(posedge clk) begin
    exec_mem_exception <= '0;
    exec_mem_trap_cause <= 'x;
    if (input_valid && input_is_mem)
        exec_mem_fault_addr <= memory_addr_comb;

    if (!lsu_stall_next && waiting_amo_op_load) begin
        exec_mem_result <= loaded_data;
        exec_mem_exception <= '0;
        exec_mem_trap_cause <= 'x;
    end else if (!lsu_stall_next && !had_amo_write) begin
        exec_mem_result <= loaded_data;
        exec_mem_exception <= lsu_access_fault;
        exec_mem_trap_cause <= trap_causes::EXC_LOAD_ACCESS_FAULT;
    end else if (input_valid && input_is_mem) begin
        unique if (is_load_store && is_amo) begin
            // NOTE: We only output those regs here in case of misaligned exception (or for SC results)
            exec_mem_exception <= is_access_misaligned;
            exec_mem_trap_cause <= store_bit ? trap_causes::EXC_STORE_ADDR_MISALIGNED : trap_causes::EXC_LOAD_ADDR_MISALIGNED;
            if (is_amo && amo_is_sc)
                exec_mem_result <= !amo_has_reservation;
            else
                exec_mem_result <= 'x;
        end else if (is_load_store && !is_amo) begin
            // NOTE: For actual load/stores we only output using those regs in case of misaligned exception, so result is 'x
            //       The other kinds of load/store results come from the load/store unit combinatorially
            exec_mem_exception <= is_access_misaligned;
            exec_mem_trap_cause <= store_bit ? trap_causes::EXC_STORE_ADDR_MISALIGNED : trap_causes::EXC_LOAD_ADDR_MISALIGNED;
            exec_mem_result <= 'x;
        end else if (opcode == opcodes::MISC_MEM) begin
            // NOTE: Everything is already serialized, regular data FENCE is a no-op (but FENCE.I and others are not!)
            exec_mem_exception <= funct3 != 'b000;
            exec_mem_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
            exec_mem_result <= 'x;
        end else begin
            exec_mem_exception <= '1;
            exec_mem_trap_cause <= trap_causes::EXC_ILLEGAL_INSTR;
            exec_mem_result <= 'x;
        end
    end
end

endmodule