/**
 *  icache_dual_issue.sv
 *
 *  Super-scalar (dual-issue) instruction cache for manycore. 
 *  Outputs 2 consecutive instructions with dual branch predictions.
 *
 *  Diagram on branch target pre-computation logic:
 *  https://docs.google.com/presentation/d/1ZeRHYhqMHJQ0mRgDTilLuWQrZF7On-Be_KNNosgeW0c/edit#slide=id.g10d2e6febb9_1_0
 */

`include "bsg_vanilla_defines.svh"

module icache // dual issue icache
  import bsg_vanilla_pkg::*;
  #(`BSG_INV_PARAM(icache_tag_width_p)
    , `BSG_INV_PARAM(icache_entries_p)
    , `BSG_INV_PARAM(icache_block_size_in_words_p) // block size is power of 2.
    , localparam icache_addr_width_lp=`BSG_SAFE_CLOG2(icache_entries_p/icache_block_size_in_words_p)
    , pc_width_lp=(icache_tag_width_p+`BSG_SAFE_CLOG2(icache_entries_p))
    , icache_block_offset_width_lp=`BSG_SAFE_CLOG2(icache_block_size_in_words_p)
  )
  (
    input clk_i
    , input network_reset_i
    , input reset_i

    // ctrl signal
    , input v_i // valid inputs
    , input w_i // write enable
    , input flush_i // signal to flush
    , input read_pc_plus4_i // signal to read pc+4 (used for energy optimization, less critical for dual-issue)

    // icache write
    , input [pc_width_lp-1:0] w_pc_i // the pc of the instruction being written to icache
    , input [RV32_instr_width_gp-1:0] w_instr_i // the instruction being written to icache

    // icache read (by processor) - provides 2 consecutive PCs
    , input [pc_width_lp-1:0] pc_i // the pc of the first instruction to read
    , input [pc_width_lp-1:0] jalr_prediction_0_i // jalr predictor for first instruction
    , input [pc_width_lp-1:0] jalr_prediction_1_i // jalr predictor for second instruction

    // DUAL ISSUE OUTPUT: Two instructions, two PCs, two branch predictions
    , output [RV32_instr_width_gp-1:0] instr0_o // first instruction
    , output [RV32_instr_width_gp-1:0] instr1_o // second instruction (pc + 1 word)
    , output [pc_width_lp-1:0] pred_or_jump_addr0_o // predicted jump target for first instruction
    , output [pc_width_lp-1:0] pred_or_jump_addr1_o // predicted jump target for second instruction
    , output [pc_width_lp-1:0] pc0_o // the pc of the first instruction read from icache
    , output [pc_width_lp-1:0] pc1_o // the pc of the second instruction (pc0_o + 1)
    , output logic branch_predicted_taken0_o // branch prediction for first instruction
    , output logic branch_predicted_taken1_o // branch prediction for second instruction
    , output icache_miss_o // icache miss for first instruction
    , output icache_flush_r_o // signal to indicate the icache is being flushed
  );

  // localparam
  //
  localparam branch_pc_low_width_lp = (RV32_Bimm_width_gp+1);
  localparam jal_pc_low_width_lp    = (RV32_Jimm_width_gp+1);

  localparam branch_pc_high_width_lp = (pc_width_lp+2) - branch_pc_low_width_lp; 
  localparam jal_pc_high_width_lp    = (pc_width_lp+2) - jal_pc_low_width_lp;

  localparam icache_format_width_lp = `icache_format_width(icache_tag_width_p, icache_block_size_in_words_p);

  // declare icache entry struct.
  //
  `declare_icache_format_s(icache_tag_width_p, icache_block_size_in_words_p);

  // address decode
  //
  logic [icache_tag_width_p-1:0] w_tag;
  logic [icache_addr_width_lp-1:0] w_addr;
  logic [icache_block_offset_width_lp-1:0] w_block_offset;
  assign {w_tag, w_addr, w_block_offset} = w_pc_i;
  

  // Instantiate icache memory 
  //
  logic v_li;
  icache_format_s icache_data_li, icache_data_lo;
  logic [icache_addr_width_lp-1:0] icache_addr_li;

  bsg_mem_1rw_sync #(
    .width_p(icache_format_width_lp)
    ,.els_p(icache_entries_p/icache_block_size_in_words_p)
    ,.latch_last_read_p(1)
  ) imem_0 (
    .clk_i(clk_i)
    ,.reset_i(reset_i)
    ,.v_i(v_li)
    ,.w_i(w_i)
    ,.addr_i(icache_addr_li)
    ,.data_i(icache_data_li)
    ,.data_o(icache_data_lo)
  );

  assign icache_addr_li = w_i
    ? w_addr
    : pc_i[icache_block_offset_width_lp+:icache_addr_width_lp];


  //  Pre-compute the lower part of the jump address for JAL and BRANCH
  //  instruction
  //
  //  The width of the adder is defined by the Imm width +1.
  //
  //  For the branch op, we are saving the sign of an imm13 value, in the LSB
  //  of instruction opcode, to use it later when making branch prediction.
  //
  instruction_s w_instr;
  assign w_instr = w_instr_i;
  wire write_branch_instr = w_instr.op ==? `RV32_BRANCH;
  wire write_jal_instr    = w_instr.op ==? `RV32_JAL_OP;
  
  // BYTE address computation
  wire [branch_pc_low_width_lp-1:0] branch_imm_val = `RV32_Bimm_13extract(w_instr);
  wire [branch_pc_low_width_lp-1:0] branch_pc_val = branch_pc_low_width_lp'({w_pc_i, 2'b0}); 
  
  wire [jal_pc_low_width_lp-1:0] jal_imm_val = `RV32_Jimm_21extract(w_instr);
  wire [jal_pc_low_width_lp-1:0] jal_pc_val = jal_pc_low_width_lp'({w_pc_i, 2'b0}); 
  
  logic [branch_pc_low_width_lp-1:0] branch_pc_lower_res;
  logic branch_pc_lower_cout;
  logic [jal_pc_low_width_lp-1:0] jal_pc_lower_res;
  logic jal_pc_lower_cout;
  
  assign {branch_pc_lower_cout, branch_pc_lower_res} = {1'b0, branch_imm_val} + {1'b0, branch_pc_val};
  assign {jal_pc_lower_cout,    jal_pc_lower_res   } = {1'b0, jal_imm_val}    + {1'b0, jal_pc_val   };
  
  
  // Inject the 2-BYTE (half) address, the LSB is ignored.
  wire [RV32_instr_width_gp-1:0] injected_instr = write_branch_instr
    ? `RV32_Bimm_12inject1(w_instr, branch_pc_lower_res)
    : (write_jal_instr
      ? `RV32_Jimm_20inject1(w_instr, jal_pc_lower_res)
      : w_instr);

  wire imm_sign = write_branch_instr
    ? branch_imm_val[RV32_Bimm_width_gp] 
    : jal_imm_val[RV32_Jimm_width_gp];

  wire pc_lower_cout = write_branch_instr
    ? branch_pc_lower_cout
    : jal_pc_lower_cout;


  // buffered writes
  logic [icache_block_size_in_words_p-2:0] imm_sign_r;
  logic [icache_block_size_in_words_p-2:0] pc_lower_cout_r;
  logic [icache_block_size_in_words_p-2:0][RV32_instr_width_gp-1:0] buffered_instr_r;

  assign icache_data_li = '{
    lower_sign : {imm_sign, imm_sign_r},
    lower_cout : {pc_lower_cout, pc_lower_cout_r},
    tag        : w_tag,
    instr      : {injected_instr, buffered_instr_r}
  };


  // icache write counter
  logic [icache_block_offset_width_lp-1:0] write_count_r;
  always_ff @ (posedge clk_i) begin
    if (network_reset_i) begin
      write_count_r <= '0;
    end
    else begin
      if (v_i & w_i) begin
        write_count_r <= write_count_r + 1'b1;
      end
    end
  end

  logic write_en_buffer;
  logic write_en_icache;
  always_ff @ (posedge clk_i) begin
    if (write_en_buffer) begin
      imm_sign_r[write_count_r] <= imm_sign;
      pc_lower_cout_r[write_count_r] <= pc_lower_cout;
      buffered_instr_r[write_count_r] <= injected_instr;
    end
  end

  always_comb begin
    if (write_count_r == icache_block_size_in_words_p-1) begin
      write_en_buffer = 1'b0;
      write_en_icache = v_i & w_i;
    end
    else begin
      write_en_buffer = v_i & w_i;
      write_en_icache = 1'b0;
    end
  end

  // synopsys translate_off
  always_ff @ (negedge clk_i) begin
    if ((network_reset_i === 1'b0) & v_i & w_i) begin
      assert(write_count_r == w_block_offset) else $error("icache being written not in sequence.");
    end
  end
  // synopsys translate_on

  // Program counter - tracks first instruction
  logic [pc_width_lp-1:0] pc_r; 
  logic icache_flush_r;

  always_ff @ (posedge clk_i) begin
    if (reset_i) begin
      pc_r <= '0;
      icache_flush_r <= 1'b0;
    end
    else begin

      if (v_i & ~w_i) begin
        pc_r <= pc_i;
        icache_flush_r <= 1'b0;
      end
      else begin
        icache_flush_r <= flush_i;
      end
    end
  end

  assign icache_flush_r_o = icache_flush_r;


  // Energy-saving logic (simplified for dual-issue)
  // - Don't read the icache if at the last word of the block and expecting sequential fetch next cycle
  //   since next fetch would wrap to next block (block boundary crossing requires separate memory access)
  assign v_li = w_i
    ? write_en_icache
    : (v_i & ((&pc_r[0+:icache_block_offset_width_lp] | (pc_r[0+:icache_block_offset_width_lp] == (icache_block_size_in_words_p-2))) | ~read_pc_plus4_i));


  // ============================================================================
  // DUAL ISSUE READ PATH: Extract two consecutive instructions
  // ============================================================================

  // Extract first instruction (at offset pc_r[block_offset])
  instruction_s instr0_out;
  wire lower_sign0_out, lower_cout0_out;
  
  assign instr0_out = icache_data_lo.instr[pc_r[0+:icache_block_offset_width_lp]];
  assign lower_sign0_out = icache_data_lo.lower_sign[pc_r[0+:icache_block_offset_width_lp]];
  assign lower_cout0_out = icache_data_lo.lower_cout[pc_r[0+:icache_block_offset_width_lp]];

  // Extract second instruction (at offset pc_r[block_offset] + 1)
  // NOTE: This assumes icache_block_size_in_words_p >= 2
  //       If the second instruction is at the block boundary, this may cross to next block
  //       In that case, we'd need dual-port memory or separate handling
  // For now, assume block_size >= 2 and both instructions fit within the same block
  instruction_s instr1_out;
  wire lower_sign1_out, lower_cout1_out;
  logic [icache_block_offset_width_lp-1:0] offset_instr1;
  
  assign offset_instr1 = pc_r[0+:icache_block_offset_width_lp] + 1'b1;
  assign instr1_out = icache_data_lo.instr[offset_instr1];
  assign lower_sign1_out = icache_data_lo.lower_sign[offset_instr1];
  assign lower_cout1_out = icache_data_lo.lower_cout[offset_instr1];


  // ============================================================================
  // Branch Target Prediction for INSTRUCTION 0
  // ============================================================================

  wire sel_pc0    = ~(lower_sign0_out ^ lower_cout0_out); 
  wire sel_pc0_p1 = (~lower_sign0_out) & lower_cout0_out; 

  logic [branch_pc_high_width_lp-1:0] branch_pc_high0;
  logic [jal_pc_high_width_lp-1:0] jal_pc_high0;

  assign branch_pc_high0 = pc_r[(branch_pc_low_width_lp-2)+:branch_pc_high_width_lp];
  assign jal_pc_high0 = pc_r[(jal_pc_low_width_lp-2)+:jal_pc_high_width_lp];

  logic [branch_pc_high_width_lp-1:0] branch_pc_high0_out;
  logic [jal_pc_high_width_lp-1:0] jal_pc_high0_out;

  always_comb begin
    if (sel_pc0) begin
      branch_pc_high0_out = branch_pc_high0;
      jal_pc_high0_out = jal_pc_high0;
    end
    else if (sel_pc0_p1) begin
      branch_pc_high0_out = branch_pc_high0 + 1'b1;
      jal_pc_high0_out = jal_pc_high0 + 1'b1;
    end
    else begin // sel_pc0_n1
      branch_pc_high0_out = branch_pc_high0 - 1'b1;
      jal_pc_high0_out = jal_pc_high0 - 1'b1;
    end
  end

  wire is_jal_instr0 =  instr0_out.op == `RV32_JAL_OP;
  wire is_jalr_instr0 = instr0_out.op == `RV32_JALR_OP;

  logic [pc_width_lp+2-1:0] jal_pc0;
  logic [pc_width_lp+2-1:0] branch_pc0;
   
  assign branch_pc0 = {branch_pc_high0_out, `RV32_Bimm_13extract(instr0_out)};
  assign jal_pc0 = {jal_pc_high0_out, `RV32_Jimm_21extract(instr0_out)};


  // ============================================================================
  // Branch Target Prediction for INSTRUCTION 1
  // ============================================================================

  // For instruction 1, we need to compute with PC = pc_r + 1
  // The carry propagation is similar but uses pc_r + 1
  wire sel_pc1    = ~(lower_sign1_out ^ lower_cout1_out); 
  wire sel_pc1_p1 = (~lower_sign1_out) & lower_cout1_out; 

  logic [branch_pc_high_width_lp-1:0] branch_pc_high1;
  logic [jal_pc_high_width_lp-1:0] jal_pc_high1;

  // pc_r + 1 in terms of the low/high split for branch/jal calculations
  // Since we're at offset+1, we need to be careful about carry propagation
  logic [pc_width_lp-1:0] pc1_val = pc_r + 1'b1;
  
  assign branch_pc_high1 = pc1_val[(branch_pc_low_width_lp-2)+:branch_pc_high_width_lp];
  assign jal_pc_high1 = pc1_val[(jal_pc_low_width_lp-2)+:jal_pc_high_width_lp];

  logic [branch_pc_high_width_lp-1:0] branch_pc_high1_out;
  logic [jal_pc_high_width_lp-1:0] jal_pc_high1_out;

  always_comb begin
    if (sel_pc1) begin
      branch_pc_high1_out = branch_pc_high1;
      jal_pc_high1_out = jal_pc_high1;
    end
    else if (sel_pc1_p1) begin
      branch_pc_high1_out = branch_pc_high1 + 1'b1;
      jal_pc_high1_out = jal_pc_high1 + 1'b1;
    end
    else begin // sel_pc1_n1
      branch_pc_high1_out = branch_pc_high1 - 1'b1;
      jal_pc_high1_out = jal_pc_high1 - 1'b1;
    end
  end

  wire is_jal_instr1 =  instr1_out.op == `RV32_JAL_OP;
  wire is_jalr_instr1 = instr1_out.op == `RV32_JALR_OP;

  logic [pc_width_lp+2-1:0] jal_pc1;
  logic [pc_width_lp+2-1:0] branch_pc1;
   
  assign branch_pc1 = {branch_pc_high1_out, `RV32_Bimm_13extract(instr1_out)};
  assign jal_pc1 = {jal_pc_high1_out, `RV32_Jimm_21extract(instr1_out)};


  // ============================================================================
  // ASSIGN OUTPUTS - DUAL ISSUE
  // ============================================================================
  
  // Instruction outputs
  assign instr0_o = instr0_out;
  assign instr1_o = instr1_out;
  
  // PC outputs
  assign pc0_o = pc_r;
  assign pc1_o = pc_r + 1'b1;

  // Predicted jump/branch targets
  assign pred_or_jump_addr0_o = is_jal_instr0
    ? jal_pc0[2+:pc_width_lp]
    : (is_jalr_instr0
      ? jalr_prediction_0_i
      : branch_pc0[2+:pc_width_lp]);

  assign pred_or_jump_addr1_o = is_jal_instr1
    ? jal_pc1[2+:pc_width_lp]
    : (is_jalr_instr1
      ? jalr_prediction_1_i
      : branch_pc1[2+:pc_width_lp]);

  // Branch prediction indicators (from sign bit of immediate)
  assign branch_predicted_taken0_o = lower_sign0_out;
  assign branch_predicted_taken1_o = lower_sign1_out;

  // icache miss logic - check first instruction
  assign icache_miss_o = icache_data_lo.tag != pc_r[icache_block_offset_width_lp+icache_addr_width_lp+:icache_tag_width_p];

 
endmodule

`BSG_ABSTRACT_MODULE(icache_dual_issue)
