/**
 *  scoreboard.v (modified for dual-issue)
 *  
 *  Allow 2 instructions to reserve registers (score) and 
 *  complete (clear) simultaneously.
 */

`include "bsg_defines.sv"

module scoreboard
  import bsg_vanilla_pkg::*;
  #(els_p = RV32_reg_els_gp
    , `BSG_INV_PARAM(num_src_port_p)

    // int scoreboard: 1 clear port (default)
    // fp scoreboard: 2 clear ports
    , num_clear_port_p=1

    // up to 2 registers marked as busy per cycle
    , num_score_port_p=1

    , x0_tied_to_zero_p = 0
    , localparam id_width_lp = `BSG_SAFE_CLOG2(els_p)
  )
  (
    input clk_i
    , input reset_i

    , input [num_src_port_p-1:0][id_width_lp-1:0] src_id_i
    , input [id_width_lp-1:0] dest_id_i

    , input [num_src_port_p-1:0] op_reads_rf_i
    , input op_writes_rf_i

    // score port 0 = older instruction
    // score port 1 = younger instruction
    , input [num_score_port_p-1:0] score_i
    , input [num_score_port_p-1:0][id_width_lp-1:0] score_id_i

    , input [num_clear_port_p-1:0] clear_i
    , input [num_clear_port_p-1:0][id_width_lp-1:0] clear_id_i

    , output logic dependency_o
  );

  logic [els_p-1:0] scoreboard_r;


  // ---------------------------
  // multi-port clear logic
  // ---------------------------

  logic [num_clear_port_p-1:0][els_p-1:0] clear_by_port;
  logic [els_p-1:0][num_clear_port_p-1:0] clear_by_port_t; // transposed
  logic [els_p-1:0] clear_combined;

  // clear port transpose
  //
  bsg_transpose #(
    .els_p(num_clear_port_p)
    ,.width_p(els_p)
  ) clr_tranposer (
    .i(clear_by_port)
    ,.o(clear_by_port_t)
  );

  for (genvar j = 0 ; j < num_clear_port_p; j++) begin: clr_dcode_v
    bsg_decode_with_v #(
      .num_out_p(els_p)
    ) clear_decode_v (
      .i(clear_id_i[j])
      ,.v_i(clear_i[j])
      ,.o(clear_by_port[j])
    );
  end

  always_comb begin
    for (integer i = 0; i < els_p; i++) begin
      clear_combined[i] = |clear_by_port_t[i];
    end
  end


  // synopsys translate_off
  /*
  always_ff @ (negedge clk_i) begin
    if (~reset_i) begin
      for (integer i = 0; i < els_p; i++) begin
        assert($countones(clear_by_port_t[i]) <= 1) else
          $error("[ERROR][SCOREBOARD] multiple clear on the same id. t=%0t", $time);
      end
    end
  end
  */
  // synopsys translate_on


  // ---------------------------
  // multi-port score logic
  // ---------------------------

  // logic [els_p-1:0] score_bits;
  logic [num_score_port_p-1:0][els_p-1:0] score_by_port; // replaces score_bits
  logic [els_p-1:0][num_score_port_p-1:0] score_by_port_t; // transposed
  logic [els_p-1:0] score_combined;

  // determine allow_zero per score port
  logic [num_score_port_p-1:0] allow_zero;

  // score port transpose
  //
  bsg_transpose #(
    .els_p(num_score_port_p)
    ,.width_p(els_p)
  ) scr_transposer (
    .i(score_by_port)
    ,.o(score_by_port_t)
  );

  for (genvar j = 0 ; j < num_score_port_p ; j++) begin: score_dcode_v
    assign allow_zero[j] = (x0_tied_to_zero_p == 0) | (score_id_i[j] != '0);

    bsg_decode_with_v #(
      .num_out_p(els_p)
    ) score_demux (
      .i(score_id_i[j])
      ,.v_i(score_i[j] & allow_zero[j])
      ,.o(score_by_port[j])
    );
  end

  // combine score bits
  always_comb begin
    for (integer i = 0; i < els_p; i++) begin
      score_combined[i] = |score_by_port_t[i];
    end
  end

  // make extra sure x0 not marked busy
  // synopsys translate_off
  always_ff @ (negedge clk_i) begin
    if (x0_tied_to_zero_p && ~reset_i) begin
      // score_combined[0] = register x0
      assert(!score_combined[0]) 
      else $error("[ERROR][SCOREBOARD] Port Safety Violation: Attempted to score register x0.");
    end
  end
  // synopsys translate_on


  //---------------------------------------
  //
  always_ff @ (posedge clk_i) begin
    for (integer i = 0; i < els_p; i++) begin
      if(reset_i) begin
        scoreboard_r[i] <= 1'b0;
      end
      else begin
        // "score" takes priority over "clear" in case of 
        // simultaneous score and clear. But this
        // condition should not occur in general, as 
        // the pipeline should not allow a new dependency
        // on a register until the old dependency on that 
        // register is cleared.
        if(score_combined[i]) begin
          scoreboard_r[i] <= 1'b1;
        end
        else if (clear_combined[i]) begin
          scoreboard_r[i] <= 1'b0;
        end
      end
    end
  end

 
  // dependency logic
  // As the register is scored (in EXE), the instruction in ID that has WAW or RAW dependency on this register stalls.
  // The register that is being cleared does not stall ID. 

  // find dependency on scoreboard.
  logic [num_src_port_p-1:0] rs_depend_on_sb;
  logic rd_depend_on_sb;

  for (genvar i = 0; i < num_src_port_p; i++) begin
    assign rs_depend_on_sb[i] = scoreboard_r[src_id_i[i]] & op_reads_rf_i[i];
  end
  
  assign rd_depend_on_sb = scoreboard_r[dest_id_i] & op_writes_rf_i;

  // --------------------------------
  // find which matches on clear_id.
  // --------------------------------

  logic [num_clear_port_p-1:0][num_src_port_p-1:0] rs_on_clear;
  logic [num_src_port_p-1:0][num_clear_port_p-1:0] rs_on_clear_t;
  logic [num_clear_port_p-1:0] rd_on_clear;
  
  for (genvar i = 0; i < num_clear_port_p; i++) begin
    for (genvar j = 0; j < num_src_port_p; j++) begin
      assign rs_on_clear[i][j] = clear_i[i] && (clear_id_i[i] == src_id_i[j]);
    end

    assign rd_on_clear[i] = clear_i[i] && (clear_id_i[i] == dest_id_i);
  end

  bsg_transpose #(
    .els_p(num_clear_port_p)
    ,.width_p(num_src_port_p)
  ) trans1 (
    .i(rs_on_clear)
    ,.o(rs_on_clear_t)
  );

  logic [num_src_port_p-1:0] rs_on_clear_combined;
  logic rd_on_clear_combined;

  for (genvar i = 0; i < num_src_port_p; i++) begin
    assign rs_on_clear_combined[i] = |rs_on_clear_t[i];
  end

  assign rd_on_clear_combined = |rd_on_clear;


  // ----------------------------------
  // find which could depend on score.
  // ----------------------------------

  logic [num_score_port_p-1:0][num_src_port_p-1:0] rs_depend_on_score;
  logic [num_src_port_p-1:0][num_score_port_p-1:0] rs_depend_on_score_t; // transposed
  logic [num_score_port_p-1:0] rd_depend_on_score;

  // check if current src/dest ID matches reg being scored
  for (genvar i = 0; i < num_score_port_p; i++) begin
    for (genvar j = 0; j < num_src_port_p; j++) begin

      // RAW
      assign rs_depend_on_score[i][j] = (src_id_i[j] == score_id_i[i]) && op_reads_rf_i[j];
    end

    // WAW
    assign rd_depend_on_score[i] = (dest_id_i == score_id_i[i]) && op_writes_rf_i;
  end

  // -----------------------------
  // final dependency calculation
  // -----------------------------

  // score_i arrives later than other signals, so we want to remove it from the long path.
  wire depend_on_sb = |({rd_depend_on_sb, rs_depend_on_sb} & ~{rd_on_clear_combined, rs_on_clear_combined});

  // condense source reg matches for each src port into a single bit per score port
  logic [num_score_port_p-1:0] rs_depend_on_score_any;
  for (genvar i = 0; i < num_score_port_p; i++) begin
    assign rs_depend_on_score_any[i] = |rs_depend_on_score[i];
  end

  wire [num_score_port_p-1:0] depend_on_score = rd_depend_on_score | rs_depend_on_score_any;

  // assign dependency_o = depend_on_sb | |(depend_on_score & score_i & allow_zero);
  assign dependency_o = depend_on_sb;


  // synopsys translate_off
  /*
  always_ff @ (negedge clk_i) begin
    if (~reset_i) begin
      assert((score_combined & clear_combined) == '0)
        else $error("[BSG_ERROR] score and clear on the same id cannot happen.");
    end
  end
  */
  // synopsys translate_on


endmodule

`BSG_ABSTRACT_MODULE(scoreboard)

