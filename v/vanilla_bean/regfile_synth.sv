/**
 *    regfile_synth.v
 *
 *    synthesized register file
 *
 *    @author tommy
 */

`include "bsg_defines.sv"

module regfile_synth
  #(`BSG_INV_PARAM(width_p)
    , `BSG_INV_PARAM(els_p)
    , `BSG_INV_PARAM(num_rs_p)
    , num_ws_p // number of writeback ports
    , `BSG_INV_PARAM(x0_tied_to_zero_p)

    , localparam addr_width_lp=`BSG_SAFE_CLOG2(els_p)
  )
  (
    input clk_i
    , input reset_i

    // wb port 1
    , input w_v_i
    , input [addr_width_lp-1:0] w_addr_i
    , input [width_p-1:0] w_data_i
    
    // wb port 2 (fp regfile only)
    , input w2_v_i
    , input [addr_width_lp-1:0] w2_addr_i
    , input [width_p-1:0] w2_data_i

    , input [num_rs_p-1:0] r_v_i
    , input [num_rs_p-1:0][addr_width_lp-1:0] r_addr_i
    , output logic [num_rs_p-1:0][width_p-1:0] r_data_o
  );

  wire unused = reset_i;
  
  logic [num_rs_p-1:0][addr_width_lp-1:0] r_addr_r;


  always_ff @ (posedge clk_i)
    for (integer i = 0; i < num_rs_p; i++)
      if (r_v_i[i]) r_addr_r[i] <= r_addr_i[i];



  if (x0_tied_to_zero_p) begin: xz
    // x0 is tied to zero.
    logic [width_p-1:0] mem_r [els_p-1:1];
    
    for (genvar i = 0; i < num_rs_p; i++) begin

      // if address being read matches a write in the same cycle,
      // return data from write port (port 1 has priority over port 0).
      // otherwise, read normally.

      assign r_data_o[i] = 
        (num_ws_p > 1 && w2_v_i && (r_addr_r[i] == w2_addr_i) && (w2_addr_i != '0)) ? w2_data_i :
        (w_v_i && (r_addr_r[i] == w_addr_i) && (w_addr_i != '0)) ? w_data_i :
        ((r_addr_r[i] == '0) ? '0 : mem_r[r_addr_r[i]]);

    end

    always_ff @ (posedge clk_i) begin

      // wb port 1
      if (w_v_i & (w_addr_i != '0))
        mem_r[w_addr_i] <= w_data_i;

      // wb port 2 (fp regfile only)
      // allow port 2 to overwrite port 1 if same addr
      if (num_ws_p > 1) begin
        if (w2_v_i & (w2_addr_i != '0))
          mem_r[w2_addr_i] <= w2_data_i;
      end
    end
  end
  else begin: xnz
    // x0 is not tied to zero.
    logic [width_p-1:0] mem_r [els_p-1:0];
   
    for (genvar i = 0; i < num_rs_p; i++) begin

      // if address being read matches a write in the same cycle,
      // return data from write port (port 1 has priority over port 0).
      // otherwise, read normally.

      assign r_data_o[i] = 
        (num_ws_p > 1 && w2_v_i && (r_addr_r[i] == w2_addr_i)) ? w2_data_i :
        (w_v_i && (r_addr_r[i] == w_addr_i)) ? w_data_i :
        mem_r[r_addr_r[i]];

    end

    always_ff @ (posedge clk_i) begin

      // wb port 1
      if (w_v_i)
        mem_r[w_addr_i] <= w_data_i;

      // wb port 2 (fp regfile only)
      // allow port 2 to overwrite port 1 if same addr
      if (num_ws_p > 1) begin
        if (w2_v_i) begin
          mem_r[w2_addr_i] <= w2_data_i;
        end
      end
    end
  end

endmodule

`BSG_ABSTRACT_MODULE(regfile_synth)

