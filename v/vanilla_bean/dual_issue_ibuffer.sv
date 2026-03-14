// Yara Al-Shorman
// Dual issue final project
// the dual issue ibuffer goes between the icache and decode units
// it holds the two instructions fetched from icache and sends them to 
// decode or fp_decode based on the nature of the instructions
// it also handles logic for branch prediction and jump target calculation
// as well as stalling logic for when the decode units are not ready to accept new instructions
// only holds 2 instrucions at a time

`include "bsg_vanilla_defines.svh"

module dual_issue_ibuffer
    import bsg_vanilla_pkg::*;
    #(  
        parameter pc_width_lp // param for pc width
    )
    (
        input clk_i;
        , input reset_i;
     
        // valid-ready signals to icache
        , input v_i;
        , output ready_o
        // valid-ready signals to int decode
        , input int_yum_i
        , output int_v_o;
        // valid-ready signals to fp decode
        , input fp_yum_i
        , output fp_v_o;

        , input [RV32_instr_width_gp-1:0] instr0_i
        , input [RV32_instr_width_gp-1:0] instr1_i
     
        // From icache
        , input [pc_width_lp-1:0] pc0_i
        , input [pc_width_lp-1:0] pc1_i
        , input [pc_width_lp-1:0] pred_or_jump_addr0_i
        , input [pc_width_lp-1:0] pred_or_jump_addr1_i
        , input logic branch_predicted_taken0_i
        , input logic branch_predicted_taken1_i
     
        // To downstream
        , output [pc_width_lp-1:0] pred_or_jump_addr0_o // predicted jump target for first instruction
        , output [pc_width_lp-1:0] pred_or_jump_addr1_o // predicted jump target for second instruction
        , output [pc_width_lp-1:0] pc0_o // the pc of the first instruction read from icache
        , output [pc_width_lp-1:0] pc1_o // the pc of the second instruction (pc0_o + 1)
        , output logic branch_predicted_taken0_o // branch prediction for first instruction
        , output logic branch_predicted_taken1_o

        , output [RV32_instr_width_gp-1:0] instr_int_o // instruction going to int decode
        , output [RV32_instr_width_gp-1:0] instr_fp_o // instruction going to fp decode
    );

    logic is_fp_instr0, is_fp_instr1;
    // an instruction is serializing if it is a branch, jump, fence, csr, or mret instruction
    logic is_serializing_instr0, is_serializing_instr1;
    // logic to distribute instructions and consider edge cases
    always_comb begin
        unique casez (instr0_i[6:0])
            `RV32_OP_FP: begin
                is_fp_instr0 = 1'b1;
                is_serializing_instr0 = 1'b0;
            end
            `RV32_BRANCH, `RV32_JAL_OP, `RV32_JALR_OP, `RV32_MISC_MEM, `RV32_SYSTEM: begin
                is_fp_instr0 = 1'b0;
                is_serializing_instr0 = 1'b1;
            end
            default: begin
                is_fp_instr0 = 1'b0;
                is_serializing_instr0 = 1'b0;
            end
        endcase
    end

     always_comb begin
        unique casez (instr1_i[6:0])
            `RV32_OP_FP: begin
                is_fp_instr1 = 1'b1;
                is_serializing_instr1 = 1'b0;
            end
            `RV32_BRANCH, `RV32_JAL_OP, `RV32_JALR_OP, `RV32_MISC_MEM, `RV32_SYSTEM: begin
                is_fp_instr1 = 1'b0;
                is_serializing_instr1 = 1'b1;
            end
            default: begin
                is_fp_instr1 = 1'b0;
                is_serializing_instr1 = 1'b0;
            end
        endcase
    end

    // Register to hold instr1 when it can't be issued in the same cycle as instr0
    logic [RV32_instr_width_gp-1:0] instr1_held_r;
    logic instr1_held_valid_r;
    logic instr1_held_is_fp_r;
    logic instr1_held_is_serializing_r;
    
    // PC and prediction registers for held instruction
    logic [pc_width_lp-1:0] pc1_held_r;
    logic [pc_width_lp-1:0] pred_or_jump_addr1_held_r;
    logic branch_predicted_taken1_held_r;

    // Determine if we should hold instr1 based on current instructions
    logic hold_instr1;
    always_comb begin
        if (is_serializing_instr0 | is_serializing_instr1) begin
            hold_instr1 = 1'b1;
        end
        else if (!(is_fp_instr0 ^ is_fp_instr1)) begin
            // the instructions are the same type (fp/fp or int/int)
            hold_instr1 = 1'b1;
        end
        else begin
            // different types and no serializing instructions
            hold_instr1 = 1'b0;
        end
    end

    // Update held instruction register
    always_ff @(posedge clk_i) begin
        if (reset_i) begin
            instr1_held_valid_r <= 1'b0;
        end
        else begin
            // When we accept new instructions and need to hold instr1
            if (v_i && !instr1_held_valid_r && hold_instr1) begin
                instr1_held_valid_r <= 1'b1;
                instr1_held_r <= instr1_i;
                instr1_held_is_fp_r <= is_fp_instr1;
                instr1_held_is_serializing_r <= is_serializing_instr1;
                pc1_held_r <= pc1_i;
                pred_or_jump_addr1_held_r <= pred_or_jump_addr1_i;
                branch_predicted_taken1_held_r <= branch_predicted_taken1_i;
            end
            // Clear when held instruction is issued
            else if (instr1_held_valid_r && fp_yum_i && instr1_held_is_fp_r) begin
                instr1_held_valid_r <= 1'b0;
            end
            else if (instr1_held_valid_r && int_yum_i && !instr1_held_is_fp_r) begin
                instr1_held_valid_r <= 1'b0;
            end
        end
    end

    // Determine if we should hold instr1 in the next cycle
    logic will_hold_instr1_next;
    always_comb begin
        if (instr1_held_valid_r) begin
            // We're issuing a held instruction, so we can accept new ones next cycle
            will_hold_instr1_next = 1'b0;
        end
        else if (is_serializing_instr0 | is_serializing_instr1) begin
            // Serializing, so hold instr1 if present
            will_hold_instr1_next = 1'b1;
        end
        else if (!(is_fp_instr0 ^ is_fp_instr1)) begin
            // Same type, hold instr1
            will_hold_instr1_next = 1'b1;
        end
        else begin
            // Different types, no hold
            will_hold_instr1_next = 1'b0;
        end
    end

    // Output routing - route issued instructions to appropriate decoders
    always_comb begin
        instr_int_o = '0;
        instr_fp_o = '0;
        
        if (instr1_held_valid_r) begin
            // Issue the held instruction
            if (instr1_held_is_fp_r) begin
                instr_fp_o = instr1_held_r;
            end
            else begin
                instr_int_o = instr1_held_r;
            end
        end
        else if (v_i) begin
            // Issue from fresh instructions
            if (will_hold_instr1_next) begin
                // Only issue instr0
                if (is_fp_instr0) begin
                    instr_fp_o = instr0_i;
                end
                else begin
                    instr_int_o = instr0_i;
                end
            end
            else begin
                // Issue both instr0 and instr1
                if (is_fp_instr0) begin
                    instr_fp_o = instr0_i;
                    // instr1 must be int (different type)
                    instr_int_o = instr1_i;
                end
                else begin
                    instr_int_o = instr0_i;
                    // instr1 must be fp (different type)
                    instr_fp_o = instr1_i;
                end
            end
        end
    end

    // Valid and ready signals
    always_comb begin
        if (instr1_held_valid_r) begin
            // Issuing held instruction from previous cycle
            int_v_o = !instr1_held_is_fp_r ? 1'b1 : 1'b0;
            fp_v_o = instr1_held_is_fp_r ? 1'b1 : 1'b0;
            ready_o = 1'b1;  // Can accept new instructions
        end
        else if (v_i) begin
            // Have new instructions from icache
            if (will_hold_instr1_next) begin
                // Will hold instr1, so only issue instr0
                int_v_o = !is_fp_instr0 ? 1'b1 : 1'b0;
                fp_v_o = is_fp_instr0 ? 1'b1 : 1'b0;
                ready_o = 1'b0;  // Don't accept new ones yet
            end
            else begin
                // Can issue both instr0 and instr1
                int_v_o = (!is_fp_instr0 | !is_fp_instr1) ? 1'b1 : 1'b0;
                fp_v_o = (is_fp_instr0 | is_fp_instr1) ? 1'b1 : 1'b0;
                ready_o = 1'b1;  // Ready for more
            end
        end
        else begin
            // No valid instructions
            int_v_o = 1'b0;
            fp_v_o = 1'b0;
            ready_o = 1'b1;
        end
    end

    // Output PC and prediction info
    always_comb begin
        if (instr1_held_valid_r) begin
            // Issuing held instr1 as instr0
            pc0_o = pc1_held_r;
            pred_or_jump_addr0_o = pred_or_jump_addr1_held_r;
            branch_predicted_taken0_o = branch_predicted_taken1_held_r;
            pc1_o = '0;
            pred_or_jump_addr1_o = '0;
            branch_predicted_taken1_o = 1'b0;
        end
        else if (v_i && !will_hold_instr1_next) begin
            // Issuing both instr0 and instr1
            pc0_o = pc0_i;
            pred_or_jump_addr0_o = pred_or_jump_addr0_i;
            branch_predicted_taken0_o = branch_predicted_taken0_i;
            pc1_o = pc1_i;
            pred_or_jump_addr1_o = pred_or_jump_addr1_i;
            branch_predicted_taken1_o = branch_predicted_taken1_i;
        end
        else if (v_i && will_hold_instr1_next) begin
            // Issuing only instr0
            pc0_o = pc0_i;
            pred_or_jump_addr0_o = pred_or_jump_addr0_i;
            branch_predicted_taken0_o = branch_predicted_taken0_i;
            pc1_o = '0;
            pred_or_jump_addr1_o = '0;
            branch_predicted_taken1_o = 1'b0;
        end
        else begin
            // No valid instructions
            pc0_o = '0;
            pc1_o = '0;
            pred_or_jump_addr0_o = '0;
            pred_or_jump_addr1_o = '0;
            branch_predicted_taken0_o = 1'b0;
            branch_predicted_taken1_o = 1'b0;
        end
    end

endmodule