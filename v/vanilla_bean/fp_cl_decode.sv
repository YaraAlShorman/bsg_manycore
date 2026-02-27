/**
 *
 *  fp_cl_decode.sv
 *
 *  floating point instruction decoder.
 *
 *  This module defines a decode unit that looks at the instruction
 *  and sets a bunch of control signals that describe the use of the
 *  instruction if they are floating point. A smaller version of 
 *  cl_decode.sv.
 *
 *
 */

`include "bsg_vanilla_defines.svh"

module fp_cl_decode
import bsg_vanilla_pkg::*;
import bsg_manycore_pkg::*;
(
  input instruction_s	instruction_i,

  /* signals from decode_s for FP RF and scoreboard */
  output logic		is_fp_op_o, 	// goes into FP_EXE
  output logic		read_frs1_o,	// reads rs1 of FP regfile
  output logic		read_frs2_o,	// reads rs2 of FP regfile
  output logic		read_frs3_o,	// reads rs3 of FP regfile
  output logic		write_frd_o,	// writes back to FP regfile

  output fp_decode_s	fp_decode_o
);


//+----------------------------------------------
//|
//|     RISC-V edit: "F" STANDARD EXTENSION
//|
//+----------------------------------------------

always_comb begin
  read_frs1_o = 1'b0;
  read_frs2_o = 1'b0;
  read_frs3_o = 1'b0;
  write_frd_o = 1'b0;
  is_fp_op_o = 1'b0;
  unique casez (instruction_i)
    // Rtype float instr
    `RV32_FADD_S,  `RV32_FSUB_S,   `RV32_FMUL_S,
    `RV32_FSGNJ_S, `RV32_FSGNJN_S, `RV32_FSGNJX_S,
    `RV32_FMIN_S,  `RV32_FMAX_S: begin
      read_frs1_o = 1'b1;
      read_frs2_o = 1'b1;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b1;
      is_fp_op_o = 1'b1;
    end
    // compare
    `RV32_FEQ_S, `RV32_FLT_S, `RV32_FLE_S: begin
      read_frs1_o = 1'b1;
      read_frs2_o = 1'b1;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b0;
      is_fp_op_o = 1'b1;
    end
    // classify
    `RV32_FCLASS_S: begin
      read_frs1_o = 1'b1;
      read_frs2_o = 1'b0;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b0;
      is_fp_op_o = 1'b1;
    end
    // i2f (signed int)
    `RV32_FCVT_S_W, `RV32_FCVT_S_WU: begin
      read_frs1_o = 1'b0;
      read_frs2_o = 1'b0;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b1;
      is_fp_op_o = 1'b1;
    end
    // f2i
    `RV32_FCVT_W_S, `RV32_FCVT_WU_S: begin
      read_frs1_o = 1'b1;
      read_frs2_o = 1'b0;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b0;
      is_fp_op_o = 1'b1;
    end
    // FMV (fp -> int)
    `RV32_FMV_X_W: begin
      read_frs1_o = 1'b1;
      read_frs2_o = 1'b0;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b0;
      is_fp_op_o = 1'b1;
    end
    // FMV (int -> fp)
    `RV32_FMV_W_X: begin
      read_frs1_o = 1'b0;
      read_frs2_o = 1'b0;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b1;
      is_fp_op_o = 1'b1;
    end
    // Float load
    `RV32_FLW_S: begin
      read_frs1_o = 1'b0;
      read_frs2_o = 1'b0;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b1;
      is_fp_op_o = 1'b0;
    end
    // Float store
    `RV32_FSW_S: begin
      read_frs1_o = 1'b0;
      read_frs2_o = 1'b1;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b0;
      is_fp_op_o = 1'b0;
    end
    // FMA
    `RV32_FMADD_S, `RV32_FMSUB_S, `RV32_FNMSUB_S, `RV32_FNMADD_S: begin
      read_frs1_o = 1'b1;
      read_frs2_o = 1'b1;
      read_frs3_o = 1'b1;
      write_frd_o = 1'b1;
      is_fp_op_o = 1'b1;
    end
    // FDIV, SQRT
    `RV32_FDIV_S, `RV32_FSQRT_S: begin
      read_frs1_o = 1'b1;
      read_frs2_o = 1'b1;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b1;
      is_fp_op_o = 1'b1;
    end
    default: begin
      read_frs1_o = 1'b0;
      read_frs2_o = 1'b0;
      read_frs3_o = 1'b0;
      write_frd_o = 1'b0;
      is_fp_op_o = 1'b0;
    end
  endcase
end


// fp_decode_s
always_comb begin
  fp_decode_o.is_fpu_float_op = 1'b0;
  fp_decode_o.is_fpu_int_op = 1'b0;
  fp_decode_o.is_fdiv_op = 1'b0;
  fp_decode_o.is_fsqrt_op = 1'b0;
  fp_decode_o.fpu_float_op = eFADD;
  fp_decode_o.fpu_int_op = eFEQ;

  unique casez (instruction_i)
    `RV32_FADD_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFADD;
    end
    `RV32_FSUB_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFSUB;
    end
    `RV32_FMUL_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFMUL;
    end
    `RV32_FSGNJ_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFSGNJ;
    end
    `RV32_FSGNJN_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFSGNJN;
    end
    `RV32_FSGNJX_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFSGNJX;
    end
    `RV32_FMIN_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFMIN;
    end
    `RV32_FMAX_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFMAX;
    end
    // i2f signed
    `RV32_FCVT_S_W: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFCVT_S_W;
    end
    // i2f unsigned
    `RV32_FCVT_S_WU: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFCVT_S_WU;
    end
    // move i->f
    `RV32_FMV_W_X: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFMV_W_X;
    end
    `RV32_FMADD_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFMADD;
    end
    `RV32_FMSUB_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFMSUB;
    end
    `RV32_FNMSUB_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFNMSUB;
    end
    `RV32_FNMADD_S: begin
      fp_decode_o.is_fpu_float_op = 1'b1;
      fp_decode_o.fpu_float_op = eFNMADD;
    end
    `RV32_FDIV_S: begin
      fp_decode_o.is_fdiv_op = 1'b1;
    end
    `RV32_FSQRT_S: begin
      fp_decode_o.is_fsqrt_op = 1'b1;
    end
    `RV32_FEQ_S: begin
      fp_decode_o.is_fpu_int_op = 1'b1;
      fp_decode_o.fpu_int_op = eFEQ;
    end
    `RV32_FLE_S: begin
      fp_decode_o.is_fpu_int_op = 1'b1;
      fp_decode_o.fpu_int_op = eFLE;
    end
    `RV32_FLT_S: begin
      fp_decode_o.is_fpu_int_op = 1'b1;
      fp_decode_o.fpu_int_op = eFLT;
    end
    // f2i signed
    `RV32_FCVT_W_S: begin
      fp_decode_o.is_fpu_int_op = 1'b1;
      fp_decode_o.fpu_int_op = eFCVT_W_S;
    end
    // f2i unsigned
    `RV32_FCVT_WU_S: begin
      fp_decode_o.is_fpu_int_op = 1'b1;
      fp_decode_o.fpu_int_op = eFCVT_WU_S;
    end
    `RV32_FCLASS_S: begin
      fp_decode_o.is_fpu_int_op = 1'b1;
      fp_decode_o.fpu_int_op = eFCLASS;
    end
    // move f->i
    `RV32_FMV_X_W: begin
      fp_decode_o.is_fpu_int_op = 1'b1;
      fp_decode_o.fpu_int_op = eFMV_X_W;
    end
    default: begin
      fp_decode_o.is_fpu_float_op = 1'b0;
      fp_decode_o.is_fpu_int_op = 1'b0;
      fp_decode_o.is_fdiv_op = 1'b0;
      fp_decode_o.is_fsqrt_op = 1'b0;
      fp_decode_o.fpu_float_op = eFADD;
      fp_decode_o.fpu_int_op = eFEQ;
    end
  endcase
end

endmodule

