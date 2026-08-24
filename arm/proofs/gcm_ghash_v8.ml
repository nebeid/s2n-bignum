(* ========================================================================= *)
(* gcm_ghash_v8 (AArch64, imported from aws-lc): GHASH over len = 16*n bytes. *)
(*                                                                           *)
(* Binary: arm/aes-gcm/gcm_ghash_v8.o  (305 instructions; the concatenation   *)
(* of aws-lc's gcm_ghash_v8 and its fallthrough target gcm_ghash_v8_4x).      *)
(*                                                                           *)
(* Structure of the routine:                                                 *)
(*   leg A (0x000..0x16f)  len < 64: 2-blocks-per-pass .Loop_mod2x_v8 plus    *)
(*                         the .Lodd_tail_v8 single-block finisher.           *)
(*   leg B (0x170..0x4cc)  len >= 64: the 4-blocks-per-pass .Loop4x with its  *)
(*                         .Ltail4x / .Lone / .Ltwo / .Lthree cascade.        *)
(*                                                                           *)
(* NOTE (decode gap, leg B only): four of the 305 instruction words are       *)
(* 3-/4-register LD1 multiple-structure forms that arm/proofs/decode.ml does  *)
(* NOT model (0x4cdf6c34 @0x174, 0x4c406c3a @0x184, 0x4cdf2c44 @0x194+0x214,  *)
(* 0x4c406c44 @0x31c); only the 1-reg (0b0111) and 2-reg (0b1010 ->           *)
(* arm_ldstp_2q) forms exist, upstream included.  ARM_MK_EXEC_RULE RAISES on  *)
(* the full byte list, so this file builds its EXEC rule over the leg-A       *)
(* SLICE (0, 0x170) via mk_sublist_of_mc.  All 92 leg-A words decode cleanly. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/gmult_nblock_lemmas.ml";;
needs "common/ghash_nist_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code.  The literal is the full 305-word .text; the four           *)
(* unmodelled leg-B words carry a UNMODELLED-LD1-MULTI comment instead of an  *)
(* instruction (print_literal_from_elf itself raises on them).                *)
(* ------------------------------------------------------------------------- *)

let ghash_v8_mc = define_assert_from_elf "ghash_v8_mc"
  "arm/aes-gcm/gcm_ghash_v8.o"
[
  0xf101007f;       (* arm_CMP X3 (rvalue (word 64)) *)
  0x54000b62;       (* arm_BCS (word 364) *)
  0x4c407c00;       (* arm_LDR Q0 X0 No_Offset *)
  0xf1008063;       (* arm_SUBS X3 X3 (rvalue (word 32)) *)
  0xd280020c;       (* arm_MOV X12 (rvalue (word 16)) *)
  0x4cdfac34;       (* arm_LDP Q20 Q21 X1 (Postimmediate_Offset (word 32)) *)
  0x6e144294;       (* arm_EXT Q20 Q20 Q20 64 *)
  0x4f07e433;       (* arm_MOVI Q19 (word 16276538888567251425) *)
  0x4c407c36;       (* arm_LDR Q22 X1 No_Offset *)
  0x6e1642d6;       (* arm_EXT Q22 Q22 Q22 64 *)
  0x9a8c03ec;       (* arm_CSEL X12 XZR X12 Condition_EQ *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x4cdf7c50;       (* arm_LDR Q16 X2 (Postimmediate_Offset (word 16)) *)
  0x4f795673;       (* arm_SHL_VEC Q19 Q19 57 64 128 *)
  0x4e200a10;       (* arm_REV64_VEC Q16 Q16 8 *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x54000663;       (* arm_BCC (word 204) *)
  0x4ccc7c51;       (* arm_LDR Q17 X2 (Postreg_Offset X12) *)
  0x4e200a31;       (* arm_REV64_VEC Q17 Q17 8 *)
  0x6e114227;       (* arm_EXT Q7 Q17 Q17 64 *)
  0x6e201c63;       (* arm_EOR_VEC Q3 Q3 Q0 128 *)
  0x0ee7e284;       (* arm_PMULL_VEC Q4 Q20 Q7 64 *)
  0x6e271e31;       (* arm_EOR_VEC Q17 Q17 Q7 128 *)
  0x4ee7e286;       (* arm_PMULL2_VEC Q6 Q20 Q7 64 *)
  0x14000003;       (* arm_B (word 12) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0x6e034072;       (* arm_EXT Q18 Q3 Q3 64 *)
  0xf1008063;       (* arm_SUBS X3 X3 (rvalue (word 32)) *)
  0x0ee3e2c0;       (* arm_PMULL_VEC Q0 Q22 Q3 64 *)
  0x9a8c33ec;       (* arm_CSEL X12 XZR X12 Condition_CC *)
  0x0ef1e2a5;       (* arm_PMULL_VEC Q5 Q21 Q17 64 *)
  0x6e231e52;       (* arm_EOR_VEC Q18 Q18 Q3 128 *)
  0x4ee3e2c2;       (* arm_PMULL2_VEC Q2 Q22 Q3 64 *)
  0x6e241c00;       (* arm_EOR_VEC Q0 Q0 Q4 128 *)
  0x4ef2e2a1;       (* arm_PMULL2_VEC Q1 Q21 Q18 64 *)
  0x4ccc7c50;       (* arm_LDR Q16 X2 (Postreg_Offset X12) *)
  0x6e261c42;       (* arm_EOR_VEC Q2 Q2 Q6 128 *)
  0x9a8c03ec;       (* arm_CSEL X12 XZR X12 Condition_EQ *)
  0x6e251c21;       (* arm_EOR_VEC Q1 Q1 Q5 128 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4ccc7c51;       (* arm_LDR Q17 X2 (Postreg_Offset X12) *)
  0x4e200a10;       (* arm_REV64_VEC Q16 Q16 8 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x4e200a31;       (* arm_REV64_VEC Q17 Q17 8 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e114227;       (* arm_EXT Q7 Q17 Q17 64 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x0ee7e284;       (* arm_PMULL_VEC Q4 Q20 Q7 64 *)
  0x6e221c63;       (* arm_EOR_VEC Q3 Q3 Q2 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e321c63;       (* arm_EOR_VEC Q3 Q3 Q18 128 *)
  0x6e271e31;       (* arm_EOR_VEC Q17 Q17 Q7 128 *)
  0x6e201c63;       (* arm_EOR_VEC Q3 Q3 Q0 128 *)
  0x4ee7e286;       (* arm_PMULL2_VEC Q6 Q20 Q7 64 *)
  0x54fffbc2;       (* arm_BCS (word 2097016) *)
  0x6e321c42;       (* arm_EOR_VEC Q2 Q2 Q18 128 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0xb1008063;       (* arm_ADDS X3 X3 (rvalue (word 32)) *)
  0x6e221c00;       (* arm_EOR_VEC Q0 Q0 Q2 128 *)
  0x54000280;       (* arm_BEQ (word 80) *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x6e201c63;       (* arm_EOR_VEC Q3 Q3 Q0 128 *)
  0x6e321e11;       (* arm_EOR_VEC Q17 Q16 Q18 128 *)
  0x0ee3e280;       (* arm_PMULL_VEC Q0 Q20 Q3 64 *)
  0x6e231e31;       (* arm_EOR_VEC Q17 Q17 Q3 128 *)
  0x4ee3e282;       (* arm_PMULL2_VEC Q2 Q20 Q3 64 *)
  0x0ef1e2a1;       (* arm_PMULL_VEC Q1 Q21 Q17 64 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x4c007c00;       (* arm_STR Q0 X0 No_Offset *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd503201f;       (* arm_NOP *)
  0x4c407c00;       (* arm_LDR Q0 X0 No_Offset *)
  0x4cdf6c34;       (* UNMODELLED-LD1-MULTI *)
  0x6e144294;       (* arm_EXT Q20 Q20 Q20 64 *)
  0x6e1642d6;       (* arm_EXT Q22 Q22 Q22 64 *)
  0x4f07e433;       (* arm_MOVI Q19 (word 16276538888567251425) *)
  0x4c406c3a;       (* UNMODELLED-LD1-MULTI *)
  0x6e1a435a;       (* arm_EXT Q26 Q26 Q26 64 *)
  0x6e1c439c;       (* arm_EXT Q28 Q28 Q28 64 *)
  0x4f795673;       (* arm_SHL_VEC Q19 Q19 57 64 128 *)
  0x4cdf2c44;       (* UNMODELLED-LD1-MULTI *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x4e2008e7;       (* arm_REV64_VEC Q7 Q7 8 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x6e0740f9;       (* arm_EXT Q25 Q7 Q7 64 *)
  0x6e0640d8;       (* arm_EXT Q24 Q6 Q6 64 *)
  0x6e0540b7;       (* arm_EXT Q23 Q5 Q5 64 *)
  0x0ef9e29d;       (* arm_PMULL_VEC Q29 Q20 Q25 64 *)
  0x6e391ce7;       (* arm_EOR_VEC Q7 Q7 Q25 128 *)
  0x4ef9e29f;       (* arm_PMULL2_VEC Q31 Q20 Q25 64 *)
  0x0ee7e2be;       (* arm_PMULL_VEC Q30 Q21 Q7 64 *)
  0x0ef8e2d0;       (* arm_PMULL_VEC Q16 Q22 Q24 64 *)
  0x6e381cc6;       (* arm_EOR_VEC Q6 Q6 Q24 128 *)
  0x4ef8e2d8;       (* arm_PMULL2_VEC Q24 Q22 Q24 64 *)
  0x4ee6e2a6;       (* arm_PMULL2_VEC Q6 Q21 Q6 64 *)
  0x6e301fbd;       (* arm_EOR_VEC Q29 Q29 Q16 128 *)
  0x6e381fff;       (* arm_EOR_VEC Q31 Q31 Q24 128 *)
  0x6e261fde;       (* arm_EOR_VEC Q30 Q30 Q6 128 *)
  0x0ef7e347;       (* arm_PMULL_VEC Q7 Q26 Q23 64 *)
  0x6e371ca5;       (* arm_EOR_VEC Q5 Q5 Q23 128 *)
  0x4ef7e357;       (* arm_PMULL2_VEC Q23 Q26 Q23 64 *)
  0x0ee5e365;       (* arm_PMULL_VEC Q5 Q27 Q5 64 *)
  0x6e271fbd;       (* arm_EOR_VEC Q29 Q29 Q7 128 *)
  0x6e371fff;       (* arm_EOR_VEC Q31 Q31 Q23 128 *)
  0x6e251fde;       (* arm_EOR_VEC Q30 Q30 Q5 128 *)
  0xf1020063;       (* arm_SUBS X3 X3 (rvalue (word 128)) *)
  0x540006a3;       (* arm_BCC (word 212) *)
  0x14000002;       (* arm_B (word 8) *)
  0xd503201f;       (* arm_NOP *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x4cdf2c44;       (* UNMODELLED-LD1-MULTI *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x4e2008e7;       (* arm_REV64_VEC Q7 Q7 8 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x0ee3e380;       (* arm_PMULL_VEC Q0 Q28 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e382;       (* arm_PMULL2_VEC Q2 Q28 Q3 64 *)
  0x6e0740f9;       (* arm_EXT Q25 Q7 Q7 64 *)
  0x4ef0e361;       (* arm_PMULL2_VEC Q1 Q27 Q16 64 *)
  0x6e3d1c00;       (* arm_EOR_VEC Q0 Q0 Q29 128 *)
  0x6e3f1c42;       (* arm_EOR_VEC Q2 Q2 Q31 128 *)
  0x6e0640d8;       (* arm_EXT Q24 Q6 Q6 64 *)
  0x6e3e1c21;       (* arm_EOR_VEC Q1 Q1 Q30 128 *)
  0x6e0540b7;       (* arm_EXT Q23 Q5 Q5 64 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x0ef9e29d;       (* arm_PMULL_VEC Q29 Q20 Q25 64 *)
  0x6e391ce7;       (* arm_EOR_VEC Q7 Q7 Q25 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4ef9e29f;       (* arm_PMULL2_VEC Q31 Q20 Q25 64 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ee7e2be;       (* arm_PMULL_VEC Q30 Q21 Q7 64 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x0ef8e2d0;       (* arm_PMULL_VEC Q16 Q22 Q24 64 *)
  0x6e381cc6;       (* arm_EOR_VEC Q6 Q6 Q24 128 *)
  0x4ef8e2d8;       (* arm_PMULL2_VEC Q24 Q22 Q24 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x4ee6e2a6;       (* arm_PMULL2_VEC Q6 Q21 Q6 64 *)
  0x6e301fbd;       (* arm_EOR_VEC Q29 Q29 Q16 128 *)
  0x6e381fff;       (* arm_EOR_VEC Q31 Q31 Q24 128 *)
  0x6e261fde;       (* arm_EOR_VEC Q30 Q30 Q6 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x0ef7e347;       (* arm_PMULL_VEC Q7 Q26 Q23 64 *)
  0x6e371ca5;       (* arm_EOR_VEC Q5 Q5 Q23 128 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x4ef7e357;       (* arm_PMULL2_VEC Q23 Q26 Q23 64 *)
  0x0ee5e365;       (* arm_PMULL_VEC Q5 Q27 Q5 64 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x6e271fbd;       (* arm_EOR_VEC Q29 Q29 Q7 128 *)
  0x6e371fff;       (* arm_EOR_VEC Q31 Q31 Q23 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x6e251fde;       (* arm_EOR_VEC Q30 Q30 Q5 128 *)
  0xf1010063;       (* arm_SUBS X3 X3 (rvalue (word 64)) *)
  0x54fff9e2;       (* arm_BCS (word 2096956) *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x0ee3e380;       (* arm_PMULL_VEC Q0 Q28 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e382;       (* arm_PMULL2_VEC Q2 Q28 Q3 64 *)
  0x4ef0e361;       (* arm_PMULL2_VEC Q1 Q27 Q16 64 *)
  0x6e3d1c00;       (* arm_EOR_VEC Q0 Q0 Q29 128 *)
  0x6e3f1c42;       (* arm_EOR_VEC Q2 Q2 Q31 128 *)
  0x6e3e1c21;       (* arm_EOR_VEC Q1 Q1 Q30 128 *)
  0xb1010063;       (* arm_ADDS X3 X3 (rvalue (word 64)) *)
  0x54000c20;       (* arm_BEQ (word 388) *)
  0xf100807f;       (* arm_CMP X3 (rvalue (word 32)) *)
  0x54000943;       (* arm_BCC (word 296) *)
  0x54000520;       (* arm_BEQ (word 164) *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4c406c44;       (* UNMODELLED-LD1-MULTI *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e0640d8;       (* arm_EXT Q24 Q6 Q6 64 *)
  0x6e0540b7;       (* arm_EXT Q23 Q5 Q5 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x0ef8e29d;       (* arm_PMULL_VEC Q29 Q20 Q24 64 *)
  0x6e381cc6;       (* arm_EOR_VEC Q6 Q6 Q24 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x4ef8e29f;       (* arm_PMULL2_VEC Q31 Q20 Q24 64 *)
  0x0ee6e2be;       (* arm_PMULL_VEC Q30 Q21 Q6 64 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x0ef7e2c7;       (* arm_PMULL_VEC Q7 Q22 Q23 64 *)
  0x6e371ca5;       (* arm_EOR_VEC Q5 Q5 Q23 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x4ef7e2d7;       (* arm_PMULL2_VEC Q23 Q22 Q23 64 *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x4ee5e2a5;       (* arm_PMULL2_VEC Q5 Q21 Q5 64 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x6e271fbd;       (* arm_EOR_VEC Q29 Q29 Q7 128 *)
  0x6e371fff;       (* arm_EOR_VEC Q31 Q31 Q23 128 *)
  0x6e251fde;       (* arm_EOR_VEC Q30 Q30 Q5 128 *)
  0x0ee3e340;       (* arm_PMULL_VEC Q0 Q26 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e342;       (* arm_PMULL2_VEC Q2 Q26 Q3 64 *)
  0x0ef0e361;       (* arm_PMULL_VEC Q1 Q27 Q16 64 *)
  0x6e3d1c00;       (* arm_EOR_VEC Q0 Q0 Q29 128 *)
  0x6e3f1c42;       (* arm_EOR_VEC Q2 Q2 Q31 128 *)
  0x6e3e1c21;       (* arm_EOR_VEC Q1 Q1 Q30 128 *)
  0x14000036;       (* arm_B (word 216) *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4c40ac44;       (* arm_LDP Q4 Q5 X2 No_Offset *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e0540b7;       (* arm_EXT Q23 Q5 Q5 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x0ef7e29d;       (* arm_PMULL_VEC Q29 Q20 Q23 64 *)
  0x6e371ca5;       (* arm_EOR_VEC Q5 Q5 Q23 128 *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x4ef7e29f;       (* arm_PMULL2_VEC Q31 Q20 Q23 64 *)
  0x0ee5e2be;       (* arm_PMULL_VEC Q30 Q21 Q5 64 *)
  0x0ee3e2c0;       (* arm_PMULL_VEC Q0 Q22 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e2c2;       (* arm_PMULL2_VEC Q2 Q22 Q3 64 *)
  0x4ef0e2a1;       (* arm_PMULL2_VEC Q1 Q21 Q16 64 *)
  0x6e3d1c00;       (* arm_EOR_VEC Q0 Q0 Q29 128 *)
  0x6e3f1c42;       (* arm_EOR_VEC Q2 Q2 Q31 128 *)
  0x6e3e1c21;       (* arm_EOR_VEC Q1 Q1 Q30 128 *)
  0x14000017;       (* arm_B (word 92) *)
  0xd503201f;       (* arm_NOP *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4c407c44;       (* arm_LDR Q4 X2 No_Offset *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x0ee3e280;       (* arm_PMULL_VEC Q0 Q20 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e282;       (* arm_PMULL2_VEC Q2 Q20 Q3 64 *)
  0x0ef0e2a1;       (* arm_PMULL_VEC Q1 Q21 Q16 64 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x4c007c00;       (* arm_STR Q0 X0 No_Offset *)
  0xd65f03c0;       (* arm_RET X30 *)
];;

(* Length of the full machine code, needed by mk_sublist_of_mc. *)
let GHASH_V8_LENGTH = prove
 (`LENGTH ghash_v8_mc = 1220`,
  REWRITE_TAC[ghash_v8_mc] THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN REFL_TAC);;

(* Leg-A slice: bytes [0, 0x170).  ARM_MK_EXEC_RULE succeeds here (all 92
   words decode), whereas it raises on the full list -- see the header note. *)
let ghash_v8_lega_mc_def, ghash_v8_lega_mc, GHASH_V8_LEGA_EXEC =
  mk_sublist_of_mc "ghash_v8_lega_mc" ghash_v8_mc (`0`,`0x170`)
    GHASH_V8_LENGTH;;

(* ------------------------------------------------------------------------- *)
(* Spec vocabulary, lifted with provenance so this file's closure stays at    *)
(* base.ml + gmult_nblock_lemmas.ml + ghash_nist_bridge.ml (the 940 KB        *)
(* decrypt proof is deliberately NOT a dependency).                           *)
(* ------------------------------------------------------------------------- *)

(* From _docs/jargh_gcm/aes_gcm_enc_kernel_x4_ilp.ml:329, restricted to the 6
   slots this routine reads (Htable[0..5], 96 bytes).  h is the POLYVAL-side
   key; with h = ghash_twist H this is the x4 kernels' hypothesis shape. *)
let htable_mem_4 = new_definition
 `htable_mem_4 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s = byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128(h_power h 3)`;;

(* From arm/proofs/aesv8_gcm_8x_dec_256_wb.ml:7622 / ~:7626. *)
let BREV_RF8_128 = prove
 (`word_bytereverse (x:int128) = word_reversefields 8 x`,
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] WORD_BYTEREVERSE_REVERSEFIELDS]);;

let BREV_RF8_INV_128 = prove
 (`!x:int128. word_bytereverse (word_reversefields 8 x) = x`,
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* NOTE: `nist_input_block` (decrypt file :7646) is deliberately NOT lifted here.
   Its body needs `bytes_to_int128`, which lives in arm/proofs/utils/aes_ctr_spec.ml
   -- outside this file's three-`needs` closure.  The band statements below quantify
   the input block as an `int128` read directly, so it is not needed until the
   byte-list-shaped export in Phase 10; lift it (with its substrate) there.
   Lifting it here made `new_definition` raise "term not closed: bytes_to_int128",
   which `loadt` swallows -- every definition after it silently vanished. *)

(* ------------------------------------------------------------------------- *)
(* Byte-order pipeline: rev64 (per-lane byte reverse) composed with ext #8    *)
(* (byteswap128, i.e. the 64-bit lane exchange) is a full 128-bit reversal.   *)
(* Mined from the stale probe branch ghash-v8-symbolic-sim:                   *)
(* arm/proofs/ghash_v8_sim.ml:111-140.  All feasible at 128 bits (< 0.3s).    *)
(* ------------------------------------------------------------------------- *)

let rev64_128 = new_definition
 `rev64_128 (x:int128) : int128 =
    word_join (word_bytereverse (word_subword x (64,64) : 64 word))
              (word_bytereverse (word_subword x (0,64) : 64 word))`;;

let REV64_EXT8_IS_BYTEREVERSE = prove
 (`!x:int128. byteswap128(rev64_128 x) = word_bytereverse x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128; rev64_128] THEN BITBLAST_TAC);;

let EXT8_REV64_IS_BYTEREVERSE = prove
 (`!x:int128. rev64_128(byteswap128 x) = word_bytereverse x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128; rev64_128] THEN BITBLAST_TAC);;

let BYTEREVERSE128_INVOLUTION = prove
 (`!x:int128. word_bytereverse(word_bytereverse x) = x`,
  GEN_TAC THEN BITBLAST_TAC);;

let BYTEREVERSE128_XOR = prove
 (`!x y:int128. word_bytereverse(word_xor x y) =
                word_xor (word_bytereverse x) (word_bytereverse y)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* The single-block GHASH core, once the byte-swaps have cancelled. *)
let GHASH_1BLOCK_CORRECT = prove
 (`!acc block h:int128.
     polyval_dot (word_xor acc block) h = ghash_polyval_acc h acc [block]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_polyval_acc; polyval_dot]);;

(* ------------------------------------------------------------------------- *)
(* Scalar rung lemmas: which branch each n takes.                            *)
(*   leg A -- n in {1,2,3}: n=1 takes b.lo at 0x044 (16 - 32 borrows),        *)
(*   n=2 exits via b.eq at 0x10c, n=3 falls through to .Lodd_tail_v8.         *)
(*   leg B -- n >= 4: k+1 full .Loop4x groups plus a remainder r < 4.         *)
(* ------------------------------------------------------------------------- *)

let LEGA_RUNG = prove
 (`!n. 1 <= n /\ n <= 3
       ==> (16 * n < 32 <=> n = 1) /\
           (16 * n = 32 <=> n = 2) /\
           (16 * n = 48 <=> n = 3)`,
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let LEGB_RUNG = prove
 (`!n. 4 <= n ==> ?k r. r < 4 /\ n = 4 * (k + 1) + r`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(n - 4) DIV 4` THEN EXISTS_TAC `(n - 4) MOD 4` THEN
  MP_TAC(SPECL [`n - 4`; `4`] DIVISION) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Symbolic-simulation infrastructure for the leg-A bands.                    *)
(*                                                                           *)
(* CRITICAL ORDERING: EXT8_FOLD must be rewritten BEFORE                      *)
(* WORD_SIMPLE_SUBWORD_CONV.  The ARM `ext v,v,v,#8` emits                    *)
(* `word_subword (word_join x x : 256 word) (64,128)`; if the subword conv     *)
(* runs first it distributes that into a 256-bit byte tree, and any BITBLAST   *)
(* over such a tree exhausts memory and kills the HOL process.                *)
(* ------------------------------------------------------------------------- *)

let EXT8_FOLD = prove
 (`!x:int128. word_subword (word_join x x : 256 word) (64,128) = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_INVOLUTION = prove
 (`!x:int128. byteswap128(byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* The rev64 byte tree the stepper emits, folded back to `rev64_128`.  Built
   programmatically so the shape matches the stepper's output exactly. *)
let REV64_TREE_FOLD =
  let s8 x k = mk_comb(mk_comb(`word_subword:int128->num#num->8 word`,x),
                       mk_pair(mk_small_numeral k,`8`)) in
  let j16 a b = mk_comb(mk_comb(`word_join:8 word->8 word->16 word`,a),b) in
  let j32 a b = mk_comb(mk_comb(`word_join:16 word->16 word->32 word`,a),b) in
  let j64 a b = mk_comb(mk_comb(`word_join:32 word->32 word->64 word`,a),b) in
  let j128 a b = mk_comb(mk_comb(`word_join:64 word->64 word->128 word`,a),b) in
  let lane x b =
    j64 (j32 (j16 (s8 x b) (s8 x (b+8))) (j16 (s8 x (b+16)) (s8 x (b+24))))
        (j32 (j16 (s8 x (b+32)) (s8 x (b+40))) (j16 (s8 x (b+48)) (s8 x (b+56)))) in
  let revtree x = j128 (lane x 64) (lane x 0) in
  GEN_ALL(prove(mk_eq(revtree `x:int128`, `rev64_128 (x:int128)`),
    REWRITE_TAC[rev64_128] THEN CONV_TAC WORD_BLAST));;

(* Per-step normalizer.  It rewrites ONLY `read <reg> sN = <int128>`
   assumptions: a blanket RULE_ASSUM_TAC over every assumption mangles the
   `read PC sN = ...` fact, and the next ARM_STEPS_TAC then dies with
   "ARM_CONV: can't find `read PC .. = ..` from ths". *)
let Q128_NORM_TAC =
  let core = TOP_DEPTH_CONV(REWR_CONV EXT8_FOLD) THENC
             REWRITE_CONV[BYTESWAP128_INVOLUTION] THENC
             TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
             TOP_DEPTH_CONV(REWR_CONV EXT8_FOLD) THENC
             REWRITE_CONV[BYTESWAP128_INVOLUTION; REV64_TREE_FOLD;
                          REV64_EXT8_IS_BYTEREVERSE; EXT8_REV64_IS_BYTEREVERSE;
                          BYTEREVERSE128_INVOLUTION] in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && type_of(rhs c) = `:int128` &&
       (try (let l = lhs c in is_comb l &&
             (let f = rator l in is_comb f &&
              fst(dest_const(fst(strip_comb f))) = "read")) with _ -> false)
    then CONV_RULE(RAND_CONV core) th else th);;

(* ------------------------------------------------------------------------- *)
(* Phase 2, step 1: the n = 1 (.Lodd_tail_v8) band, PC-only postcondition.    *)
(*                                                                           *)
(* This pins the CONTROL FLOW of the single-block path, harvested from the    *)
(* live simulation (40 steps, ~29s, hyps = 0):                                *)
(*   s3  : `b.cs` @0x004 falls through (16 < 64).                             *)
(*   s18 : `b.lo` @0x044 IS taken -> PC = pc+0x110 = .Lodd_tail_v8, with      *)
(*         Q0 = word_bytereverse xi, Q3 = word_bytereverse blk0,              *)
(*         Q16 = rev64_128 blk0, Q20 = h_power h 0, Q22 = h_power h 1.        *)
(*   s26 : the Karatsuba triple is formed and separable --                    *)
(*         Q3 = xi' XOR blk0', Q0/Q2 = the lo/hi pmulls against h_power h 0.  *)
(*   s40 : PC = pc+0x168, the `ret`.                                          *)
(*                                                                           *)
(* The GHASH algebra close (upgrading the postcondition to the nist_ghash     *)
(* statement) is the next step; this theorem is what it will be built on.     *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LE1BLOCK_PCONLY = prove
 (`!xi_p htbl_p in_p pc h xi blk0.
     nonoverlapping (word pc, LENGTH ghash_v8_lega_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_lega_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word 16] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               read (memory :> bytes128 in_p) s = blk0 /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x168))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[C_ARGUMENTS; htable_mem_4; fst GHASH_V8_LEGA_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_V8_LEGA_EXEC (1--3) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC GHASH_V8_LEGA_EXEC [n] THEN Q128_NORM_TAC)
            (4--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Algebra-close ingredients for the n = 1 band's GHASH postcondition.        *)
(*                                                                           *)
(* The value the assembly leaves in Q0 (and stores at xi_p) at s40 is         *)
(* `word_bytereverse (<byteform>)`, where <byteform> is a 3-summand XOR built *)
(* from exactly the atoms `build_GMULTn_fast 1` produces (the two `h_power h  *)
(* 0` lane pmulls, `karatsuba_mid (h_power h 0)`, and the reduce constant     *)
(* `word 13979173243358019584` = 0xC200000000000000).  The four lemmas below  *)
(* were measured against the LIVE s40 term and each fires; they are what the  *)
(* close needs beyond `build_GMULTn_fast 1` itself.                          *)
(*                                                                           *)
(* THE TYPE GOTCHA: `arm_INS` at 0x140/0x144 emits `word_insert` whose        *)
(* INSERTED argument is an `int128`, not a `64 word`.  A 64-bit-typed         *)
(* ins->join lemma silently fails to rewrite (`Failure "type_match"`), so     *)
(* BOTH width variants are needed.                                           *)
(* ------------------------------------------------------------------------- *)

let INS_TO_JOIN = prove
 (`!(x:int128) (y:64 word). word_insert x (0,64) y : int128 =
     word_join (word_subword x (64,64) : 64 word) y`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INS_HI_TO_JOIN = prove
 (`!(x:int128) (y:64 word). word_insert x (64,64) y : int128 =
     word_join y (word_subword x (0,64) : 64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INS128_TO_JOIN = prove
 (`!(x:int128) (y:int128). word_insert x (0,64) y : int128 =
     word_join (word_subword x (64,64) : 64 word) (word_subword y (0,64) : 64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INS128_HI_TO_JOIN = prove
 (`!(x:int128) (y:int128). word_insert x (64,64) y : int128 =
     word_join (word_subword y (0,64) : 64 word) (word_subword x (0,64) : 64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The Karatsuba MID operand.  `eor v17,v16,v18` at 0x118 mixes the un-ext'd
   input register (rev64_128 blk0) with the ext'd accumulator, so the machine's
   mid input is NOT syntactically `karatsuba_mid`'s `lo XOR hi` shape.  This
   collapses it to exactly that shape (BITBLAST at 128 bits, ~2.2s). *)
let MID_FOLD = prove
 (`!(xi:int128) (blk0:int128).
     word_subword
       (word_xor (word_xor (word_bytereverse xi) (word_bytereverse blk0))
                 (word_xor (byteswap128 (word_bytereverse xi)) (rev64_128 blk0)))
       (0,64) : 64 word =
     word_xor
       (word_subword (word_xor (word_bytereverse xi) (word_bytereverse blk0))
                     (0,64) : 64 word)
       (word_subword (word_xor (word_bytereverse xi) (word_bytereverse blk0))
                     (64,64) : 64 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byteswap128; rev64_128] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The two lemmas that finish the n = 1 algebra close.                        *)
(*                                                                           *)
(* Both are stated over OPAQUE 128-bit atoms p1/p2/p3, which stand for the    *)
(* three Karatsuba partial products                                          *)
(*   p1 = pmul (mid H) (mid B),  p2 = pmul (lo H) (lo B),  p3 = pmul (hi H) (hi B)  *)
(* where H = h_power h 0 and B = xi' XOR blk0'.  Abstracting the pmuls is     *)
(* what makes these tractable: the raw machine-vs-spec diff is 4054 vs 3525   *)
(* chars, but over the abstracted atoms it is 397 vs 314, and `word_pmul` is  *)
(* opaque to BITBLAST anyway, so nothing is lost by hiding it.                *)
(*                                                                           *)
(* ARG_EQ: the two spellings of the reduce step's 64-bit argument agree.  The *)
(* machine builds it as `xor <wa> (join ...)` with a doubly-nested subword on *)
(* the low lane; build_GMULTn_fast states it as `xor (join ...) <wa>`.        *)
(* GHASH1_ALIGN: with that in hand, the whole 3-summand XOR aligns -- pure    *)
(* XOR/word_join/word_subword bookkeeping, ~1.7s at 128 bits.                 *)
(* ------------------------------------------------------------------------- *)

let ARG_EQ = prove
 (`!p1 p2 p3 p4:int128. ((word_subword ((word_xor (p4:(128)word) ((word_join 
     ((word_subword ((word_subword (p2:(128)word) (0,64)):(128)word) (0,64)):(64)word) 
     ((word_subword ((word_xor ((word_xor (p3:(128)word) (p2:(128)word)):(128)word) 
     ((word_xor ((word_subword ((word_join (p3:(128)word) (p2:(128)word)):(256)word) 
     (64,128)):(128)word) (p1:(128)word)):(128)word)):(128)word) (0,64)):(64)word)):(128)word)):(128)word) 
     (0,64)):(64)word) = ((word_subword ((word_xor ((word_join ((word_subword 
     (p2:(128)word) (0,64)):(64)word) ((word_xor ((word_subword (p2:(128)word) 
     (64,64)):(64)word) ((word_subword ((word_xor ((word_xor (p1:(128)word) 
     (p2:(128)word)):(128)word) (p3:(128)word)):(128)word) (0,64)):(64)word)):(64)word)):(128)word) 
     (p4:(128)word)):(128)word) (0,64)):(64)word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let GHASH1_ALIGN = prove
 (`!p1 p2 p3:int128. ((word_xor ((word_xor ((word_join ((word_subword (p3:(128)word) 
     (64,64)):(64)word) ((word_subword ((word_subword ((word_xor ((word_xor 
     (p3:(128)word) (p2:(128)word)):(128)word) ((word_xor ((word_subword 
     ((word_join (p3:(128)word) (p2:(128)word)):(256)word) (64,128)):(128)word) 
     (p1:(128)word)):(128)word)):(128)word) (64,64)):(128)word) (0,64)):(64)word)):(128)word) 
     (byteswap128 ((word_xor ((word_pmul ((word_subword (p2:(128)word) (0,64)):(64)word) 
     ((word 13979173243358019584):(64)word)):(128)word) ((word_join ((word_subword 
     ((word_subword (p2:(128)word) (0,64)):(128)word) (0,64)):(64)word) ((word_subword 
     ((word_xor ((word_xor (p3:(128)word) (p2:(128)word)):(128)word) ((word_xor 
     ((word_subword ((word_join (p3:(128)word) (p2:(128)word)):(256)word) 
     (64,128)):(128)word) (p1:(128)word)):(128)word)):(128)word) (0,64)):(64)word)):(128)word)):(128)word))):(128)word) 
     ((word_pmul ((word_subword ((word_xor ((word_pmul ((word_subword (p2:(128)word) 
     (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word) 
     ((word_join ((word_subword ((word_subword (p2:(128)word) (0,64)):(128)word) 
     (0,64)):(64)word) ((word_subword ((word_xor ((word_xor (p3:(128)word) 
     (p2:(128)word)):(128)word) ((word_xor ((word_subword ((word_join (p3:(128)word) 
     (p2:(128)word)):(256)word) (64,128)):(128)word) (p1:(128)word)):(128)word)):(128)word) 
     (0,64)):(64)word)):(128)word)):(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)):(128)word) 
     = ((word_xor ((word_pmul ((word_subword ((word_xor ((word_join ((word_subword 
     (p2:(128)word) (0,64)):(64)word) ((word_xor ((word_subword (p2:(128)word) 
     (64,64)):(64)word) ((word_subword ((word_xor ((word_xor (p1:(128)word) 
     (p2:(128)word)):(128)word) (p3:(128)word)):(128)word) (0,64)):(64)word)):(64)word)):(128)word) 
     ((word_pmul ((word_subword (p2:(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)):(128)word) 
     (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word) 
     ((word_xor (byteswap128 ((word_xor ((word_join ((word_subword (p2:(128)word) 
     (0,64)):(64)word) ((word_xor ((word_subword (p2:(128)word) (64,64)):(64)word) 
     ((word_subword ((word_xor ((word_xor (p1:(128)word) (p2:(128)word)):(128)word) 
     (p3:(128)word)):(128)word) (0,64)):(64)word)):(64)word)):(128)word) 
     ((word_pmul ((word_subword (p2:(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)):(128)word)) 
     ((word_join ((word_subword (p3:(128)word) (64,64)):(64)word) ((word_xor 
     ((word_subword (p3:(128)word) (0,64)):(64)word) ((word_subword ((word_xor 
     ((word_xor (p1:(128)word) (p2:(128)word)):(128)word) (p3:(128)word)):(128)word) 
     (64,64)):(64)word)):(64)word)):(128)word)):(128)word)):(128)word)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `(p4:int128) = ((word_pmul ((word_subword (p2:(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)` THEN
  REWRITE_TAC[ARG_EQ] THEN
  ABBREV_TAC `(p5:int128) = ((word_pmul ((word_subword ((word_xor ((word_join ((word_subword (p2:(128)word) (0,64)):(64)word) ((word_xor ((word_subword (p2:(128)word) (64,64)):(64)word) ((word_subword ((word_xor ((word_xor (p1:(128)word) (p2:(128)word)):(128)word) (p3:(128)word)):(128)word) (0,64)):(64)word)):(64)word)):(128)word) (p4:(128)word)):(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)` THEN
  REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

(* The spec-level chain, from the reduce output to the exported NIST vocabulary.
   `h_power h 0 = h` turns the reduce into `polyval_dot`, WORD_PMUL_SYM puts the
   accumulator on the left where `GHASH_1BLOCK_CORRECT` expects it, and
   `NIST_GHASH_IS_POLYVAL` (common/ghash_nist_bridge.ml) lands in `nist_ghash`. *)
let GHASH1_SPEC_CHAIN = prove
 (`!(H:int128) (h:int128) (xi:int128) (blk0:int128).
     h = ghash_twist H
     ==> polyval_reduce_prop3
           (word_pmul (h_power h 0)
                      (word_xor (word_bytereverse xi) (word_bytereverse blk0))) =
         nist_ghash H (word_bytereverse xi) [word_bytereverse blk0]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  ASM_REWRITE_TAC[GSYM GHASH_1BLOCK_CORRECT] THEN
  REWRITE_TAC[polyval_dot; h_power] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_PMUL_SYM] THEN
  REFL_TAC);;
