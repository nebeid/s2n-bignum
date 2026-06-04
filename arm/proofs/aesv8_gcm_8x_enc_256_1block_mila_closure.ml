(* ========================================================================= *)
(* Functional correctness proof for aesv8_gcm_8x_enc_256 1-block path.       *)
(* Proves BOTH ciphertext output AND GHASH tag update.                       *)
(* No CHEAT_TAC, no new axioms.                                              *)
(* WARNING: GHASH closure uses ABBREV_ALL_PMUL_TAC + WORD_BLAST on the full  *)
(* REV64 term tree (~145k chars). This may take >15min or fail on slower     *)
(* machines. A faster approach using per-step SIMD simplification (Mila's    *)
(* pattern) is documented in _docs/ghash-proof-strategy-2026-06-02.md.       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
needs "common/karatsuba_pmul.ml";;
needs "common/polyval_ghash.ml";;

(* Machine code definition *)
let aesv8_gcm_8x_enc_256_mc = define_assert_from_elf "aesv8_gcm_8x_enc_256_mc"
  "arm/aes-gcm/aesv8_gcm_8x_enc_256.o"
[
  0xd503201f;       (* arm_NOP *)
  0xb4008f61;       (* arm_CBZ X1 (word 4588) *)
  0x6dbb27e8;       (* arm_STP D8 D9 SP (Preimmediate_Offset (iword (-- &80))) *)
  0xd343fc29;       (* arm_LSR X9 X1 3 *)
  0xaa0403f0;       (* arm_MOV X16 X4 *)
  0xaa0503eb;       (* arm_MOV X11 X5 *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0xd2f84005;       (* arm_MOVZ X5 (word 49664) 48 *)
  0xa9047fe5;       (* arm_STP X5 XZR SP (Immediate_Offset (iword (&64))) *)
  0x910103ea;       (* arm_ADD X10 SP (rvalue (word 64)) *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xaa0903e5;       (* arm_MOV X5 X9 *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x6e20081e;       (* arm_REV32_VEC Q30 Q0 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x540054aa;       (* arm_BGE (word 2708) *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce007108;       (* arm_EOR3 Q8 Q8 Q0 Q28 *)
  0x6e200bc0;       (* arm_REV32_VEC Q0 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce017129;       (* arm_EOR3 Q9 Q9 Q1 Q28 *)
  0xce03716b;       (* arm_EOR3 Q11 Q11 Q3 Q28 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac812448;       (* arm_STP Q8 Q9 X2 (Postimmediate_Offset (iword (&32))) *)
  0xac812c4a;       (* arm_STP Q10 Q11 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0xce0771ef;       (* arm_EOR3 Q15 Q15 Q7 Q28 *)
  0xce0671ce;       (* arm_EOR3 Q14 Q14 Q6 Q28 *)
  0xce0571ad;       (* arm_EOR3 Q13 Q13 Q5 Q28 *)
  0xac81344c;       (* arm_STP Q12 Q13 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0xac813c4e;       (* arm_STP Q14 Q15 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x54002aaa;       (* arm_BGE (word 1364) *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e200bd4;       (* arm_REV32_VEC Q20 Q30 8 *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e200bd6;       (* arm_REV32_VEC Q22 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x6e200bd7;       (* arm_REV32_VEC Q23 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0x6e200bd9;       (* arm_REV32_VEC Q25 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0xce0571ad;       (* arm_EOR3 Q13 Q13 Q5 Q28 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0xce03716b;       (* arm_EOR3 Q11 Q11 Q3 Q28 *)
  0x4eb91f23;       (* arm_MOV_VEC Q3 Q25 128 *)
  0xce017129;       (* arm_EOR3 Q9 Q9 Q1 Q28 *)
  0xce007108;       (* arm_EOR3 Q8 Q8 Q0 Q28 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac812448;       (* arm_STP Q8 Q9 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb71ee2;       (* arm_MOV_VEC Q2 Q23 128 *)
  0xce0771ef;       (* arm_EOR3 Q15 Q15 Q7 Q28 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0xac812c4a;       (* arm_STP Q10 Q11 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0671ce;       (* arm_EOR3 Q14 Q14 Q6 Q28 *)
  0x4eb61ec1;       (* arm_MOV_VEC Q1 Q22 128 *)
  0xac81344c;       (* arm_STP Q12 Q13 X2 (Postimmediate_Offset (iword (&32))) *)
  0xac813c4e;       (* arm_STP Q14 Q15 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb41e80;       (* arm_MOV_VEC Q0 Q20 128 *)
  0x54ffd5ab;       (* arm_BLT (word 2095796) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0xad4564d8;       (* arm_LDP Q24 Q25 X6 (Immediate_Offset (iword (&160))) *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0xad4354d4;       (* arm_LDP Q20 Q21 X6 (Immediate_Offset (iword (&96))) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0xad445cd6;       (* arm_LDP Q22 Q23 X6 (Immediate_Offset (iword (&128))) *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xf101c0bf;       (* arm_CMP X5 (rvalue (word 112)) *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x540005ec;       (* arm_BGT (word 188) *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea21c43;       (* arm_MOV_VEC Q3 Q2 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea11c22;       (* arm_MOV_VEC Q2 Q1 128 *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0xf10180bf;       (* arm_CMP X5 (rvalue (word 96)) *)
  0x540005ec;       (* arm_BGT (word 188) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540006ac;       (* arm_BGT (word 212) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x540007ac;       (* arm_BGT (word 244) *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540008ac;       (* arm_BGT (word 276) *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x54000a0c;       (* arm_BGT (word 320) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x54000b6c;       (* arm_BGT (word 364) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x14000069;       (* arm_B (word 420) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x6e084712;       (* arm_INS Q18 Q24 0 64 64 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0xce027529;       (* arm_EOR3 Q9 Q9 Q2 Q29 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce037529;       (* arm_EOR3 Q9 Q9 Q3 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0xce047529;       (* arm_EOR3 Q9 Q9 Q4 Q29 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef5e37b;       (* arm_PMULL_VEC Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef8e37b;       (* arm_PMULL2_VEC Q27 Q27 Q24 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0xce057529;       (* arm_EOR3 Q9 Q9 Q5 Q29 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0xce067529;       (* arm_EOR3 Q9 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0xce077529;       (* arm_EOR3 Q9 Q9 Q7 Q29 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x92401821;       (* arm_AND X1 X1 (rvalue (word 127)) *)
  0xd1020021;       (* arm_SUB X1 X1 (rvalue (word 128)) *)
  0xcb0103e1;       (* arm_NEG X1 X1 *)
  0xaa3f03e7;       (* arm_MVN X7 XZR *)
  0x92401821;       (* arm_AND X1 X1 (rvalue (word 127)) *)
  0x9ac124e7;       (* arm_LSRV X7 X7 X1 *)
  0xf101003f;       (* arm_CMP X1 (rvalue (word 64)) *)
  0xaa3f03e8;       (* arm_MVN X8 XZR *)
  0x9a9fb0ee;       (* arm_CSEL X14 X7 XZR Condition_LT *)
  0x9a87b10d;       (* arm_CSEL X13 X8 X7 Condition_LT *)
  0x4e081da0;       (* arm_INS_GEN Q0 X13 0 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4c40705a;       (* arm_LDR Q26 X2 No_Offset *)
  0x4e181dc0;       (* arm_INS_GEN Q0 X14 64 64 *)
  0x4e201d29;       (* arm_AND_VEC Q9 Q9 Q0 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x6ee01f49;       (* arm_BIF Q9 Q26 Q0 128 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0xce115673;       (* arm_EOR3 Q19 Q19 Q17 Q21 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6cc527e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&80))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x52800000;       (* arm_MOV W0 (rvalue (word 0)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AESV8_GCM_8X_ENC_256_EXEC = ARM_MK_EXEC_RULE aesv8_gcm_8x_enc_256_mc;;

(* ------------------------------------------------------------------------- *)
(* SIMD REV64 fold-back lemmas (ported from Mila's gcm_gmult_v8_spec.ml,     *)
(* branch mila-gcm_gmult_proof).  The ARM simulator expands REV64.16B into a *)
(* 4-level nested word_join/word_subword byte tree (128->64->32->16->8).     *)
(* These collapse it back to word_reversefields 8 the instant it appears, so *)
(* the giant (~145k char) term never forms and the final closure is fast.    *)
(* ------------------------------------------------------------------------- *)

let REV64_LOWER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (0,8):(8)word) (word_subword xi (8,8):(8)word):(16)word)
                 (word_join (word_subword xi (16,8):(8)word) (word_subword xi (24,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (32,8):(8)word) (word_subword xi (40,8):(8)word):(16)word)
                 (word_join (word_subword xi (48,8):(8)word) (word_subword xi (56,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (0,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_UPPER_LANE = prove(
  `!(xi:(128)word).
    word_join
      (word_join (word_join (word_subword xi (64,8):(8)word) (word_subword xi (72,8):(8)word):(16)word)
                 (word_join (word_subword xi (80,8):(8)word) (word_subword xi (88,8):(8)word):(16)word):(32)word)
      (word_join (word_join (word_subword xi (96,8):(8)word) (word_subword xi (104,8):(8)word):(16)word)
                 (word_join (word_subword xi (112,8):(8)word) (word_subword xi (120,8):(8)word):(16)word):(32)word):(64)word =
    word_reversefields 8 (word_subword xi (64,64):(64)word)`,
  CONV_TAC WORD_BLAST);;

let REV64_128 = prove(
  `!(xi:(128)word).
    word_join
      (word_reversefields 8 (word_subword xi (64,64):(64)word))
      (word_reversefields 8 (word_subword xi (0,64):(64)word)):(128)word =
    word_subword (word_join (word_reversefields 8 xi:(128)word)
                            (word_reversefields 8 xi:(128)word):(256)word) (64,128)`,
  CONV_TAC WORD_BLAST);;

let WORD_SWAP_HALVES_INVOLUTION = prove(
  `!(a:(128)word).
    word_subword
      (word_join
        (word_subword (word_join a a:(256)word) (64,128):(128)word)
        (word_subword (word_join a a:(256)word) (64,128):(128)word):(256)word)
      (64,128):(128)word = a`,
  CONV_TAC WORD_BLAST);;

(* The xi_p store value is the per-lane byte-reverse of the GHASH result R
   (rev64 on each 64-bit lane); that equals word_bytereverse of the whole 128. *)
let REV64_LANES_EQ = prove(
  `!R:int128. word_join (word_reversefields 8 (word_subword R (0,64):(64)word))
                        (word_reversefields 8 (word_subword R (64,64):(64)word)):(128)word =
              word_bytereverse R`,
  CONV_TAC WORD_BLAST);;

(* Structural normalization lemmas for the GHASH bridge close (from the standalone
   gcm_gmult_v8 proof).  word_insert comes from the INS instr, nested word_subword
   from the EXT instr.  byteswap128 = pure 64-bit half-swap. *)
let WORD_INSERT_SUBWORD = prove(
  `(!x:int128 y:64 word. word_subword (word_insert x (0,64) y : int128) (64,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128 y:64 word. word_subword (word_insert x (64,64) y : int128) (0,64) : 64 word = word_subword x (0,64)) /\
   (!x:int128 y:64 word. word_subword (word_insert x (0,64) y : int128) (0,64) : 64 word = y) /\
   (!x:int128 y:64 word. word_subword (word_insert x (64,64) y : int128) (64,64) : 64 word = y)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let WORD_SUBWORD_SUBWORD = prove(
  `(!x:int128. word_subword (word_subword x (0,128) : int128) (0,64) : 64 word = word_subword x (0,64)) /\
   (!x:int128. word_subword (word_subword x (0,128) : int128) (64,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128. word_subword (word_subword x (64,128) : int128) (0,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128. word_subword (word_subword x (0,64) : 64 word) (0,64) : 64 word = word_subword x (0,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* GHASH bridge lemmas (recovered from the standalone gcm_gmult proof).       *)
(* These prove the Karatsuba + Prop3 reduction the assembly computes equals   *)
(* the spec-level polyval_dot / ghash_polyval_acc, so the symbolic Q19 result *)
(* at the xi_p store can be bridged to the postcondition.  All are BITBLAST / *)
(* WORD_RULE proofs (no CHEAT, no axioms).                                    *)
(* ------------------------------------------------------------------------- *)

let KARATSUBA_LIMBS = prove(
  `!(p_lo:int128) (p_hi:int128) (cross:int128).
   let t:(256)word = word_xor (word_xor (word_zx p_lo)
                                        (word_shl (word_zx cross) 64))
                              (word_shl (word_zx p_hi) 128) in
   word_subword t (0,64) : 64 word = word_subword p_lo (0,64) /\
   word_subword t (64,64) : 64 word = word_xor (word_subword p_lo (64,64))
                                               (word_subword cross (0,64)) /\
   word_subword t (128,64) : 64 word = word_xor (word_subword p_hi (0,64))
                                                (word_subword cross (64,64)) /\
   word_subword t (192,64) : 64 word = word_subword p_hi (64,64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

let JOIN_SUBWORD_RULES = prove(
  `(!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
   (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let WORD_XOR_ACI = WORD_RULE
  `(!x y:N word. word_xor x y = word_xor y x) /\
   (!x y z:N word. word_xor (word_xor x y) z = word_xor x (word_xor y z)) /\
   (!x y z:N word. word_xor x (word_xor y z) = word_xor y (word_xor x z))`;;

let GHASH_1BLOCK_CORRECT = prove(
  `!acc block h:int128.
    polyval_dot (word_xor acc block) h = ghash_polyval_acc h acc [block]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_polyval_acc; polyval_dot]);;

let BYTESWAP128_INVOLUTION = prove(
  `!x:int128. byteswap128(byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

let BYTEREVERSE128_XOR = prove(
  `!x y:int128. word_bytereverse(word_xor x y) =
                word_xor (word_bytereverse x) (word_bytereverse y)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* The full GHASH multiply+reduce bridge: the byte-level Karatsuba/Prop3 the   *)
(* assembly computes (left-hand side, in terms of 64-bit pmul limbs) equals    *)
(* the spec-level polyval_dot.                                                 *)
let GMULT_FULL_CORRECT_BA = prove(
  `!a b:int128.
   let a_lo = word_subword a (0,64) : 64 word in
   let a_hi = word_subword a (64,64) : 64 word in
   let b_lo = word_subword b (0,64) : 64 word in
   let b_hi = word_subword b (64,64) : 64 word in
   let p_lo:int128 = word_pmul b_lo a_lo in
   let p_hi:int128 = word_pmul b_hi a_hi in
   let p_mid:int128 = word_pmul (word_xor b_lo b_hi) (word_xor a_lo a_hi) in
   let cross = word_xor (word_xor p_mid p_lo) p_hi in
   let bb = word_xor (word_subword p_lo (64,64) : 64 word)
                     (word_subword cross (0,64) : 64 word) in
   let cc = word_xor (word_subword p_hi (0,64) : 64 word)
                     (word_subword cross (64,64) : 64 word) in
   let aa = word_subword p_lo (0,64) : 64 word in
   let dd = word_subword p_hi (64,64) : 64 word in
   let w:64 word = word 13979173243358019584 in
   let wa:int128 = word_pmul aa w in
   let v0:int128 = word_xor (word_join aa bb) wa in
   let wv:int128 = word_pmul (word_subword v0 (0,64) : 64 word) w in
   let result:int128 = word_xor wv (word_xor (byteswap128 v0) (word_join dd cc)) in
   result = polyval_dot a b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; polyval_dot] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  REWRITE_TAC[polyval_reduce_prop3; LET_DEF; LET_END_DEF; byteswap128] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_LIMBS] THEN
  SUBGOAL_THEN
    `(!x y:int128. word_subword (word_xor x y) (0,64) : 64 word =
      word_xor (word_subword x (0,64)) (word_subword y (0,64))) /\
     (!x y:int128. word_subword (word_xor x y) (64,64) : 64 word =
      word_xor (word_subword x (64,64)) (word_subword y (64,64))) /\
     (!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
     (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`
    (fun th -> REWRITE_TAC[th]) THENL
  [REPEAT CONJ_TAC THEN TRY(REPEAT GEN_TAC) THEN BITBLAST_TAC; ALL_TAC] THEN
  CONV_TAC(DEPTH_CONV(REWR_CONV(CONJUNCT1 JOIN_SUBWORD_RULES))) THEN
  REWRITE_TAC[WORD_XOR_ACI; WORD_PMUL_SYM] THEN
  ABBREV_TAC `p_lo:int128 = word_pmul (word_subword (a:int128) (0,64) : 64 word)
    (word_subword (b:int128) (0,64) : 64 word)` THEN
  ABBREV_TAC `p_hi:int128 = word_pmul (word_subword (a:int128) (64,64) : 64 word)
    (word_subword (b:int128) (64,64) : 64 word)` THEN
  ABBREV_TAC `p_mid:int128 = word_pmul
    (word_xor (word_subword (a:int128) (64,64) : 64 word) (word_subword a (0,64) : 64 word))
    (word_xor (word_subword (b:int128) (64,64) : 64 word) (word_subword b (0,64) : 64 word))` THEN
  ABBREV_TAC `wa:int128 = word_pmul (word_subword (p_lo:int128) (0,64) : 64 word)
    (word 13979173243358019584 : 64 word)` THEN
  ABBREV_TAC `wv:int128 = word_pmul
    (word_xor (word_subword (p_hi:int128) (0,64) : 64 word)
    (word_xor (word_subword (p_lo:int128) (64,64) : 64 word)
    (word_xor (word_subword p_lo (0,64) : 64 word)
    (word_xor (word_subword (wa:int128) (0,64) : 64 word)
              (word_subword (p_mid:int128) (0,64) : 64 word)))))
    (word 13979173243358019584 : 64 word)` THEN
  BITBLAST_TAC);;

let SIMD_SIMPLIFY_RULES = [REV64_LOWER_LANE; REV64_UPPER_LANE; REV64_128];;

let SIMD_SIMPLIFY_ASSUM_TAC =
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th);;

(* Per-step SIMD simplifier core: fold REV64 trees, cancel double half-swaps,
   normalize nested subwords.  Run after each GHASH step so terms stay small. *)
let GCM_SIMD_SIMPLIFY_CORE_TAC =
  SIMD_SIMPLIFY_ASSUM_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION]) THEN
  RULE_ASSUM_TAC(fun th ->
    try CONV_RULE(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) th
    with _ -> th);;

(* The REV64 fold needs TWO passes to reach a fixpoint: pass 1 normalizes the
   nested word_subword tree, pass 2 lets the REV64 lane rules (REV64_LOWER_LANE/
   UPPER_LANE/128) match.  A single pass leaves the raw byte-tree (~2.5k chars)
   in read Q8; two passes fold it to ~320 chars.  Applying the core twice is
   enough empirically (the result is a fixpoint). *)
let GCM_SIMD_SIMPLIFY_TAC =
  GCM_SIMD_SIMPLIFY_CORE_TAC THEN GCM_SIMD_SIMPLIFY_CORE_TAC;;

(* Discard large counter-increment register hypotheses *)
let DISCARD_COUNTER_REGS_TAC =
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let s = string_of_term (concl th) in
    String.length s > 500 &&
    (let has sub = let slen = String.length s and sublen = String.length sub in
      let rec check j = if j > slen - sublen then false
        else if String.sub s j sublen = sub then true else check (j+1) in check 0 in
     has "read Q1 " || has "read Q2 " || has "read Q3 " || has "read Q4 " ||
     has "read Q5 " || has "read Q6 " || has "read Q7 " || has "read Q30 " ||
     has "read Q16 " || has "read Q17 " || has "read Q18 " || has "read Q19 "));;

(* Resolve conditional branches in PC hypotheses *)
let RESOLVE_BRANCH_TAC =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && can (find_term is_cond) (rhs c) &&
       can (find_term (fun t -> name_of t = "PC")) (lhs c) then
      CONV_RULE(RAND_CONV(
        REWRITE_CONV[WORD_RULE `word_sub (word_sub (word_add (x:int64) (word a)) x) (word b) = word_sub (word a) (word b)`;
                     WORD_RULE `word_sub (word_add (x:int64) (word a)) x = word a`] THENC
        DEPTH_CONV WORD_NUM_RED_CONV THENC DEPTH_CONV NUM_RED_CONV THENC
        REWRITE_CONV[BIT_WORD; DIMINDEX_64] THENC NUM_REDUCE_CONV THENC
        REWRITE_CONV[bitval] THENC INT_REDUCE_CONV THENC
        REWRITE_CONV[TAUT `~T <=> F`; TAUT `~F <=> T`;
                     TAUT `F /\ p <=> F`; TAUT `T /\ p <=> p`;
                     TAUT `(F <=> F) <=> T`; TAUT `(T <=> T) <=> T`;
                     TAUT `(T <=> F) <=> F`; TAUT `(F <=> T) <=> F`] THENC
        REWRITE_CONV[COND_CLAUSES])) th
    else th);;

(* Step with branch resolution before each step *)
let ARM_STEPS_RESOLVE_TAC exec range =
  MAP_EVERY (fun n -> RESOLVE_BRANCH_TAC THEN ARM_STEPS_TAC exec [n]) (range);;

(* Step with branch resolution + per-step SIMD REV64 folding (Mila's pattern).
   Folds the byte-tree the instant each REV64/EXT step produces it, so the
   final closure never sees a 145k-char term. *)
let ARM_STEPS_RESOLVE_SIMD_TAC exec range =
  MAP_EVERY (fun n ->
    RESOLVE_BRANCH_TAC THEN ARM_STEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC)
    (range);;

(* VSTEPS variant: keeps register hypotheses alive (needed to capture the
   ciphertext/xi store read-backs) AND folds the REV64 byte-tree per step.
   Used for the store windows where ARM_STEPS_TAC would discard the register
   value the store read-back references. *)
let ARM_VSTEPS_RESOLVE_SIMD_TAC exec range =
  MAP_EVERY (fun n ->
    RESOLVE_BRANCH_TAC THEN ARM_VSTEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC)
    (range);;

(* Straight-line VSTEPS + per-step fold (no branch resolution).  Used for the
   GHASH multiply/reduce tail (steps 333-351), which has no branches.  Keeps the
   GHASH accumulators (Q17/Q18/Q19) and the xi_p store read-back alive while
   folding REV64 byte-trees so the terms stay bounded (~1-2k chars). *)
let ARM_VSTEPS_FOLD_TAC exec range =
  MAP_EVERY (fun n -> ARM_VSTEPS_TAC exec [n] THEN GCM_SIMD_SIMPLIFY_TAC) (range);;

(* Tactic to abbreviate all word_pmul subterms in the goal *)
let ABBREV_ALL_PMUL_TAC =
  let is_pmul t =
    try let (f,_) = dest_comb t in
        let (g,_) = dest_comb f in
        fst(dest_const g) = "word_pmul"
    with _ -> false in
  fun (asl,w) ->
    let pmuls = find_terms is_pmul w in
    let unique_pmuls = setify pmuls in
    let all_frees = frees w @
      List.concat (map (fun (_,th) -> frees(concl th)) asl) in
    let n = ref 0 in
    let tacs = List.map (fun t ->
      incr n;
      let v = variant all_frees (mk_var("pmul_"^string_of_int !n, type_of t)) in
      ABBREV_TAC (mk_eq(v, t))
    ) unique_pmuls in
    (EVERY tacs) (asl,w);;

(* Discard stale flag hypotheses but KEEP read PC (ENSURES_FINAL_STATE_TAC needs the
   final PC value to discharge the PC postcondition). *)
let DISCARD_COUNTER_ONLY_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let s = string_of_term(concl th) in
    try String.sub s 0 7 = "read NF" ||
        String.sub s 0 7 = "read ZF" ||
        String.sub s 0 7 = "read CF" ||
        String.sub s 0 7 = "read VF"
    with _ -> false)));;

(* ------------------------------------------------------------------------- *)
(* GHASH s348 bridge close.  The assembly computes, in Q19 at s348, the       *)
(* Karatsuba+Prop3 GHASH over the block word_xor (brev xi)(brev ct) with KEY  *)
(* byteswap128 h (the htable H is stored twisted; the real GHASH key is        *)
(* byteswap128(read htbl_p)).  GMULT_FULL_CORRECT_BA with b := byteswap128 h   *)
(* makes the lane operands match exactly; we then abbreviate the Karatsuba     *)
(* pmul limbs to opaque atoms, canonicalize their argument order with          *)
(* WORD_PMUL_SYM (via a congruence), and bit-blast the residual structural     *)
(* XOR/join/subword skeleton.  All BITBLAST/WORD_BLAST, no cheat.              *)
(* ------------------------------------------------------------------------- *)

let PMUL_CONG_128 = prove(
  `!a b c d:64 word. a = c /\ b = d ==> (word_pmul a b:int128) = word_pmul c d`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SUBWORD_XOR_JOIN_DIST = prove(
  `(!x y:int128. word_subword (word_xor x y) (0,64) : 64 word =
      word_xor (word_subword x (0,64)) (word_subword y (0,64))) /\
   (!x y:int128. word_subword (word_xor x y) (64,64) : 64 word =
      word_xor (word_subword x (64,64)) (word_subword y (64,64))) /\
   (!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
   (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`,
  REPEAT CONJ_TAC THEN TRY(REPEAT GEN_TAC) THEN BITBLAST_TAC);;

let SUBWORD0_LEMMAS = prove(
  `(word_subword (word 0:int128) (0,64):64 word = word 0) /\
   (word_subword (word 0:int128) (64,64):64 word = word 0)`,
  CONJ_TAC THEN BITBLAST_TAC);;

(* Abbreviate every currently-innermost fully-applied word_pmul to a fresh qqN:int128. *)
let ABBREV_INNER_PMULS_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,args)=strip_comb t in
        fst(dest_const h)="word_pmul" && length args=2 with _ -> false in
  let pmuls = setify(find_terms is_pmul_app w) in
  let contains_pmul_strict t = exists (fun p -> p <> t &&
     (let rec occ u = u=p ||
        (match u with Comb(a,b)->occ a||occ b|Abs(_,b)->occ b|_->false) in occ t)) pmuls in
  let inner = filter (fun t -> not(contains_pmul_strict t)) pmuls in
  let allvars = itlist (fun (_,th) acc ->
        union (map (fun v -> fst(dest_var v)) (frees(concl th))) acc)
        asl (map (fun v -> fst(dest_var v)) (frees w)) in
  let used = ref allvars in
  let fresh () = let rec go i = let n = "qq"^string_of_int i in
                   if mem n !used then go (i+1) else (used := n :: !used; n) in go 0 in
  EVERY (map (fun t -> ABBREV_TAC (mk_eq(mk_var(fresh(), `:int128`), t))) inner) (asl,w);;

(* For each pair of pmul-atom definitions, try to prove the atoms equal (same product up to
   argument order via WORD_PMUL_SYM, operands equal by WORD_BLAST) and rewrite to merge them. *)
let MERGE_PMUL_ATOMS_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,a)=strip_comb t in
        fst(dest_const h)="word_pmul" && length a=2 with _ -> false in
  let defs = filter (fun (_,th) ->
        let c = concl th in is_eq c && is_var(rhs c) && is_pmul_app(lhs c)) asl in
  let rec allpairs2 = function [] -> []
    | x::xs -> (map (fun y -> (x,y)) xs) @ allpairs2 xs in
  let cand = filter (fun ((_,t1),(_,t2)) -> rhs(concl t1) <> rhs(concl t2)) (allpairs2 defs) in
  let rec chain = function
    | [] -> ALL_TAC
    | ((_,t1),(_,t2))::rest ->
        let v1 = rhs(concl t1) and v2 = rhs(concl t2) in
        let prover =
          EXPAND_TAC (fst(dest_var v1)) THEN EXPAND_TAC (fst(dest_var v2)) THEN
          ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)
           ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                   MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)) in
        (SUBGOAL_THEN (mk_eq(v1,v2)) (fun th -> REWRITE_TAC[th]) THENL [prover; chain rest])
        ORELSE chain rest in
  chain cand (asl,w);;

(* Abbreviate the innermost Prop3 reduction pmul (word_pmul (word_subword _ (0,64)) W). *)
let ABBREV_WA_TAC : tactic = fun (asl,w) ->
  let is_wa t = try let (h,a)=strip_comb t in fst(dest_const h)="word_pmul" &&
                    string_of_term(List.nth a 1)="word 13979173243358019584" &&
                    (let (h2,_)=strip_comb(List.nth a 0) in fst(dest_const h2)="word_subword")
                with _ -> false in
  let was = setify(find_terms is_wa w) in
  let inner = filter (fun t -> not(can (find_term (fun s -> s<>t && is_wa s)) t)) was in
  (match inner with
   | t::_ -> ABBREV_TAC (mk_eq(`wa_atom:int128`, t))
   | [] -> ALL_TAC) (asl,w);;

(* Final: if exactly two pmuls remain (the two wv reductions), prove them equal and blast. *)
let FINISH_WV_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,a)=strip_comb t in
        fst(dest_const h)="word_pmul" && length a=2 with _ -> false in
  let pmuls = setify(find_terms is_pmul_app w) in
  match pmuls with
  | [p0;p1] ->
     (SUBGOAL_THEN (mk_eq(p0,p1)) (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
      CONV_TAC WORD_BLAST) (asl,w)
  | _ -> CONV_TAC WORD_BLAST (asl,w);;

(* Abbreviate the two 64-bit halves of every Karatsuba pmul output as fresh xNl/xNh vars
   (label l=low subword(0,64), h=hi subword(64,64); N from the operand kind: l for
   subword-at-0 product, h for subword-at-64, m for the (a xor b) mid product).  Ported
   verbatim from Mila's one_block_aes256_gcm_preloop_tail_direct.ml. *)
let ABBREV_PMUL_HALVES_TAC : tactic = fun (asl,w) ->
  let classify_pmul eqn =
    try
      let lhs, rhs = dest_eq eqn in
      let pmul, _ = dest_comb lhs in
      let pmul_fn, x_arg = dest_comb pmul in
      if name_of pmul_fn <> "word_pmul" then None
      else begin
        match x_arg with
        | Comb(Comb(Const("word_xor",_), _), _) -> Some ("m", rhs)
        | Comb(Comb(Const("word_subword",_), _), pair) ->
          (try
             let k_term, _ = dest_pair pair in
             let k = dest_small_numeral k_term in
             if k = 0 then Some ("l", rhs)
             else if k = 64 then Some ("h", rhs)
             else None
           with _ -> None)
        | _ -> None
      end
    with _ -> None in
  let pmul_vs = List.filter_map (fun (_, th) -> classify_pmul (concl th)) asl in
  let all_frees =
    frees w @ List.concat (map (fun (_,th) -> frees(concl th)) asl) in
  let subword_const =
    inst [`:128`, `:M`; `:64`, `:N`] `word_subword:(M)word->num#num->(N)word` in
  let rec process all tasks (asl,w) =
    match tasks with
    | [] -> ALL_TAC (asl,w)
    | (label, v_term) :: rest ->
      let vname = "x" ^ label in
      let vl_var = variant all (mk_var(vname ^ "l", `:(64)word`)) in
      let vh_var = variant all (mk_var(vname ^ "h", `:(64)word`)) in
      let el = mk_eq(vl_var, mk_comb(mk_comb(subword_const, v_term), `0,64`)) in
      let eh = mk_eq(vh_var, mk_comb(mk_comb(subword_const, v_term), `64,64`)) in
      (ABBREV_TAC el THEN ABBREV_TAC eh THEN process (vl_var::vh_var::all) rest) (asl,w) in
  process all_frees pmul_vs (asl,w);;

(* Half projection helpers for the Mila close. *)
let JOINMID = prove(
  `!q:int128. word_subword (word_join q q :(256)word) (64,128):int128 =
     word_join (word_subword q (0,64):64 word) (word_subword q (64,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let QQ0SPLIT = prove(
  `!q:int128. q = word_join (word_subword q (64,64):64 word) (word_subword q (0,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* MILA-ROUTE close.  Closes the GHASH bridge by Mila's reduction-as-rewrite instead of one
   monolithic structural WORD_BLAST over `word_pmul _ W`.  Context at entry (after GMULT GSYM +
   byteswap128/subword normalize + ABBREV_INNER_PMULS_TAC + MERGE_PMUL_ATOMS_TAC + WORD_XOR_0
   cleanup): the goal is a pure word identity carrying the three Karatsuba product atoms
   qq0,qq1,qq2 (qq1 the H-hi×block-lo product, whose lo limb xhl is the Prop3 reduction limb),
   the GMULT halfswap mids `word_subword (word_join qq1 qq1) (64,128)`, and the W-multiplies.
   ABBREV_PMUL_HALVES_TAC names the product halves DETERMINISTICALLY:
     qq0 -> xll/xlh, qq1 -> xhl/xhh, qq2 -> xml'''/xmh'''  (xhl is the reduction limb).
   Steps:
     1. PMUL_W_64_128: rewrite each `word_pmul V W` to shl63 V ⊕ shl62 V ⊕ shl57 V — this is the
        key move that removes the ~107s carryless-multiply-by-constant blast.
     2. JOINMID: collapse the halfswap mid `word_subword (word_join q q) (64,128)` to
        `word_join (sub q 0) (sub q 64)`.
     3. Split the bare product atoms qq0/qq1/qq2 into joins of their (named) halves (QQ0SPLIT),
        then WORD_SUBWORD_XOR + ASM_REWRITE substitute every half hypothesis — eliminating all
        128-bit atoms; the goal is now a pure 64-bit-word identity in xhl,xhh,xll,xlh,xml''',xmh'''.
     4. First reduction round: abbreviate r1 = shift-triple of the reduction limb xhl, fold its
        lo/hi subwords (RL/RH per-shift WORD_BLAST lemmas).
     5. Abbreviate the second-round shift argument u; fold both xor-orderings of it to the atom u.
     6. Distribute the residual bare r1 into its subwords (WORD_SUBWORD_XOR), fold joins, refold
        the recombine lo-part to u, and finish with one WORD_BLAST over the atoms u / subword r1.
   Measured on our s348 bridge term: ~88s total here (qq-split ASM_MESON ~32s + final blast ~30s)
   vs ~107s+27s for the committed FINISH_WV route. *)
let FINISH_WV_REDUCE_TAC : tactic =
  REWRITE_TAC[PMUL_W_64_128] THEN
  ABBREV_PMUL_HALVES_TAC THEN
  REWRITE_TAC[JOINMID] THEN
  SUBGOAL_THEN
    `qq0:int128 = word_join (xlh:64 word) (xll:64 word) /\
     qq1:int128 = word_join (xhh:64 word) (xhl:64 word) /\
     qq2:int128 = word_join (xmh''':64 word) (xml''':64 word)`
    (fun th -> REWRITE_TAC[CONJUNCT1 th] THEN
               REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)] THEN
               REWRITE_TAC[CONJUNCT2(CONJUNCT2 th)]) THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC[QQ0SPLIT]; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[JOIN_SUBWORD_RULES] THEN
  ABBREV_TAC
   `r1:(128)word = word_xor (word_xor (word_shl (word_zx (xhl:(64)word):(128)word) 63)
                                      (word_shl (word_zx xhl:(128)word) 62))
                            (word_shl (word_zx xhl:(128)word) 57)` THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (0,64):(64)word)
                       (word_subword (word_shl (word_zx xhl:(128)word) 62) (0,64):(64)word))
             (word_subword (word_shl (word_zx xhl:(128)word) 57) (0,64):(64)word) =
    word_subword (r1:(128)word) (0,64):(64)word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (64,64):(64)word)
                       (word_subword (word_shl (word_zx xhl:(128)word) 62) (64,64):(64)word))
             (word_subword (word_shl (word_zx xhl:(128)word) 57) (64,64):(64)word) =
    word_subword (r1:(128)word) (64,64):(64)word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC `u:(64)word = word_xor (word_xor (xhh:64 word) (word_xor (word_xor (xml''':64 word) (xhl:64 word)) (xll:64 word))) (word_subword (r1:(128)word) (0,64))` THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor (word_xor (xml''':64 word) (xhl:64 word)) (xll:64 word)) (word_subword (r1:128 word) (0,64))) (xhh:64 word) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_SUBWORD_RULES] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor (word_xor (xml''':64 word) (xhl:64 word)) (xll:64 word)) (word_subword (r1:128 word) (0,64))) (xhh:64 word) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  CONV_TAC WORD_BLAST;;

(* Precondition note: the Prop3 GHASH reduction constant 0xC200000000000000 is written to
   [SP+64] by the function prologue (MOVZ X5,0xC200<<48; STP X5 XZR,[SP+64] at 0x24/0x28)
   BEFORE the pc+0x2c entry, so it is carried as the precondition
   `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`.
   The tail reloads it (LDR D16,[SP+64], ~step 341) for the polyval reduction; it is the w
   constant in GMULT_FULL_CORRECT_BA.
   NOTE: HOL term quotations do NOT accept (* *) comments — keep all such notes outside the
   backticks (a stray in-term comment makes the whole `prove` fail to parse). *)
let AESV8_GCM_8X_ENC_256_1BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    plaintext xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk.
    nonoverlapping (word pc, 4600) (out_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (xi_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (ivec_p, 16) (word_add stackpointer (word 64):int64, 8) /\
    nonoverlapping (xi_p, 16) (in_p, 16) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (word_add stackpointer (word 64):int64, 8) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 240) /\
    nonoverlapping (out_p, 16) (htbl_p, 192) /\
    nonoverlapping (out_p, 16) (word_add stackpointer (word 64):int64, 8) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0x2c) /\ read SP s = stackpointer /\
          read X0 s = in_p /\ read X1 s = word 128 /\
          read X9 s = word 16 /\ read X2 s = out_p /\
          read X3 s = xi_p /\ read X16 s = ivec_p /\
          read X11 s = key_p /\ read X6 s = htbl_p /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = plaintext /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes64 (word_add stackpointer (word 64))) s =
            word 13979173243358019584)
     (\s. read PC s = word (pc + 0x11d8) /\
          read (memory :> bytes128 out_p) s =
          word_xor plaintext (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse
                (word_xor plaintext
                  (aes256_encrypt ctr0
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 16); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 8)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  (* === AES-256 encryption: steps 1-265 === *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (1--11) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (12--13) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (14--15) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (16--17) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (18--19) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (20--21) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (22--23) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (24--25) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (26--84) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (85--173) THEN DISCARD_COUNTER_REGS_TAC THEN
  (* Steps 174-176 load the GHASH tag: LDR Q19,[xi_p]; EXT Q19; REV64 Q19.
     The REV64 expands Q19 into a ~49k-char byte-tree; without folding it,
     DISCARD_COUNTER_REGS_TAC (>500 chars) would DROP Q19 and the GHASH tag
     (byteswapped xi) would be lost.  Fold it immediately so Q19 collapses to
     the clean ~120-char word_join (word_reversefields 8 (word_subword xi 0 64))
     (word_reversefields 8 (word_subword xi 64 64)) form and survives the
     remaining AES rounds (which never touch Q19) into the GHASH tail. *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (174--176) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (177--184) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (185--254) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [255] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (256--265) THEN DISCARD_COUNTER_REGS_TAC THEN
  (* === Assert Q9 = ciphertext === *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(word_xor plaintext (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL
  [ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC];
   DISCH_TAC] THEN
  (* === Steps 266-324 === *)
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_ENC_256_EXEC (266--310) THEN
  DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_ENC_256_EXEC (311--324) THEN
  DISCARD_COUNTER_REGS_TAC THEN
  (* === Mask (steps 325-326): the all-ones mask makes the AND_VEC v9,v9,v0 the
     identity, but the simulator leaves Q9 as word_and(allones, ciphertext).
     Step with plain ARM_STEPS (so a single, latest read Q9 survives) and fold
     the REV64 byte-tree per step, then re-assert Q9 = clean ciphertext via
     WORD_BLAST (proves the all-ones mask is the identity without expanding the
     aese tree).  This keeps the subsequent rev64 v8,v9 (step 327) folding to a
     small word_reversefields term instead of the ~582k-char byte-tree. *)
  ARM_STEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_ENC_256_EXEC (325--326) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(word_xor plaintext (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  (* === VSTEPS 327-332: ciphertext store window.  VSTEPS keeps the Q8/Q9
     register reads alive (needed for the out_p store read-back), and the
     per-step REV64 fold keeps read Q8 small (~350 chars, was ~582k). === *)
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_ENC_256_EXEC (327--332) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s332:armstate) =
     word_xor plaintext (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* === GHASH tail (steps 333-351): INS, PMULL Karatsuba multiply, Prop3
     reduction, EXT/REV64, and the xi_p store (STR Q19,[X3] at step 351, 0x11d4).
     The tail is straight-line, so use VSTEPS+fold (no branch resolution).  VSTEPS
     keeps Q19 (and the xi_p store read-back) alive; the per-step fold keeps the
     GHASH accumulator terms bounded.  The GHASH tag (byteswapped xi) reached the
     tail in Q19 via the step-176 fold above, so the data block GHASH'd here is
     word_xor (byteswap xi) (byteswap ciphertext), exactly the spec's input. === *)
  DISCARD_COUNTER_REGS_TAC THEN
  (* Steps 333-348: GHASH Karatsuba multiply + Prop3 reduction; the reduced result
     lands in Q19 at s348 (BEFORE the final EXT(349)+REV64(350) byte-reorder).  Fold
     per step so the accumulator terms stay bounded. *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (333--348) THEN
  (* Bridge the reduced GHASH result to the spec at s348.  The block GHASH'd is the spec
     block word_xor (brev xi)(brev ct); the assembly's GHASH KEY is byteswap128 h (the htable
     H is stored twisted).  Instantiate GMULT_FULL_CORRECT_BA with b := byteswap128 h so the
     lane operands match exactly, then abbreviate the Karatsuba pmul limbs, canonicalize their
     argument order (WORD_PMUL_SYM via PMUL_CONG_128) and bit-blast the structural skeleton.
     The Prop3 reduction constant 0xC2.. comes from the [SP+64] precondition.  GMULT GSYM is a
     SEPARATE step (folding it into the THEN chain can intermittently no-op).
     First DISCARD_OLDSTATE prunes the ~1357 intermediate-state hyps down to ~77 (the Q19@s348
     RHS is self-contained in xi/ct/h, so this is safe) — otherwise the bridge crawls. *)
  DISCARD_OLDSTATE_TAC "s348" THEN
  SUBGOAL_THEN
    `read Q19 (s348:armstate) =
     polyval_dot (word_xor (word_bytereverse xi)
       (word_bytereverse (word_xor plaintext (aes256_encrypt (ctr0:int128)
         [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))))
       (byteswap128 h)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s348`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [(* rewrite the LHS read Q19 s348 to its simulator byte-form via its hypothesis *)
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s348` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   GEN_REWRITE_TAC RAND_CONV
     [GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
        (ISPECL [`word_xor (word_bytereverse xi)
          (word_bytereverse (word_xor plaintext (aes256_encrypt (ctr0:int128)
            [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))) : int128`;
          `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))] THEN
   REWRITE_TAC[byteswap128] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_PMUL_ATOMS_TAC THEN
   REWRITE_TAC[WORD_XOR_0; SUBWORD0_LEMMAS] THEN REWRITE_TAC[WORD_XOR_0] THEN
   FINISH_WV_REDUCE_TAC;
   ALL_TAC] THEN
  (* Steps 349-351: EXT (halfswap) + REV64 (per-lane byte-reverse) reorder Q19 to
     word_bytereverse of the reduced result, then STR to xi_p.  With Q19@s348 now the
     clean polyval_dot term, the fold collapses the store value to
     word_bytereverse (polyval_dot ...) (REV64_LANES_EQ). *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (349--350) THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [351] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  (* === Close proof === *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (* GHASH (xi_p) goal: stored = word_bytereverse(polyval_dot ...); bridge polyval_dot
     -> ghash_polyval_acc and collapse the REV64 lane form. *)
  TRY(REWRITE_TAC[REV64_LANES_EQ; GHASH_1BLOCK_CORRECT] THEN
      REWRITE_TAC[GSYM GHASH_1BLOCK_CORRECT] THEN CONV_TAC WORD_BLAST) THEN
  TRY(CONV_TAC WORD_BLAST) THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]));;
