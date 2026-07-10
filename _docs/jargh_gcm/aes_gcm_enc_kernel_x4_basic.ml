(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-128-GCM encryption kernel.                                            *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "common/fips197.ml";;

needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes_gcm/aes_gcm_enc_kernel_x4_basic.o";; *)

let aes_gcm_enc_kernel_x4_basic_mc =
  define_assert_from_elf "aes_gcm_enc_kernel_x4_basic_mc"
                         "arm/aes_gcm/aes_gcm_enc_kernel_x4_basic.o"
[
  0xd10283ff;       (* sub      sp, sp, #0xa0 *)
  0xa90053f3;       (* stp      x19, x20, [sp] *)
  0xa9015bf5;       (* stp      x21, x22, [sp, #0x10] *)
  0xa90263f7;       (* stp      x23, x24, [sp, #0x20] *)
  0xa9036bf9;       (* stp      x25, x26, [sp, #0x30] *)
  0xa90473fb;       (* stp      x27, x28, [sp, #0x40] *)
  0xa9057bfd;       (* stp      x29, x30, [sp, #0x50] *)
  0x6d0627e8;       (* stp      d8, d9, [sp, #0x60] *)
  0x6d072fea;       (* stp      d10, d11, [sp, #0x70] *)
  0x6d0837ec;       (* stp      d12, d13, [sp, #0x80] *)
  0x6d093fee;       (* stp      d14, d15, [sp, #0x90] *)
  0xd343fc2f;       (* lsr      x15, x1, #3 *)
  0x3dc000b2;       (* ldr      q18, [x5] *)
  0x3dc004b3;       (* ldr      q19, [x5, #0x10] *)
  0x3dc008b4;       (* ldr      q20, [x5, #0x20] *)
  0x3dc00cb5;       (* ldr      q21, [x5, #0x30] *)
  0x3dc010b6;       (* ldr      q22, [x5, #0x40] *)
  0x3dc014b7;       (* ldr      q23, [x5, #0x50] *)
  0x3dc018b8;       (* ldr      q24, [x5, #0x60] *)
  0x3dc01cb9;       (* ldr      q25, [x5, #0x70] *)
  0x3dc020ba;       (* ldr      q26, [x5, #0x80] *)
  0x3dc024bb;       (* ldr      q27, [x5, #0x90] *)
  0x3dc028bc;       (* ldr      q28, [x5, #0xa0] *)
  0x3dc0006b;       (* ldr      q11, [x3] *)
  0x4e20096b;       (* rev64.16b        v11, v11 *)
  0x3dc0009f;       (* ldr      q31, [x4] *)
  0xd2c00039;       (* mov      x25, #0x100000000 *)
  0x4f00e41e;       (* movi.16b v30, #0x0 *)
  0x9eaf033e;       (* fmov.d   v30[1], x25 *)
  0x6e200bff;       (* rev32.16b        v31, v31 *)
  0xd344fde7;       (* lsr      x7, x15, #4 *)
  0xd342fce1;       (* lsr      x1, x7, #2 *)
  0x924004e9;       (* and      x9, x7, #0x3 *)
  0x0f06e447;       (* movi     v7.8b, #0xc2 *)
  0x5f7854e7;       (* shl      d7, d7, #56 *)
  0xb4001341;       (* cbz      x1, 0x2f4 *)
  0x3cc4041d;       (* ldr      q29, [x0], #0x40 *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c840440;       (* str      q0, [x2], #0x40 *)
  0x3dc00ccc;       (* ldr      q12, [x6, #0x30] *)
  0x3dc014cd;       (* ldr      q13, [x6, #0x50] *)
  0x3dc010ce;       (* ldr      q14, [x6, #0x40] *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x6e2b1c00;       (* eor.16b  v0, v0, v11 *)
  0x0eede008;       (* pmull.1q v8, v0, v13 *)
  0x4eede009;       (* pmull2.1q        v9, v0, v13 *)
  0x6e00400b;       (* ext.16b  v11, v0, v0, #0x8 *)
  0x6e201d6b;       (* eor.16b  v11, v11, v0 *)
  0x4eeee16a;       (* pmull2.1q        v10, v11, v14 *)
  0x3cdd001d;       (* ldur     q29, [x0, #-0x30] *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c9d0040;       (* stur     q0, [x2, #-0x30] *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x0eece00b;       (* pmull.1q v11, v0, v12 *)
  0x6e2b1d08;       (* eor.16b  v8, v8, v11 *)
  0x4eece00b;       (* pmull2.1q        v11, v0, v12 *)
  0x6e2b1d29;       (* eor.16b  v9, v9, v11 *)
  0x5e18040b;       (* mov      d11, v0.d[1] *)
  0x2e201d6b;       (* eor.8b   v11, v11, v0 *)
  0x0eeee16b;       (* pmull.1q v11, v11, v14 *)
  0x6e2b1d4a;       (* eor.16b  v10, v10, v11 *)
  0x3cde001d;       (* ldur     q29, [x0, #-0x20] *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c9e0040;       (* stur     q0, [x2, #-0x20] *)
  0x3dc000cc;       (* ldr      q12, [x6] *)
  0x3dc008cd;       (* ldr      q13, [x6, #0x20] *)
  0x3dc004ce;       (* ldr      q14, [x6, #0x10] *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x0eede00b;       (* pmull.1q v11, v0, v13 *)
  0x6e2b1d08;       (* eor.16b  v8, v8, v11 *)
  0x4eede00b;       (* pmull2.1q        v11, v0, v13 *)
  0x6e2b1d29;       (* eor.16b  v9, v9, v11 *)
  0x6e00400b;       (* ext.16b  v11, v0, v0, #0x8 *)
  0x6e201d6b;       (* eor.16b  v11, v11, v0 *)
  0x4eeee16b;       (* pmull2.1q        v11, v11, v14 *)
  0x6e2b1d4a;       (* eor.16b  v10, v10, v11 *)
  0x3cdf001d;       (* ldur     q29, [x0, #-0x10] *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c9f0040;       (* stur     q0, [x2, #-0x10] *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x0eece00b;       (* pmull.1q v11, v0, v12 *)
  0x6e2b1d08;       (* eor.16b  v8, v8, v11 *)
  0x4eece00b;       (* pmull2.1q        v11, v0, v12 *)
  0x6e2b1d29;       (* eor.16b  v9, v9, v11 *)
  0x5e18040b;       (* mov      d11, v0.d[1] *)
  0x2e201d6b;       (* eor.8b   v11, v11, v0 *)
  0x0eeee16b;       (* pmull.1q v11, v11, v14 *)
  0x6e2b1d4a;       (* eor.16b  v10, v10, v11 *)
  0x6e291d00;       (* eor.16b  v0, v8, v9 *)
  0x0ee7e121;       (* pmull.1q v1, v9, v7 *)
  0x6e094129;       (* ext.16b  v9, v9, v9, #0x8 *)
  0x6e201d4a;       (* eor.16b  v10, v10, v0 *)
  0x6e211d21;       (* eor.16b  v1, v9, v1 *)
  0x6e211d4a;       (* eor.16b  v10, v10, v1 *)
  0x0ee7e149;       (* pmull.1q v9, v10, v7 *)
  0x6e291d08;       (* eor.16b  v8, v8, v9 *)
  0x6e0a414a;       (* ext.16b  v10, v10, v10, #0x8 *)
  0x6e2a1d0b;       (* eor.16b  v11, v8, v10 *)
  0x6e0b416b;       (* ext.16b  v11, v11, v11, #0x8 *)
  0xd1000421;       (* sub      x1, x1, #0x1 *)
  0xb5ffed01;       (* cbnz     x1, 0x94 *)
  0x3dc000cc;       (* ldr      q12, [x6] *)
  0x3dc008cd;       (* ldr      q13, [x6, #0x20] *)
  0x3dc004ce;       (* ldr      q14, [x6, #0x10] *)
  0xb40005c9;       (* cbz      x9, 0x3bc *)
  0x3cc1041d;       (* ldr      q29, [x0], #0x10 *)
  0x6e200be0;       (* rev32.16b        v0, v31 *)
  0x4ebe87ff;       (* add.4s   v31, v31, v30 *)
  0x4e284a40;       (* aese.16b v0, v18 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a60;       (* aese.16b v0, v19 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284a80;       (* aese.16b v0, v20 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284aa0;       (* aese.16b v0, v21 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ac0;       (* aese.16b v0, v22 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284ae0;       (* aese.16b v0, v23 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b00;       (* aese.16b v0, v24 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b20;       (* aese.16b v0, v25 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b40;       (* aese.16b v0, v26 *)
  0x4e286800;       (* aesmc.16b        v0, v0 *)
  0x4e284b60;       (* aese.16b v0, v27 *)
  0x6e3c1fbd;       (* eor.16b  v29, v29, v28 *)
  0x6e201fa0;       (* eor.16b  v0, v29, v0 *)
  0x3c810440;       (* str      q0, [x2], #0x10 *)
  0x4e200800;       (* rev64.16b        v0, v0 *)
  0x6e2b1c00;       (* eor.16b  v0, v0, v11 *)
  0x0eece008;       (* pmull.1q v8, v0, v12 *)
  0x4eece009;       (* pmull2.1q        v9, v0, v12 *)
  0x5e18040b;       (* mov      d11, v0.d[1] *)
  0x2e201d6b;       (* eor.8b   v11, v11, v0 *)
  0x0eeee16a;       (* pmull.1q v10, v11, v14 *)
  0x6e291d00;       (* eor.16b  v0, v8, v9 *)
  0x0ee7e121;       (* pmull.1q v1, v9, v7 *)
  0x6e094129;       (* ext.16b  v9, v9, v9, #0x8 *)
  0x6e201d4a;       (* eor.16b  v10, v10, v0 *)
  0x6e211d21;       (* eor.16b  v1, v9, v1 *)
  0x6e211d4a;       (* eor.16b  v10, v10, v1 *)
  0x0ee7e149;       (* pmull.1q v9, v10, v7 *)
  0x6e291d08;       (* eor.16b  v8, v8, v9 *)
  0x6e0a414a;       (* ext.16b  v10, v10, v10, #0x8 *)
  0x6e2a1d0b;       (* eor.16b  v11, v8, v10 *)
  0x6e0b416b;       (* ext.16b  v11, v11, v11, #0x8 *)
  0xd1000529;       (* sub      x9, x9, #0x1 *)
  0xb5fffa89;       (* cbnz     x9, 0x308 *)
  0xaa0f03e0;       (* mov      x0, x15 *)
  0x4e20096b;       (* rev64.16b        v11, v11 *)
  0x3d80006b;       (* str      q11, [x3] *)
  0x6e200bff;       (* rev32.16b        v31, v31 *)
  0x3d80009f;       (* str      q31, [x4] *)
  0x6d4627e8;       (* ldp      d8, d9, [sp, #0x60] *)
  0x6d472fea;       (* ldp      d10, d11, [sp, #0x70] *)
  0x6d4837ec;       (* ldp      d12, d13, [sp, #0x80] *)
  0x6d493fee;       (* ldp      d14, d15, [sp, #0x90] *)
  0xa94053f3;       (* ldp      x19, x20, [sp] *)
  0xa9415bf5;       (* ldp      x21, x22, [sp, #0x10] *)
  0xa94263f7;       (* ldp      x23, x24, [sp, #0x20] *)
  0xa9436bf9;       (* ldp      x25, x26, [sp, #0x30] *)
  0xa94473fb;       (* ldp      x27, x28, [sp, #0x40] *)
  0xa9457bfd;       (* ldp      x29, x30, [sp, #0x50] *)
  0x910283ff;       (* add      sp, sp, #0xa0 *)
  0xd65f03c0        (* ret *)
];;

let AES_GCM_ENC_KERNEL_X4_BASIC_EXEC = ARM_MK_EXEC_RULE aes_gcm_enc_kernel_x4_basic_mc;;

(* ------------------------------------------------------------------------- *)
(* Some specification concepts.                                              *)
(* ------------------------------------------------------------------------- *)

let ctr_block = new_definition
 `ctr_block nonce ctr :int128 = word_join (nonce:96 word) (word ctr:int32)`;;

(**** This is the form that we actually XOR little-endian bytes with
 **** in the algorithm, so we switch back out of NIST big-endian
 ****)

let aes_ctr_block = new_definition
 `aes_ctr_block nonce rk i =
    word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 2)) rk)`;;

(* The i-th ciphertext block: keystream XOR plaintext - little-endian *)

let cipher_block = new_definition
 `cipher_block nonce rk inblock i =
    word_xor (aes_ctr_block nonce rk i) (inblock i)`;;

(* The NIST convention is big-endian, however *)

let nist_cipher_block = new_definition
 `nist_cipher_block nonce rk inblock i =
        word_reversefields 8 (cipher_block nonce rk inblock i)`;;

(* Restricted Htable predicate: only the entries the kernel actually reads.
   The x4-unrolled loop uses H^1..H^4 and their Karatsuba mid terms (the
   first 6 entries = offsets 0..80 of the full htable_mem layout).
   The tail loop only uses H^1..H^2 (offsets 0..32) but we assert all four
   here since the outer loop needs them and the precondition is shared. *)

let htable_mem_4 = new_definition
 `htable_mem_4 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s =
    byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s =
    byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s =
    byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s =
    byteswap128(h_power h 3)`;;

(* ------------------------------------------------------------------------- *)
(* Equivalences between the FIPS197 specs and the ARM hardare specs.         *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_REVERSEFIELDS = prove
 (`word_subword (word_reversefields 8 x) (0,8):byte = word_subword x (120,8) /\
   word_subword (word_reversefields 8 x) (8,8):byte = word_subword x (112,8) /\
   word_subword (word_reversefields 8 x) (16,8):byte = word_subword x (104,8) /\
   word_subword (word_reversefields 8 x) (24,8):byte = word_subword x (96,8) /\
   word_subword (word_reversefields 8 x) (32,8):byte = word_subword x (88,8) /\
   word_subword (word_reversefields 8 x) (40,8):byte = word_subword x (80,8) /\
   word_subword (word_reversefields 8 x) (48,8):byte = word_subword x (72,8) /\
   word_subword (word_reversefields 8 x) (56,8):byte = word_subword x (64,8) /\
   word_subword (word_reversefields 8 x) (64,8):byte = word_subword x (56,8) /\
   word_subword (word_reversefields 8 x) (72,8):byte = word_subword x (48,8) /\
   word_subword (word_reversefields 8 x) (80,8):byte = word_subword x (40,8) /\
   word_subword (word_reversefields 8 x) (88,8):byte = word_subword x (32,8) /\
   word_subword (word_reversefields 8 x) (96,8):byte = word_subword x (24,8) /\
   word_subword (word_reversefields 8 x) (104,8):byte = word_subword x (16,8) /\
   word_subword (word_reversefields 8 x) (112,8):byte = word_subword x (8,8) /\
   word_subword (word_reversefields 8 x:int128) (120,8):byte =
   word_subword x (0,8)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_SHIFT_ROWS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (aes_shift_rows x) =
              aes_shift_rows (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[aes_sub_bytes_select; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let WORD_XOR_REVERSEFIELDS = prove
 (`!x y:int128.
        word_xor (word_reversefields 8 x) (word_reversefields 8 y) =
        word_reversefields 8 (word_xor x y)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_REVERSEFIELDS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (word_reversefields 8 x) =
              word_reversefields 8 (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; word_join_list_16_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  CONV_TAC WORD_BLAST);;

let FIPS197_EQ_SHIFT_ROWS = prove
 (`!x:int128.
        fips197_shift_rows x =
        word_reversefields 8 (aes_shift_rows (word_reversefields 8 x))`,
  REWRITE_TAC[fips197_shift_rows; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

let FIPS197_EQ_MIX_COLUMNS = prove
 (`!x:int128.
        fips197_mix_columns x =
        word_reversefields 8 (aes_mix_columns  (word_reversefields 8 x))`,
  REWRITE_TAC[aes_mix_columns; fips197_mix_columns;
              word_join_list_16_8; aes_mix_word] THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN_COMBINE_LEMMA = prove
 (`(!(x:N word) pos1 pos2.
        pos1 + 8 = pos2
        ==> word_join (word_subword x (pos2,8):byte)
                      (word_subword x (pos1,8):byte):int16 =
            word_subword x (pos1,16)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 16 = pos2
        ==> word_join (word_subword x (pos2,16):int16)
                      (word_subword x (pos1,16):int16):int32 =
            word_subword x (pos1,32)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 32 = pos2
        ==> word_join (word_subword x (pos2,32):int32)
                      (word_subword x (pos1,32):int32):int64 =
            word_subword x (pos1,64)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 64 = pos2
        ==> word_join (word_subword x (pos2,64):int64)
                      (word_subword x (pos1,64):int64):int128 =
            word_subword x (pos1,128)) /\
   (!x:int128. word_subword x (0,128) = x)`,
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_BLAST] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_SUBWORD;
        DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_SUBWORD_REVERSEFIELDS_32 = prove
 (`word_subword (word_reversefields 32 x:int128) (0,32):int32 =
   word_subword x (96,32) /\
   word_subword (word_reversefields 32 x:int128) (32,32):int32 =
   word_subword x (64,32) /\
   word_subword (word_reversefields 32 x:int128) (64,32):int32 =
   word_subword x (32,32) /\
   word_subword (word_reversefields 32 x:int128) (96,32):int32 =
   word_subword x (0,32)`,
  CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_BYTESWAP128 = prove
 (`(!x. word_subword (byteswap128 x) (0,64):int64 = word_subword x (64,64)) /\
   (!x. word_subword (byteswap128 x) (64,64):int64 = word_subword x (0,64))`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_CTR_BLOCK_32 = prove
 (`word_subword (ctr_block nonce cnt) (0,32):int32 = word cnt /\
   word_subword (ctr_block nonce cnt) (32,32):int32 =
     word_subword nonce (0,32) /\
   word_subword (ctr_block nonce cnt) (64,32):int32 =
     word_subword nonce (32,32) /\
   word_subword (ctr_block nonce cnt) (96,32):int32 =
     word_subword nonce (64,32)`,
  REWRITE_TAC[ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let CTR_BLOCK_RECONSTRUCT_REV8 = prove
 (`word_join
    (word_join (word_reversefields 8 (word ctr):int32)
               (word_reversefields 8 (word_subword nonce (0,32):int32)):int64)
    (word_join (word_reversefields 8 (word_subword nonce (32,32):int32))
               (word_reversefields 8 (word_subword nonce (64,32):int32)):int64)
    = word_reversefields 8 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let CTR_BLOCK_RECONSTRUCT_REV32 = prove
 (`word_join
    (word_join (word ctr:int32)
               (word_subword nonce (0,32):int32):int64)
    (word_join (word_subword nonce (32,32):int32)
               (word_subword nonce (64,32):int32):int64) =
  word_reversefields 32 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let AES_CTR_BLOCK_RECONSTRUCT = prove
 (`word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 2)) rk) =
   aes_ctr_block nonce rk i /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 3)) rk) =
   aes_ctr_block nonce rk (i + 1) /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 4)) rk) =
   aes_ctr_block nonce rk (i + 2) /\
   word_reversefields 8 (aes128_cipher (ctr_block nonce (i + 5)) rk) =
   aes_ctr_block nonce rk (i + 3)`,
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CIPHER_BLOCK_NIST = prove
 (`cipher_block nonce rk inblock i =
        word_reversefields 8 (nist_cipher_block nonce rk inblock i)`,
  REWRITE_TAC[nist_cipher_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(*** Direct implementation of AES128 using the hardware primitives ***)

let AES128_CIPHER_RECONSTRUCT = prove
 (`word_xor
   (aese
    (aesmc
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
         rk3))
        rk4))
       rk5))
      rk6))
     rk7))
    rk8))
   rk9)
   rk10 =
   word_reversefields 8
    (aes128_cipher (word_reversefields 8 plaintext)
        (MAP (word_reversefields 8)
             [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10]))`,
  REWRITE_TAC[aes128_cipher; LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[aesmc; aese; fips197_final_round; fips197_round] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS] THEN
  REWRITE_TAC[FIPS197_EQ_SHIFT_ROWS; FIPS197_EQ_MIX_COLUMNS; fips197_sub_bytes;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GSYM WORD_XOR_REVERSEFIELDS; WORD_REVERSEFIELDS_REVERSEFIELDS;
              GSYM AES_SUB_BYTES_REVERSEFIELDS]);;

(*** This is the sequence in the code, folding an XOR in sooner ***)

let XOR_AES128_CIPHER_RECONSTRUCT = prove
 (`word_xor
    (aese
     (aesmc
     (aese
      (aesmc
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc
          (aese
           (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2))
          rk3))
         rk4))
        rk5))
       rk6))
      rk7))
     rk8))
    rk9)
   (word_xor rk10 inblock) =
   word_xor
    (word_reversefields 8
      (aes128_cipher (word_reversefields 8 plaintext)
         (MAP (word_reversefields 8)
              [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10])))
    inblock`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[AES128_CIPHER_RECONSTRUCT]);;

(* ------------------------------------------------------------------------- *)
(* The reduction pattern that is used in the code (p1, p2, p3 are the        *)
(* Karatsuba subcomponents of an implicit 256-bit result).                   *)
(* ------------------------------------------------------------------------- *)

let polyval_reduce_g2 = new_definition
 `polyval_reduce_g2 p1 p2 p3 =
        let (HI:int128->int64) = \x. word_subword x (64,64)
        and (LO:int128->int64) = \x. word_subword x (0,64) in
        let ks = word_xor (word_xor p1 p2) p3 in
        let w1 = word_pmul (LO p1) (word 13979173243358019584 : int64) in
        let w2 = word_pmul
                 (word_xor (word_xor (LO w1) (HI p1))
                           (LO(word_xor (word_xor p1 p2) p3)))
                 (word 13979173243358019584 : int64) in
        word_xor
           (word_join
              (LO (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              (HI (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              : int128)
           (word_xor w2 p2 : int128)`;;

let RECONSTRUCT_POLYVAL_REDUCE_G2 =
  REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM polyval_reduce_g2);;

let POLYVAL_REDUCE_G2 = prove
 (`polyval_reduce_g2 p1 p2 p3 =
    polyval_reduce_prop3
      ((word_join : int128 -> int128 -> (256)word)
         (word_join (word_subword p2 (64,64):int64)
                    (word_xor (word_subword (word_xor (word_xor p1 p2) p3)
                                            (64,64):int64)
                              (word_subword p2 (0,64):int64)): int128)
         (word_join (word_xor (word_subword
          (word_xor (word_xor p1 p2) p3) (0,64):int64)
                    (word_subword p1 (64,64):int64))
                    (word_subword p1 (0,64):int64): int128))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_g2; polyval_reduce_prop3;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 =  (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  ABBREV_TAC `ks:int128 = word_xor (word_xor p1 p2) p3` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w2:int128 = word_pmul
     (word_xor (word_xor (word_subword (w1:int128) (0,64):int64)
                     (word_subword (p1:int128) (64,64):int64))
           (word_subword (ks:int128) (0,64):int64))
     (word 13979173243358019584:int64)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o LAND_CONV)
   [WORD_BITWISE_RULE
    `word_xor (word_xor w1 p1) ks = word_xor (word_xor ks p1) w1`]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Variants of the existing Karatsuba lemmas better fitting the code.        *)
(* ------------------------------------------------------------------------- *)

let PMUL_KARATSUBA_JOIN = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (0,64):int64)
                                 (word_subword a (64,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC WORD_BLAST);;

let PMUL_KARATSUBA_JOIN_ALT = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (64,64):int64)
                                 (word_subword a (0,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REWRITE_TAC[PMUL_KARATSUBA_JOIN] THEN REWRITE_TAC[WORD_XOR_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(*                                                                           *)
(* This covers the body of the function with the save/restore boilerplate    *)
(* excised: PC starts at pc + 0x2c (first real instruction after the 11      *)
(* save instructions) and ends at pc + 0x3cc (first ldp of the postamble).   *)
(* The stackpointer is the value AFTER the sub sp, #0xa0 adjustment, i.e.    *)
(* the value the SP register actually holds inside the function body.        *)
(*                                                                           *)
(* Arguments (Standard ARM ABI, values in registers at core entry):          *)
(*   X0 = in        input buffer (len_bits/8 bytes)                          *)
(*   X1 = len_bits  length in bits (whole 16-byte blocks)                    *)
(*   X2 = out       output buffer (len_bits/8 bytes)                         *)
(*   X3 = tag       16-byte GHASH accumulator (in/out)                       *)
(*   X4 = ivec      16-byte counter block (in/out)                           *)
(*   X5 = key       AES-128 round keys (176 bytes = 11 x 16)                 *)
(*   X6 = Htable    192-byte precomputed H-powers table                      *)
(*   returns X0 = byte_len (= len_bits / 8)                                  *)
(* ------------------------------------------------------------------------- *)

(*** Note that the NIST-level specs consider all byte-level encodings as
 *** big-endian, and the AES-related ARM instructions take that view too.
 *** Hence in the precondition "ctr_block" and "rk" correspond as 128-bit
 *** words to the NIST specifications. Since they are loaded from memory
 *** in the usual little-endian ARM fashion, we byte-reverse when
 *** specifying them as the values in any memory cells.
 ***)

let AES_GCM_ENC_KERNEL_X4_BASIC_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc.
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16)]
        [(word pc, LENGTH aes_gcm_enc_kernel_x4_basic_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_x4_basic_mc /\
           read PC s = word (pc + 0x2c) /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = word (pc + 0x3cc) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24;
                  X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES_GCM_ENC_KERNEL_X4_BASIC_EXEC] THEN

  (*** Abbreviate the loop counts to keep goal terms manageable ***)

  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN

  (*** Break up the round key list - a bit clumsy ****)

  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN

  (***** Initial state setup ****)

  ENSURES_SEQUENCE_TAC `pc + 0x8c`
   `\s. read X0 s = in_p /\
        read X2 s = out_p /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X6 s = htable_p /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read Q28 s = word_reversefields 8 (EL 10 rk) /\
        read Q7 s = word 13979173243358019584 /\
        read Q30 s = word 79228162514264337593543950336 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
        read Q31 s = word_reversefields 32 (ctr_block nonce 2) /\
        read Q11 s =
          byteswap128 tag0 /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!i. i < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                 inblock i)` THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_USHR_COMPOSE] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[word_ushr] THEN
      MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[word_ushr; ARITH_RULE `2 EXP 7 = 128`] THEN
      REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN
      EXPAND_TAC "loop_remain" THEN ARITH_TAC;
      REWRITE_TAC[usimd4; usimd2; ctr_block; DIMINDEX_32] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      CONV_TAC WORD_BLAST;
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    MAP_EVERY VAL_INT64_TAC
     [`nblocks:num`; `loop_count:num`; `loop_remain:num`]] THEN

  (*** Break code between main unrolled loop and tail loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0x2f4`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X6 s = htable_p /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read Q28 s = word_reversefields 8 (EL 10 rk) /\
        read Q7 s = word 13979173243358019584 /\
        read Q30 s = word 79228162514264337593543950336 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word 0 /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
        read Q31 s = word_reversefields 32
                       (ctr_block nonce (4 * loop_count + 2)) /\
        read Q11 s =
          byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock)
                            (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_CASES_TAC `loop_count = 0` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN
      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [1] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; CONJUNCT1 LT] THEN
      REWRITE_TAC[list_of_seq; nist_ghash] THEN CONV_TAC WORD_RULE;
      ALL_TAC] THEN

    (**** Loop setup for the main unrolled loop ***)

    ENSURES_WHILE_UP_TAC `loop_count:num` `pc + 0x090` `pc + 0x2f0`
      `\i s.
        read X0  s = word_add in_p  (word (64 * i)) /\
        read X2  s = word_add out_p (word (64 * i)) /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X6 s = htable_p /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\
        read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\
        read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\
        read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\
        read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\
        read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read Q28 s = word_reversefields 8 (EL 10 rk) /\
        read Q7 s = word 13979173243358019584 /\
        read Q30 s = word 79228162514264337593543950336 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word(loop_count - i) /\
        read X7 s = word nblocks /\
        read X9 s = word loop_remain /\
        read Q31 s = word_reversefields 32 (ctr_block nonce (4 * i + 2)) /\
        read Q11 s =
          byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
        (!j. j < 4 * i
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
    ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [1] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0; LT;
                  list_of_seq; nist_ghash];

      (**** Main loop invariant (main unrolled loop) ****)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read (memory :> bytes128 (word_add in_p (word (64 * i)))) s0 =
        inblock (4 * i) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 16)))) s0 =
        inblock (4 * i + 1) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 32)))) s0 =
        inblock (4 * i + 2) /\
        read (memory :> bytes128 (word_add in_p (word (64 * i + 48)))) s0 =
        inblock (4 * i + 3)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE
         `64 * i + 16 = 16 * (4 * i + 1) /\
          64 * i + 32 = 16 * (4 * i + 2) /\
          64 * i + 48 = 16 * (4 * i + 3)`] THEN
        REWRITE_TAC[ARITH_RULE `64 * a = 16 * 4 * a`] THEN
        REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [n] THEN
            RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
          (1--152) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `j < 4 * (i + 1) <=>
                              j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/
                              j = 4 * i + 2 \/ j = 4 * i + 3`] THEN
      ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
      REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
      CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
      REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
      REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
      ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
      DISCARD_STATE_TAC "s152" THEN
      REWRITE_TAC[ADD_ASSOC; ARITH] THEN
      REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
      REWRITE_TAC[GSYM cipher_block] THEN
      REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
      SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
      REWRITE_TAC [byteswap128; WORD_BLAST
      `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
       word_join (word_subword h (0,64):int64)
                 (word_subword l (64,64):int64)`] THEN
      MATCH_MP_TAC(BITBLAST_RULE
       `x:int128 = y
        ==> word_join (word_subword x (0,64):int64)
                      (word_subword x (64,64):int64):int128 =
            word_join (word_subword y (0,64):int64)
                      (word_subword y (64,64):int64):int128`) THEN
      MAP_EVERY ABBREV_TAC
       [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                   (list_of_seq (nist_cipher_block nonce rk inblock) (4 * i)))`;
        `cipherblock_0 = nist_cipher_block nonce rk inblock (4 * i)`;
        `cipherblock_1 = nist_cipher_block nonce rk inblock (4 * i + 1)`;
        `cipherblock_2 = nist_cipher_block nonce rk inblock (4 * i + 2)`;
        `cipherblock_3 = nist_cipher_block nonce rk inblock (4 * i + 3)`;
        `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
        `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
        `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
        `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
      REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
      REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
      TRANS_TAC EQ_TRANS
       `polyval_reduce_prop3
            (word_xor
            (word_pmul (cipherblock_3:int128) (h0:int128))
            (word_xor
            (word_pmul (cipherblock_2:int128) (h1:int128))
            (word_xor
            (word_pmul (cipherblock_1:int128) (h2:int128))
            (word_pmul (word_xor (sofar:int128) cipherblock_0)
                       (h3:int128)))))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
        REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[karatsuba_mid] THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
        ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
         `word_pmul (word_xor a b) (word_xor c d) =
          word_pmul (word_xor b a) (word_xor c d)`] THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        AP_TERM_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                     `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                     `sofar:int128`; `cipherblock_0:int128`]
                    GHASH_POLYVAL_ACC_BATCHED) THEN
      REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
      CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
      REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
      REWRITE_TAC[ARITH_RULE `4 * i + 4 = SUC(SUC(SUC(SUC(4 * i))))`] THEN
      REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
      REWRITE_TAC[APPEND] THEN
      REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL];

      (**** Trivial loop-back goal (main unrolled loop) ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [1] THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ];

      (*** Trivial bridge between the two loops ***)

      ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [1] THEN
      REWRITE_TAC[SUB_REFL]];

    ALL_TAC] THEN

  (*** Trivial case of the tail loop ***)

  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC BITBLAST_RULE;

    ALL_TAC] THEN

  (*** Loop setup for the tail loop ***)

  ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0x304` `pc + 0x3b4`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
      read X3 s = tag_p /\
      read X4 s = ivec_p /\
      read X6 s = htable_p /\
      read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
      read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce 2) /\
      read Q18 s = word_reversefields 8 (EL 0 rk) /\
      read Q19 s = word_reversefields 8 (EL 1 rk) /\
      read Q20 s = word_reversefields 8 (EL 2 rk) /\
      read Q21 s = word_reversefields 8 (EL 3 rk) /\
      read Q22 s = word_reversefields 8 (EL 4 rk) /\
      read Q23 s = word_reversefields 8 (EL 5 rk) /\
      read Q24 s = word_reversefields 8 (EL 6 rk) /\
      read Q25 s = word_reversefields 8 (EL 7 rk) /\
      read Q26 s = word_reversefields 8 (EL 8 rk) /\
      read Q27 s = word_reversefields 8 (EL 9 rk) /\
      read Q28 s = word_reversefields 8 (EL 10 rk) /\
      read Q7 s = word 13979173243358019584 /\
      read Q30 s = word 79228162514264337593543950336 /\
      read X15 s = word(len_bits DIV 8) /\
      read X9 s = word(loop_remain - i) /\
      read Q31 s = word_reversefields 32
                    (ctr_block nonce (4 * loop_count + i + 2)) /\
      read Q11 s =
        byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block nonce rk inblock)
                          (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128
        (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q13 s = byteswap128
       (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block nonce rk j) (inblock j))` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** Main loop invariant (tail loop) ****)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128
        (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [n] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
     (1--44) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s44" THEN
    REWRITE_TAC[ADD_ASSOC; ARITH] THEN
    REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
    REWRITE_TAC[GSYM cipher_block] THEN
    REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
    `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
     word_join (word_subword h (0,64):int64)
               (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64)
                    (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64)
                    (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) 
                              (4 * loop_count + i)))`;
      `cipherblock =
        nist_cipher_block nonce rk inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `k = karatsuba_mid h`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
      `polyval_reduce_prop3
          (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      LET_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
      ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM polyval_dot] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
    REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
    REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND; 
                NIST_GHASH_CONS; nist_ghash] THEN
    ASM_REWRITE_TAC[];

    (*** Trivial loop-back goal (tail loop) ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC [1] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ];

    (**** Final writeback, reversal etc. ***)

    ARM_SIM_TAC AES_GCM_ENC_KERNEL_X4_BASIC_EXEC (1--6) THEN
    REWRITE_TAC[ADD_ASSOC] THEN
    SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[byteswap128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC BITBLAST_RULE]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness: lifts the core proof through the save/restore     *)
(* boilerplate and the final ret. This is the theorem used externally.       *)
(* ------------------------------------------------------------------------- *)

(*** The externally-used spec. Its pre/postconditions match the core theorem
 *** (CTR ciphertext output, GHASH tag, updated counter), lifted through the
 *** save/restore prologue/epilogue and the final ret. The stack frame region
 *** (160 bytes below the incoming SP) is added to the nonoverlapping lists and
 *** to the MAYCHANGE. ARM_ADD_RETURN_STACK_TAC does the lifting; we expand the
 *** compound memory predicates htable_mem_4 and wordlist_from_memory (in both
 *** the goal and the fed core theorem) so the interior big-step's precondition
 *** obligation is discharged with no residual subgoal.
 ***)

let AES_GCM_ENC_KERNEL_X4_BASIC_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 160), 160)]
      [(word pc, LENGTH aes_gcm_enc_kernel_x4_basic_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 160), 160)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes_gcm_enc_kernel_x4_basic_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = returnaddress /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + 2)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 160), 160)])`,
  REWRITE_TAC[fst AES_GCM_ENC_KERNEL_X4_BASIC_EXEC; htable_mem_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES_GCM_ENC_KERNEL_X4_BASIC_EXEC
    (CONV_RULE(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)
       (REWRITE_RULE[fst AES_GCM_ENC_KERNEL_X4_BASIC_EXEC; htable_mem_4]
          AES_GCM_ENC_KERNEL_X4_BASIC_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 160);;
