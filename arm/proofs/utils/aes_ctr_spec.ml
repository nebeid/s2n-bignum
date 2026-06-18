(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
(* ========================================================================= *)
(* Recursive AES-256 counter-mode (CTR) ciphertext spec (XTS-style, but over  *)
(* an int128 block list rather than a byte list).  Part of the shared AES-GCM *)
(* spec home (N-block plan, Task 4).                                          *)
(*                                                                            *)
(* CTR is symmetric: this same spec serves encrypt (data = plaintext) and     *)
(* decrypt (data = ciphertext) -- the transform word_xor x (aes256_encrypt    *)
(* (gcm_ctr_inc_iter k ctr0) keys) is identical either way.                   *)
(*                                                                            *)
(* Design (see _docs/aesv8-gcm-nblock-generalization-plan-20260617.md, D1/D3):*)
(*  - element type = int128 (one per 16-byte block); thin bytes<->int128      *)
(*    adapters are added only where a memory readback needs them.             *)
(*  - block k's counter = gcm_ctr_inc_iter k ctr0 (the shared DEFINED iterator *)
(*    from arm/proofs/utils/gcm_ctr_helpers.ml), so the recursion composes and *)
(*    an N-block induction steps k -> k+1.                                    *)
(*                                                                            *)
(* No CHEAT_TAC, no new axioms.                                               *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_ctr_helpers.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;

(* One CTR block: data XOR the AES-256 keystream for block index k.           *)
let aes_ctr_block = new_definition
 `aes_ctr_block (ctr0:int128) (k:num) (pt:int128) (keys:int128 list) : int128 =
    word_xor pt (aes256_encrypt (gcm_ctr_inc_iter k ctr0) keys)`;;

(* Recursive CTR over a block list; the block at list position i uses counter *)
(* gcm_ctr_inc_iter (k+i) ctr0.  k = starting block index (0 at buffer head).  *)
(* Plain structural recursion on the list (no WF measure needed).             *)
let aes_ctr_rec = define
 `aes_ctr_rec (ctr0:int128) (k:num) ([]:int128 list) (keys:int128 list) = [] /\
  aes_ctr_rec (ctr0:int128) (k:num) (CONS pt pts) (keys:int128 list) =
    CONS (aes_ctr_block ctr0 k pt keys)
         (aes_ctr_rec ctr0 (k+1) pts keys)`;;

(* Top spec: CTR-encrypt the whole block list starting at block 0.            *)
let aes_ctr = new_definition
 `aes_ctr (ctr0:int128) (pts:int128 list) (keys:int128 list) : int128 list =
    aes_ctr_rec ctr0 0 pts keys`;;

(* LENGTH is preserved (so a bytes(out_p,16*N) framing matches).              *)
let LENGTH_AES_CTR_REC = prove
 (`!pts ctr0 k keys. LENGTH(aes_ctr_rec ctr0 k pts keys) = LENGTH pts`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[aes_ctr_rec; LENGTH]);;

let LENGTH_AES_CTR = prove
 (`!pts ctr0 keys. LENGTH(aes_ctr ctr0 pts keys) = LENGTH pts`,
  REWRITE_TAC[aes_ctr; LENGTH_AES_CTR_REC]);;

(* The per-block workhorse: element i of the recursive ciphertext, for any N.  *)
let EL_AES_CTR_REC = prove
 (`!pts ctr0 k keys i.
     i < LENGTH pts
     ==> EL i (aes_ctr_rec ctr0 k pts keys) =
         aes_ctr_block ctr0 (k+i) (EL i pts) keys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; aes_ctr_rec; LT] THEN
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  ASM_REWRITE_TAC[EL; HD; TL; ADD_CLAUSES; LT_SUC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH(t:int128 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ctr0:int128`;`k+1`;`keys:int128 list`;`n:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k+1)+n = SUC(k+n)`]);;

(* Element i of the top spec, in the explicit word_xor / aes256_encrypt form   *)
(* a binary postcondition's per-block store readback carries.                  *)
let EL_AES_CTR = prove
 (`!pts ctr0 keys i.
     i < LENGTH pts
     ==> EL i (aes_ctr ctr0 pts keys) =
         word_xor (EL i pts) (aes256_encrypt (gcm_ctr_inc_iter i ctr0) keys)`,
  REWRITE_TAC[aes_ctr] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_AES_CTR_REC; aes_ctr_block; ADD_CLAUSES]);;

(* The concrete 2-block reduction (matches AESV8_GCM_8X_ENC_256_2BLOCK's       *)
(* per-block postcond: block 0 uses ctr0, block 1 uses gcm_ctr_inc ctr0).      *)
let AES_CTR_2_EL = prove
 (`EL 0 (aes_ctr ctr0 [pt0;pt1] keys) =
     word_xor pt0 (aes256_encrypt ctr0 keys) /\
   EL 1 (aes_ctr ctr0 [pt0;pt1] keys) =
     word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys)`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; EL; HD; TL]);;

(* The 2-block ciphertext list under MAP word_bytereverse -- the GHASH input   *)
(* list [brev ct0; brev ct1] a 2-block GHASH postcond carries.                 *)
let AES_CTR_2_MAP_BREV = prove
 (`MAP word_bytereverse (aes_ctr ctr0 [pt0;pt1] keys) =
   [word_bytereverse (word_xor pt0 (aes256_encrypt ctr0 keys));
    word_bytereverse (word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys))]`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter; MAP]);;
