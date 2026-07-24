(* ========================================================================= *)
(* NIST-vocabulary convergence layer for the whole-blocks decrypt dispatch.  *)
(*                                                                           *)
(* Restates AESV8_GCM_8X_DEC_256_WB_DISPATCH in jargh's x4-kernel statement  *)
(* shape (the loop-invariant vocabulary for the future main-loop proof):     *)
(*  - htable_mem_8: htable_mem_4-style named memory predicate over h_power   *)
(*    indexing, for the 12-slot aws-lc htable layout (packed karatsuba mids).*)
(*  - GCM_DEC_FINAL_XI_NIST: gcm_dec_final_xi = byte-reversed nist_ghash     *)
(*    under byteswap128 h = ghash_twist H (Gueron Prop 1 via                 *)
(*    NIST_GHASH_IS_POLYVAL from common/ghash_nist_bridge.ml).               *)
(*  - AESV8_GCM_8X_DEC_256_WB_DISPATCH_NIST_TAG: the <=8-block dispatch with *)
(*    precondition htable_mem_8 (ghash_twist H) / tag word_reversefields 8   *)
(*    tag0 and tag postcondition word_reversefields 8 (nist_ghash H tag0 ...)*)
(*    Derived SIM-FREE from WB_DISPATCH by instantiation + rewriting.        *)
(* No CHEAT_TAC, no new axioms.                                              *)
(* ========================================================================= *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_wb.ml";;
needs "common/ghash_nist_bridge.ml";;

(* ---- karatsuba_mid ignores the byteswap of its argument ------------------- *)
let KARATSUBA_MID_BYTESWAP = prove
 (`!x:int128. karatsuba_mid (byteswap128 x) = karatsuba_mid x`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN
  CONV_TAC WORD_BLAST);;

(* ---- h_power 0..7 unfolded to the explicit left-nested dot chains --------- *)
let H_POWER_UNFOLD_7 = prove
 (`h_power (hb:int128) 0 = hb /\
   h_power hb 1 = polyval_dot hb hb /\
   h_power hb 2 = polyval_dot (polyval_dot hb hb) hb /\
   h_power hb 3 = polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb /\
   h_power hb 4 = polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb /\
   h_power hb 5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb /\
   h_power hb 6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb /\
   h_power hb 7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) hb`,
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ---- htable_mem_dec in h_power form (kills the nested let-towers) --------- *)
let HTABLE_MEM_DEC_H_POWER = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=>
     read (memory :> bytes128 ptr) s = byteswap128 (h_power (byteswap128 h) 0) /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 1))
                 (karatsuba_mid (h_power (byteswap128 h) 0)) /\
     read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128 (h_power (byteswap128 h) 1) /\
     read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128 (h_power (byteswap128 h) 2) /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 3))
                 (karatsuba_mid (h_power (byteswap128 h) 2)) /\
     read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128 (h_power (byteswap128 h) 3) /\
     read (memory :> bytes128 (word_add ptr (word 96))) s = byteswap128 (h_power (byteswap128 h) 4) /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 5))
                 (karatsuba_mid (h_power (byteswap128 h) 4)) /\
     read (memory :> bytes128 (word_add ptr (word 128))) s = byteswap128 (h_power (byteswap128 h) 5) /\
     read (memory :> bytes128 (word_add ptr (word 144))) s = byteswap128 (h_power (byteswap128 h) 6) /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 7))
                 (karatsuba_mid (h_power (byteswap128 h) 6)) /\
     read (memory :> bytes128 (word_add ptr (word 176))) s = byteswap128 (h_power (byteswap128 h) 7)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[htable_mem_dec] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[H_POWER_UNFOLD_7; KARATSUBA_MID_BYTESWAP; BYTESWAP128_INVOLUTION]);;

(* ---- the JRH-style named htable predicate over the abstract key hk -------- *)
(* hk is the POLYVAL-side key (byteswap128 of the memory h slot); with
   hk = ghash_twist H this is the exact analogue of JRH's
   htable_mem_4 (ghash_twist ...) hypothesis, extended to 8 powers /
   12 slots (aws-lc layout with packed karatsuba mids). *)
let htable_mem_8 = new_definition
 `htable_mem_8 (hk:int128) (ptr:int64) (s:armstate) <=>
    read (memory :> bytes128 ptr) s = byteswap128 (h_power hk 0) /\
    read (memory :> bytes128 (word_add ptr (word 16))) s =
      word_join (karatsuba_mid (h_power hk 1)) (karatsuba_mid (h_power hk 0)) /\
    read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128 (h_power hk 1) /\
    read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128 (h_power hk 2) /\
    read (memory :> bytes128 (word_add ptr (word 64))) s =
      word_join (karatsuba_mid (h_power hk 3)) (karatsuba_mid (h_power hk 2)) /\
    read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128 (h_power hk 3) /\
    read (memory :> bytes128 (word_add ptr (word 96))) s = byteswap128 (h_power hk 4) /\
    read (memory :> bytes128 (word_add ptr (word 112))) s =
      word_join (karatsuba_mid (h_power hk 5)) (karatsuba_mid (h_power hk 4)) /\
    read (memory :> bytes128 (word_add ptr (word 128))) s = byteswap128 (h_power hk 5) /\
    read (memory :> bytes128 (word_add ptr (word 144))) s = byteswap128 (h_power hk 6) /\
    read (memory :> bytes128 (word_add ptr (word 160))) s =
      word_join (karatsuba_mid (h_power hk 7)) (karatsuba_mid (h_power hk 6)) /\
    read (memory :> bytes128 (word_add ptr (word 176))) s = byteswap128 (h_power hk 7)`;;

let HTABLE_MEM_DEC_IS_HTABLE_MEM_8 = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=> htable_mem_8 (byteswap128 h) ptr s`,
  REWRITE_TAC[HTABLE_MEM_DEC_H_POWER; htable_mem_8]);;

(* ---- the tag spec in nist_ghash vocabulary -------------------------------- *)
(* Our band/dispatch statements quantify the raw htable h slot; JRH
   quantifies the NIST key H with the twist applied in the hypothesis.
   The two are related by byteswap128 h = ghash_twist H, under which
   gcm_dec_final_xi IS a byte-reversed nist_ghash (Gueron Prop 1 via
   NIST_GHASH_IS_POLYVAL). *)
let GCM_DEC_FINAL_XI_NIST = prove
 (`!(H:int128) (h:int128) len x xi.
     byteswap128 h = ghash_twist H
     ==> gcm_dec_final_xi len x xi h =
         word_bytereverse
           (nist_ghash H (word_bytereverse xi)
              (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[gcm_dec_final_xi; NIST_GHASH_IS_POLYVAL]);;

(* ---- word_bytereverse = word_reversefields 8 at :128 ----------------------- *)
let BREV_RF8_128 = prove
 (`word_bytereverse (x:int128) = word_reversefields 8 x`,
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] WORD_BYTEREVERSE_REVERSEFIELDS]);;

let BREV_RF8_INV_128 = prove
 (`!x:int128. word_bytereverse (word_reversefields 8 x) = x`,
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ---- the dispatch theorem in full JRH vocabulary --------------------------- *)
(* Derived sim-free from AESV8_GCM_8X_DEC_256_WB_DISPATCH:
   h := byteswap128 (ghash_twist H), xi := word_reversefields 8 tag0.
   Precondition: htable_mem_8 (ghash_twist H) htbl_p s,
                 read xi_p = word_reversefields 8 tag0.
   Tag postcondition:
     read xi_p = word_reversefields 8
       (nist_ghash H tag0
          (MAP word_bytereverse (gcm_dec_ghash_blocks (16*nblk) ibytes))). *)
let AESV8_GCM_8X_DEC_256_WB_DISPATCH_NIST_TAG =
  let vars,_ = strip_forall (concl AESV8_GCM_8X_DEC_256_WB_DISPATCH) in
  let hvar = `h:int128` and xivar = `xi:int128` in
  let hnist = `byteswap128 (ghash_twist H)` in
  let th0 = INST [hnist,hvar] (SPEC_ALL AESV8_GCM_8X_DEC_256_WB_DISPATCH) in
  let bsw_inv = SPEC `ghash_twist H` BYTESWAP128_INVOLUTION in
  let xi_rw = MP (SPECL [`H:int128`; hnist; `16 * nblk`; `ibytes:byte list`;
                         `xi:int128`] GCM_DEC_FINAL_XI_NIST) bsw_inv in
  let th1 = REWRITE_RULE[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; bsw_inv; xi_rw] th0 in
  let th2 = INST [`word_reversefields 8 (tag0:int128)`,xivar] th1 in
  let th3 = REWRITE_RULE[BREV_RF8_INV_128; BREV_RF8_128] th2 in
  GENL (map (fun v -> if v = hvar then `H:int128`
             else if v = xivar then `tag0:int128` else v) vars) th3;;

(* sanity: no hypotheses, no new axioms *)
let () =
  if hyp AESV8_GCM_8X_DEC_256_WB_DISPATCH_NIST_TAG <> [] then
    failwith "DISPATCH_NIST_TAG has hypotheses"
  else if List.length (axioms()) <> 3 then
    failwith "unexpected axiom count"
  else Format.print_string "DISPATCH_NIST_TAG: hyps=0, axioms=3\n";;
