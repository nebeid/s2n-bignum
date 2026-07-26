(* ========================================================================= *)
(* WB AES-256-GCM decrypt main loop (nblk > 8): ENSURES_WHILE proof.          *)
(*                                                                            *)
(* Extends the proven <=8-block WB chain (aesv8_gcm_8x_dec_256_wb.ml) to the  *)
(* software-pipelined 8-blocks-per-iteration main loop .L256_dec_main_loop    *)
(* (0x4a0..0x9ec), the GHASH catch-up prepretail (0x9f0..0xec0), and the tail *)
(* cascade (0xec0), so correctness holds for arbitrary nblk >= 1.             *)
(*                                                                            *)
(* Binary: arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o (frozen).                    *)
(* Plan:   _docs/wb-main-loop-plan.md (sec 3b -> 4 -> 5), with the pipeline   *)
(*         correction from orchestrator/logs/plan-rationale.md baked in:      *)
(*         GHASH lags stores by one 8-block group, so the ENSURES_WHILE       *)
(*         invariant is the TWO-STREAM form (store/counter stream at 8(i+1),  *)
(*         GHASH stream at 8i, bridged by raw ciphertext regs q8..q15), NOT   *)
(*         a lag-free single fold.                                            *)
(*                                                                            *)
(* This file holds, in phase order:                                          *)
(*   Sec 1. Scalar rung lemmas (nblk>8 generalizations; pure word/arith).     *)
(*   Sec 2. Symbolic counter layer (gcm_ctr_add; closed form at symbolic k).  *)
(*   [later] FRONT-N capture (WBN_FRONT_BUF), ENSURES_WHILE loop, prepretail, *)
(*           recomposition, subroutine wrapper.                               *)
(*                                                                            *)
(* Lemmas in sec 1-2 were developed and committed in work.ml (commit          *)
(* 41f4953b) and are moved here verbatim (all proved; total < 2s).            *)
(* ========================================================================= *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_wb.ml";;
(* aes_xts_common: IVAL_WORD_LT.  gcm_ctr_helpers: gcm_ctr_inc / _iter, the
   GCM_CTR_INC*_LANES lemmas.  Both are no-ops if wb.ml already pulled them. *)
needs "arm/proofs/utils/aes_xts_common.ml";;
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Scalar rung lemmas (nblk > 8 generalizations of USHR_128NBLK /         *)
(*    AND_MASK_16NBLK).  All pure word/arith, no sim.                        *)
(*                                                                           *)
(* NOTE (signed pointer compares): the 0x42c/0x49c/0x9e4 cmp x0,x5 feed      *)
(* b.ge/b.lt = SIGNED conditions on pointers.  For nblk <= 8 x5 = in_p so    *)
(* the compare was reflexive; for nblk > 8 the exactness of                  *)
(* ival(x0) - ival(x5) needs the buffer to not straddle the 2^63 signed     *)
(* boundary: hypothesis WB_PTR_OK below (satisfied by all userspace bufs).   *)
(* ------------------------------------------------------------------------- *)

(* x9 := bit_len >> 3 = 16*nblk, now for ALL nblk with 128*nblk < 2^64 *)
let USHR_128NBLK_ANY = prove
 (`!nblk. 128 * nblk < 2 EXP 64
        ==> word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN AP_TERM_TAC THEN ARITH_TAC);;

(* the loop byte bound: (16*nblk - 1) AND ~127 = 128 * ((nblk-1) DIV 8) *)
let AND_MASK_16NBLK_ANY = prove
 (`!nblk. 1 <= nblk /\ 16 * nblk < 2 EXP 64
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 =
            word (128 * ((nblk - 1) DIV 8))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word 18446744073709551488:int64 = word_not (word (2 EXP 7 - 1))`
    SUBST1_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `word_sub (word (16 * nblk)) (word 1):int64 = word (16 * nblk - 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (16 * nblk - 1):int64) = 16 * nblk - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(16 * nblk - 1) DIV 2 EXP 7 = (nblk - 1) DIV 8` SUBST1_TAC THENL
   [ALL_TAC; ARITH_TAC] THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (nblk - 1) DIV 8` THEN ABBREV_TAC `m = (nblk - 1) MOD 8` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk = d * 8 + m + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `16 * m + 15` THEN ASM_ARITH_TAC);;

(* exact ival of an in-range pointer offset (for the signed pointer compares
   cmp x0,x5 at 0x3e0/0x440/0x9e4 feeding b.ge/b.lt) *)
let IVAL_PTR_ADD = prove
 (`!(p:int64) a. val p + a < 2 EXP 63 ==> ival (word_add p (word a)) = &(val p + a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add p (word a):int64 = word (val p + a)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_WORD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* NOTE: ival(word_neg(word d)) needs d <= 2^63 *)
let IVAL_NEG_SMALL = prove
 (`!d. d <= 2 EXP 63 ==> ival (word_neg (word d):int64) = -- &d`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_NEG] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[INT_ARITH `--(&9223372036854775808):int <= -- &d /\ -- &d < &9223372036854775808 <=> &d <= &9223372036854775808`] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

(* signed sub of two small words *)
let IVAL_WSUB_SMALL = prove
 (`!a d. a < 2 EXP 63 /\ d < 2 EXP 63
      ==> ival (word_sub (word a) (word d):int64) = &a - &d`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `a < d \/ d <= a:num`) THENL
   [SUBGOAL_THEN `word_sub (word a) (word d):int64 = word_neg (word (d - a))` SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [WORD_RULE `word_sub (word a) (word d):int64 = word_neg (word_sub (word d) (word a))`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ival (word_neg (word (d - a)):int64) = -- &(d - a)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_NEG_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(d - a):int = &d - &a` SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
    SUBGOAL_THEN `word_sub (word a) (word d):int64 = word (a - d)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ival (word (a - d):int64) = &(a - d)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(a - d):int = &a - &d` SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; INT_ARITH_TAC]]);;

(* small pointer has exact ival *)
let IVAL_SMALL_PTR = prove
 (`!(p:int64). val p < 2 EXP 63 ==> ival p = &(val p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IVAL_VAL; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `bit 63 (p:int64) <=> F` SUBST1_TAC THENL
   [MP_TAC(ISPEC `p:int64` MSB_VAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC]);;

(* the generic signed pointer-compare flag resolver:
   cmp x0,x5 with x0 = p + a, x5 = (word d) + p; b.ge/b.lt read NF<=>VF,
   which under no-2^63-straddle collapses to a < d *)
let WB_PTRCMP_FLAGS = prove
 (`!(in_p:int64) a d.
      val in_p + a < 2 EXP 63 /\ val in_p + d < 2 EXP 63
      ==> (ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p)) < &0 <=> a < d) /\
          ((ival (word_add in_p (word a)) - ival (word_add (word d) in_p) =
            ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p))) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word a):int64) = &(val in_p + a) /\
                ival (word_add in_p (word d):int64) = &(val in_p + d)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add in_p (word a)) (word_add in_p (word d)):int64 =
                word_sub (word a) (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_sub (word a) (word d):int64) = &a - &d` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_WSUB_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_ARITH `(&v + &a) - (&v + &d):int = &a - &d`] THEN
  REWRITE_TAC[INT_ARITH `&a - &d:int < &0 <=> &a:int < &d`; INT_OF_NUM_LT]);;

(* specialization for the 0x42c loop-entry b.ge with x0 = in_p (a = 0):
   in the nblk>8 regime the branch FALLS THROUGH (NF=T <=> VF=F test fails) *)
let WB_LOOPENTER_FLAGS = prove
 (`!(in_p:int64) nblk. 17 <= nblk /\ 128 * nblk < 2 EXP 62 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = 128 * (nblk - 1) DIV 8` THEN
  SUBGOAL_THEN `1 <= d /\ d <= 16 * nblk /\ d <= 2 EXP 63` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub p (word_add (word d) p):int64 = word_neg (word d)`] THEN
  ASM_SIMP_TAC[IVAL_NEG_SMALL] THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word d):int64) = &(val in_p + d)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival (in_p:int64) = &(val in_p)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_SMALL_PTR THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `--(&d):int < &0 <=> &0:int < &d`; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* d = 128*((nblk-1) DIV 8) > 128 iff nblk >= 17 (drives the 0x49c skip) *)
let D_GT_128 = prove
 (`!nblk. 17 <= nblk ==> (128 < 128 * (nblk - 1) DIV 8 <=> T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 128 < 128 * q`) THEN
  SUBGOAL_THEN `16 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* byte-level restatement (proved as warm-up; kept for the seam arithmetic) *)
let DIV128_16NBLK = prove
 (`!nblk. 1 <= nblk ==> (16 * nblk - 1) DIV 128 = (nblk - 1) DIV 8`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (nblk - 1) DIV 8` THEN ABBREV_TAC `m = (nblk - 1) MOD 8` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk = d * 8 + m + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `16 * m + 15` THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. Symbolic counter layer: gcm_ctr_add w = "add w to the be-top-lane".    *)
(*    Gives the invariant a closed counter form at symbolic block index:     *)
(*    gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x.                         *)
(*                                                                           *)
(*    OOM WARNING: do NOT prove GCM_CTR_ADD_LANES by direct BITBLAST -- the  *)
(*    symbolic 32-bit addend makes the BDD blow past 30GB (killed session    *)
(*    2026-07-24).  The factoring below keeps every BITBLAST wiring-only     *)
(*    (word_add never meets the BDD); whole layer proves in <1s.             *)
(* ------------------------------------------------------------------------- *)

let gcm_ctr_add = new_definition
 `gcm_ctr_add (w:32 word) (ivec:128 word) : 128 word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse (word_subword ivec (96,32):(32)word)) w))`;;

let GCM_CTR_ADD_1 = prove
 (`gcm_ctr_add (word 1) = gcm_ctr_inc`,
  REWRITE_TAC[FUN_EQ_THM; gcm_ctr_add; gcm_ctr_inc]);;

(* wiring-only: byte decomposition of the byte-reversed top lane *)
let BREV_TOP_LANE = prove
 (`!ctr0:int128.
     word_bytereverse (word_subword ctr0 (96,32):32 word) =
     word_join
      (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
      (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* wiring-only: insert of brev s as the byte-join tower; s stays FREE so the
   abstract add never enters the BDD *)
let INSERT_BREV_WIRING = prove
 (`!(ctr0:int128) (s:32 word).
     word_insert ctr0 (96,32) (word_bytereverse s) : 128 word =
     word_join
      (word_join
       (word_join
        (word_join (word_subword s (0,8):8 word) (word_subword s (8,8):8 word):16 word)
        (word_join (word_subword s (16,8):8 word) (word_subword s (24,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
        (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word)
        :32 word) :64 word)
      (word_join
       (word_join
        (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
        (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
        (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word)
        :32 word) :64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* the generic-w lanes lemma: RHS built programmatically from
   GCM_CTR_INC_LANES with `w` for `word 1` (exactly the harvested Q-lane
   shape from the front sim); proof is pure rewriting *)
let GCM_CTR_ADD_LANES =
  let lanes_w = subst [`w:32 word`,`word 1:32 word`]
    (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES)))) in
  let gl = list_mk_forall([`w:32 word`;`ctr0:int128`],
    mk_eq(list_mk_comb(`gcm_ctr_add`,[`w:32 word`;`ctr0:int128`]), lanes_w)) in
  prove(gl,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[gcm_ctr_add; BREV_TOP_LANE; INSERT_BREV_WIRING]);;

(* algebra of the symbolic add *)
let SUBWORD_INSERT_TOP = prove
 (`!(x:int128) (v:32 word). word_subword (word_insert x (96,32) v : int128) (96,32) = v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let INSERT_INSERT_TOP = prove
 (`!(x:int128) (u:32 word) (v:32 word).
     word_insert (word_insert x (96,32) (u:32 word) : int128) (96,32) (v:32 word) : int128 =
     word_insert x (96,32) v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let BREV_BREV_32 = prove
 (`!s:32 word. word_bytereverse (word_bytereverse s) = s`,
  GEN_TAC THEN BITBLAST_TAC);;

let INSERT_SELF_TOP = prove
 (`!x:int128. word_insert x (96,32) (word_subword x (96,32):32 word) : int128 = x`,
  GEN_TAC THEN BITBLAST_TAC);;

let GCM_CTR_ADD_COMPOSE = prove
 (`!(u:32 word) (v:32 word) (x:int128).
     gcm_ctr_add v (gcm_ctr_add u x) = gcm_ctr_add (word_add u v) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcm_ctr_add] THEN
  REWRITE_TAC[SUBWORD_INSERT_TOP; INSERT_INSERT_TOP; BREV_BREV_32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GCM_CTR_ADD_0 = prove
 (`!x:int128. gcm_ctr_add (word 0) x = x`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_add; WORD_ADD_0; BREV_BREV_32; INSERT_SELF_TOP]);;

(* the closed form the ENSURES_WHILE invariant needs: counter at symbolic
   block index k *)
let GCM_CTR_INC_ITER_ADD = prove
 (`!k x:int128. gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_ADD_0];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN
    CONV_TAC WORD_RULE]);;

(* the RAW counter accumulator kept in v30 (session-007 finding, session-008
   promoted here): byte-grouped rep with top 32-bit lane incremented by w.
   The body's first instr `rev32 v5,v30` reads it, so the Sec-4 invariant pins
   Q30 = gcm_ctr_raw (word (8*i+13)) ctr0 -- hence this definition must precede
   Sec 4.  Its algebra lemmas (SUBW_RAW_*, GCM_CTR_RAW_INCR, REV32_FOLD_TAC) are
   body-only and stay in Sec 9b.
   rev32(gcm_ctr_raw w ctr0) = gcm_ctr_add w ctr0 (the AES input for block w);
   word_add (gcm_ctr_raw w ctr0) (word 2^96) = gcm_ctr_raw (word_add w 1) ctr0. *)
let gcm_ctr_raw_def = new_definition
 `gcm_ctr_raw (w:32 word) (ctr0:int128) : int128 =
   word_join
    (word_join
      (word_add
        (word_join
          (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
          (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word)
        w)
      (word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
        (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word):64 word)
    (word_join
      (word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
        (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word)
      (word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
        (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word):64 word):int128`;;

(* ------------------------------------------------------------------------- *)
(* 3. FRONT-N: capture the nblk>8 front (entry 0x20 -> loop head 0x4a0) as    *)
(*    WBN_FRONT_BUF.  Its harvested postcondition (state s288 at the loop     *)
(*    head) IS the i=0 instance of the ENSURES_WHILE loop invariant.          *)
(*                                                                            *)
(* Deltas vs wb.ml's <=8-block WB_FRONT_BUF (entry 0x20 -> 0x42c tail):       *)
(*  - hyps: 1<=nblk /\ nblk<=8  becomes  17<=nblk /\ 128*nblk<2^62 /\         *)
(*    val in_p + 16*nblk < 2^63 (the signed pointer-compare no-2^63-straddle).*)
(*  - prep uses the _ANY scalar rungs (X5 = word(128*((nblk-1)DIV8)) not 0).  *)
(*  - front steps 1..259 identical to WB_FRONT_STEP_TAC modulo mk_discard2[30]*)
(*    -> DISCARD_STALE_Q30_TAC, and STOPPING before the 0x42c branch (no <=8  *)
(*    INT_SUB_REFL / WORD_RULE collapse, since X5 != in_p here).              *)
(*  - the 0x42c b.ge (step 260) FALLS THROUGH via WB_LOOPENTER_FLAGS; then    *)
(*    bulk-8 segment 261..287; the 0x49c b.ge (step 288) FALLS THROUGH to     *)
(*    the loop head via WB_PTRCMP_FLAGS + D_GT_128.                           *)
(*                                                                            *)
(* Route A (as wb.ml WB_FRONT_BUF): the 8 in-flight keystream towers cannot   *)
(* be hand-written and the printed s288 term does not reparse, so we run the  *)
(* front once against a MINIMAL postcond, harvest the s288 assumptions with   *)
(* build_state_postcond_tms2 (folded to aes13 + gcm_ctr_inc^k lanes by        *)
(* wb_front_fold_tac), then prove.  The front therefore sims twice per cold   *)
(* load (once to harvest, once in the proof) -- the checkpoint hides this for *)
(* interactive work.                                                          *)
(* ------------------------------------------------------------------------- *)

(* nblk>8 front hypotheses: swap the (1<=nblk /\ nblk<=8) prefix of wb.ml's
   wb_front_hyps_tm for the nblk>=17 regime, KEEP every nonoverlapping/aligned/
   length conjunct. *)
let wbn_front_hyps_tm =
  let _,rest1 = dest_conj wb_front_hyps_tm in
  let _,rest = dest_conj rest1 in
  mk_conj(`17 <= nblk /\ 128 * nblk < 2 EXP 62 /\ val (in_p:int64) + 16 * nblk < 2 EXP 63`,
          rest);;

let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;

(* pure-arith closer for the nblk>=17 side conditions *)
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* nblk>8 buffer prep: same shape as wb.ml WB_FRONT_PREP_BUF_TAC but with the
   _ANY rungs and the nblk>=17 arithmetic for the block-0 lane. *)
let WBN_FRONT_PREP_BUF_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_TAC; ALL_TAC];;

(* input lanes 0..7 for the bulk-8 ldp at 0x430 *)
let WBN_LANES_TAC =
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s0 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

let wbn_init_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_TAC;;

(* keep only the latest read Q30 fact (the rev32 counter accumulator grows a
   big tower each step; older ones are dead) *)
let state_num_of_read_q30 th =
  let c = concl th in
  try (match lhs c with
       | Comb(Comb(Const("read",_),q),st) when string_of_term q = "Q30" ->
           let s = fst(dest_var st) in
           if String.length s > 1 && s.[0] = 's'
           then int_of_string (String.sub s 1 (String.length s - 1)) else (-1)
       | _ -> (-1))
  with _ -> (-1);;
let DISCARD_STALE_Q30_TAC : tactic = fun (asl,w) ->
  let nums = List.filter (fun n -> n >= 0)
    (List.map (fun (_,th) -> state_num_of_read_q30 th) asl) in
  if nums = [] then ALL_TAC (asl,w) else
  let mx = itlist max nums (-1) in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let n = state_num_of_read_q30 th in n >= 0 && n < mx) (asl,w);;

(* front steps 1..259 (up to but NOT including the 0x42c branch at step 260) *)
let WBN_FRONT_STEP_TAC =
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--5) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--84) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (85--173) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (174--177) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (178--189) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (190--254) THEN
  DISCARD_STALE_Q30_TAC THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [255] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (256--259);;

(* 0x42c b.ge (step 260): nblk>=17 => X0=in_p, X5=in_p+d, NF=T VF=F, FALLS THRU *)
let WBN_RESOLVE_42C_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* 0x49c b.ge (step 288): X0=in_p+128, X5=in_p+d, 128<d for nblk>=17 => NF=T
   VF=F, FALLS THROUGH to loop head 0x4a0 *)
let WBN_RESOLVE_49C_TAC : tactic = fun (asl,w) ->
  (MP_TAC(SPECL [`in_p:int64`; `128`; `128 * (nblk - 1) DIV 8`] WB_PTRCMP_FLAGS) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_TAC;
       MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
       MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN NBLK_ARITH_TAC];
     ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   MP_TAC(SPEC `nblk:num` D_GT_128) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) (asl,w);;

(* the complete front sim entry 0x20 -> loop head 0x4a0 (ends at s288) *)
let WBN_FRONT_FULL_TAC =
  wbn_init_tac THEN WBN_LANES_TAC THEN WBN_FRONT_STEP_TAC THEN
  WBN_RESOLVE_42C_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (260--260) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (261--287)) THEN
  WBN_RESOLVE_49C_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (288--288);;

(* Harvest the s288 postcondition (the i=0 invariant), then prove WBN_FRONT_BUF.
   The harvest runs the front against a minimal postcond; wb_front_fold_tac
   compacts the 8 keystream towers to aes13 + gcm_ctr_inc^k lanes.  Reuses
   wb.ml's build_state_postcond_tms2 (keeps every read _ s288 fact + the
   aligned_bytes_loaded conjunct). *)
let wbn_front_postcond_i0 =
  let min_goal = mk_wbn_front_goal `\s:armstate. read PC s = word (pc + 0x4a0)` in
  let _ = g min_goal in
  let _ = e (WBN_FRONT_FULL_TAC THEN wb_front_fold_tac) in
  let (asl288,_) = top_goal() in
  let pc = build_state_postcond_tms2 "s288" asl288 in
  let _ = b() in pc;;

(* WBN_FRONT_BUF: the FRONT-N theorem.  Its postcond = the i=0 loop invariant
   (two-stream pipelined form): q8..q15 = RAW ct blocks 0..7 pending fold,
   Q19 = word_bytereverse xi (GHASH acc over blocks 0..-1 = tag only), stores
   done for blocks 0..7, counters at 8..12, X0=in_p+128, X2=out_p+128.
   Close = WB_FRONT_BUF's, plus one REWRITE_TAC[WORD_ADD_0] (the harvested Q30
   lower lanes carry a spurious word_add _ (word 0) vs the sim's assumption). *)
let WBN_FRONT_BUF = prove(mk_wbn_front_goal wbn_front_postcond_i0,
  WBN_FRONT_FULL_TAC THEN wb_front_fold_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* 4. Phase 2: the TWO-STREAM ENSURES_WHILE loop invariant (FROZEN).          *)
(*                                                                            *)
(* Derived (session-003) by generalizing WBN_FRONT_BUF's harvested s288       *)
(* postcond to symbolic block index i.  The i=0 instance was VALIDATED to     *)
(* follow from WBN_FRONT_BUF: 44 of 47 conjuncts (all registers, counters,    *)
(* keystreams, GHASH acc, stores, pointers) close by                          *)
(*   CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN                                  *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN                *)
(*   REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] *)
(*     THEN REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN             *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES;..;GCM_CTR_INC7_LANES])    *)
(*     THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN         *)
(*   REWRITE_TAC[GCM_CTR_ADD_0] THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_   *)
(*     CONV) THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN                     *)
(*   REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[].                          *)
(*                                                                            *)
(* GAP (documented, sound): the remaining 3 conjuncts                         *)
(*   read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes       *)
(*   read (memory :> bytes128 key_p) s = k0                                   *)
(*   htable_mem_dec h htbl_p s                                                *)
(* are loop-CONSTANTS that hold at the loop head (they are in wb_front_pre_tm *)
(* and NOT in the front MAYCHANGE frame -> preserved) but are NOT in          *)
(* WBN_FRONT_BUF's harvested postcond (build_state_postcond_tms2 keeps only   *)
(* `read _ s = _` + aligned_bytes_loaded, so htable_mem_dec is dropped, and   *)
(* the in_p/key_p reads were s0 facts not re-stated at s288).  FIX for next   *)
(* session: extend the front postcond harvest to re-assert these 3 (add them  *)
(* to wbn_front_postcond_i0 / the keep-filter, OR carry them via a strengthen *)
(* step), then WBN_FRONT_BUF closes them from the precond (they are in the    *)
(* MAYCHANGE-preserved set).  With that, the ENSURES_WHILE_UP_TAC entry       *)
(* subgoal (i=0) closes by MATCH_MP_TAC WBN_FRONT_BUF + the tactic above.     *)
(*                                                                            *)
(* Two-stream reading of the invariant (VERIFIED off the i=0 goal):           *)
(*  - store/counter stream AHEAD at 8(i+1): X0=in_p+128(i+1), X2=out_p+128(i+1)*)
(*    Q0..Q4 = gcm_ctr_add (word (8i+8..12)) ctr0 (next group's counters),    *)
(*    Q5..Q7 = plaintext blocks at 8i+5..7 (in-flight keystream XOR),         *)
(*    stores done for all j < 8(i+1).                                         *)
(*  - GHASH stream LAGS at 8i: Q19 = ghash_polyval_acc (byteswap128 h)        *)
(*    (word_bytereverse xi) over reversed raw ct blocks 0..8i-1;              *)
(*    q8..q15 = RAW ct blocks 8i..8i+7 pending fold (the bridge).             *)
(*                                                                            *)
(* STEP-CASE TODO (Phase 4, plan-rationale risk #2): the +8*i offset on the   *)
(* Q5..Q7 keystream indices (5,6,7 at i=0, all < 8) must be READ OFF the      *)
(* loop-body sim goal, not trusted from this generalization.                  *)
(* loop control flow (objdump): head pc1=pc+0x4a0; back-edge cmp x0,x5 @0x9e4 *)
(* + b.lt 0x4a0 @0x9ec (SIGNED, so a P-variant / WB_PTRCMP_FLAGS handles it); *)
(* exit fall-through @0x9f0.  count q = (nblk-9) DIV 8.                        *)
(* ------------------------------------------------------------------------- *)

let wbn_loop_invariant = new_definition
 `wbn_loop_invariant (pc:num) (ctr0:int128) (in_p:int64) (out_p:int64)
    (xi_p:int64) (ivec_p:int64) (key_p:int64) (htbl_p:int64) (stackpointer:int64)
    (nblk:num) (ibytes:byte list) (xi:int128) (h:int128)
    (k0:int128) k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 (k14:int128) =
  \(i:num) (s:armstate).
    aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
    read PC s = word (pc + 1184) /\
    read Q0 s = gcm_ctr_add (word (8 * i + 8)) ctr0 /\
    read Q1 s = gcm_ctr_add (word (8 * i + 9)) ctr0 /\
    read Q2 s = gcm_ctr_add (word (8 * i + 10)) ctr0 /\
    read Q3 s = gcm_ctr_add (word (8 * i + 11)) ctr0 /\
    read Q4 s = gcm_ctr_add (word (8 * i + 12)) ctr0 /\
    read Q5 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 5) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q6 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 6) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q7 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 7) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q8 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 0),16) ibytes) /\
    read Q9 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 1),16) ibytes) /\
    read Q10 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 2),16) ibytes) /\
    read Q11 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 3),16) ibytes) /\
    read Q12 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 4),16) ibytes) /\
    read Q13 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes) /\
    read Q14 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes) /\
    read Q15 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes) /\
    read Q19 s =
    ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * i))) /\
    read Q26 s = k12 /\
    read Q27 s = k13 /\
    read Q28 s = k14 /\
    read X0 s = word_add in_p (word (128 * (i + 1))) /\
    read X2 s = word_add out_p (word (128 * (i + 1))) /\
    read X4 s = word_add in_p (word (16 * nblk)) /\
    read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p /\
    read X9 s = word (16 * nblk) /\
    read X10 s = word_add stackpointer (word 64) /\
    read X1 s = word (128 * nblk) /\
    read X15 s = word 4294967296 /\
    read Q31 s = word 79228162514264337593543950336 /\
    read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0 /\
    read X16 s = ivec_p /\
    read X6 s = htbl_p /\
    read X3 s = xi_p /\
    read X11 s = key_p /\
    read SP s = stackpointer /\
    (!j. j < 8 * (i + 1)
         ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
             word_xor
             (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
             (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
              k10 k11 k12 k13)) k14) /\
    read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes /\
    read (memory :> bytes128 key_p) s = k0 /\
    htable_mem_dec h htbl_p s`;;

(* ---- Entry-subgoal recipe (validated interactively, session-003) ----------
   The ENSURES_WHILE_UP_TAC entry subgoal is  pre ==> (PC=pc1 /\ inv 0 s).
   Given WBN_FRONT_BUF establishes pre ==> (PC=pc+0x4a0 /\ <postcond s>), the
   i=0 invariant  (wbn_loop_invariant ... 0 s)  follows from <postcond s> PLUS
   the 3 loop-constants (in_p read-only, key_p=k0, htable_mem_dec) once those
   are added to WBN_FRONT_BUF's harvest.  The closing tactic (proves 44/47
   directly from the postcond hyps; the 3 come from the extended front):

     GEN_TAC THEN REWRITE_TAC[wbn_loop_invariant] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
     REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
     REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
        GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
        GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
     REWRITE_TAC[GCM_CTR_ADD_0] THEN
     CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]

   With the RAW WBN_FRONT_BUF postcond as the assumption set this reduces the
   goal to EXACTLY the 3 loop-constant conjuncts (confirmed session-003).  When
   packaging as a standalone lemma with the postcond as a `\s.`-abstraction
   antecedent, watch the beta step: STRIP_TAC must see the antecedent already
   beta-reduced (do CONV_TAC(TOP_DEPTH_CONV BETA_CONV) on the WHOLE goal, incl.
   the antecedent, before STRIP_TAC) — a naive `(\s.P) s /\ (\s.Q) s ==> ...`
   left unreduced makes STRIP_TAC give conjunct hyps still wrapped.

   NEXT-SESSION FIX to get a clean entry (no extra hyps):
   extend WBN_FRONT_BUF so its postcond re-asserts the 3 loop-constants.  Either
   (a) widen build_state_postcond_tms2's keep-filter to also retain
       `htable_mem_dec _ _ s` and the input/key `read _ s = _` facts (they are
       preserved: NOT in wb_front_frame_tm's MAYCHANGE), re-run the front sim,
       or (b) prove WBN_FRONT_BUF_EXT = WBN_FRONT_BUF strengthened with the 3
       (they hold in wb_front_pre_tm and survive the frame), via a framing/
       ENSURES_TRANS wrapper avoiding a full re-sim.  Then the entry subgoal of
       ENSURES_WHILE_UP_TAC closes by MATCH_MP_TAC WBN_FRONT_BUF_EXT + the tactic
       above (no leftover conjuncts). *)

(* ------------------------------------------------------------------------- *)
(* 5. Phase 3: GHASH 8-block extension algebra (pure list/field, no sim).     *)
(*                                                                            *)
(* The invariant's Q19 GHASH accumulator is                                   *)
(*   ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)                  *)
(*     (MAP word_bytereverse (list_of_seq blk (8 * i)))                       *)
(* where blk k = bytes_to_int128 (SUB_LIST (16*k,16) ibytes) is the raw ct    *)
(* block k.  The step case (i -> i+1) must extend this fold from 8*i to       *)
(* 8*(i+1) blocks.  The loop body performs exactly 8 Horner steps (one        *)
(* polyval_dot per fresh ciphertext block, each byte-reversed then XORed into *)
(* the accumulator), so we need the fold over 8*(i+1) blocks to equal the     *)
(* fold over 8*i blocks continued by 8 explicit steps over blocks            *)
(* 8*i .. 8*i+7.  This is pure algebra over GHASH_ACC_APPEND                   *)
(* (common/polyval_ghash.ml:62) + list_of_seq, provable BEFORE any sim.       *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any offset (APPEND-at-end recursion, induct on n) *)
let LIST_OF_SEQ_SPLIT = prove
 (`!(f:num->int128) m n. list_of_seq f (m + n) =
     APPEND (list_of_seq f m) (list_of_seq (\j. f (m + j)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_ASSOC]);;

(* generic group-extension of the byte-reversed GHASH fold: split m+n *)
let GHASH_ACC_GROUP_EXTEND = prove
 (`!(g:num->int128) H acc m n.
    ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g (m + n))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g m)))
      (MAP word_bytereverse (list_of_seq (\j. g (m + j)) n))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_SPLIT; MAP_APPEND; GHASH_ACC_APPEND]);;

(* clean 8-element unfold of list_of_seq (numerals, no SUC towers) *)
let LIST_OF_SEQ_8 = prove
 (`!f:num->int128. list_of_seq f 8 =
    [f 0; f 1; f 2; f 3; f 4; f 5; f 6; f 7]`,
  GEN_TAC THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[num_CONV `8`; num_CONV `7`; num_CONV `6`;
    num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`;
    LIST_OF_SEQ])) THEN
  REWRITE_TAC[o_THM] THEN CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN REWRITE_TAC[]);;

(* THE Phase-3 deliverable: extend the invariant's GHASH fold by one 8-block  *)
(* group.  RHS = the 8*i fold, continued by a fold over the 8 concrete new    *)
(* raw-ct blocks (8*i .. 8*i+7).  Instantiate blk := \k. bytes_to_int128      *)
(* (SUB_LIST (16*k,16) ibytes) in the body; REWRITE_TAC[MAP; ghash_polyval_acc]*)
(* then unfolds the RHS to the nested polyval_dot/word_xor Horner chain the    *)
(* 8 body GHASH instructions produce. *)
let GHASH_ACC_8BLOCK_EXTEND = prove
 (`!(blk:num->int128) H acc i.
    ghash_polyval_acc H acc
      (MAP word_bytereverse (list_of_seq blk (8 * (i + 1)))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq blk (8 * i))))
      (MAP word_bytereverse
        [blk (8 * i); blk (8 * i + 1); blk (8 * i + 2); blk (8 * i + 3);
         blk (8 * i + 4); blk (8 * i + 5); blk (8 * i + 6); blk (8 * i + 7)])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `8 * (i + 1) = 8 * i + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GHASH_ACC_GROUP_EXTEND] THEN
  REWRITE_TAC[LIST_OF_SEQ_8] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* 6. Route-(b) tool: strengthen an ensures postcondition with a frame-       *)
(*    PRESERVED fact, with NO re-simulation.  Pure ensures/eventually logic.  *)
(*                                                                            *)
(* This is the clean combinator for WBN_FRONT_BUF_EXT (and reusable in the    *)
(* Phase-6 recompose): given `ensures step P Q C` and that the frame C, from  *)
(* precondition P, preserves R (i.e. !s s'. P s /\ C s s' ==> R s'), we get   *)
(* `ensures step P (\s. Q s /\ R s) C` for free.                              *)
(*                                                                            *)
(* Usage for WBN_FRONT_BUF_EXT: take R s = (the 3 loop-constants at s:         *)
(*   read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes /\      *)
(*   read (memory :> bytes128 key_p) s = k0 /\ htable_mem_dec h htbl_p s).     *)
(* The preservation obligation !s s'. wb_front_pre_tm s /\ wb_front_frame_tm  *)
(* s s' ==> R s' holds because none of in_p's input bytes, key_p, or htbl_p   *)
(* memory is in wb_front_frame_tm's MAYCHANGE (only out_p/xi_p/ivec_p/stack + *)
(* Q-regs are).  Discharge it by: STRIP the frame (MAYCHANGE ... ,, ...),     *)
(* then for each read-conjunct use the nonoverlapping hyps + the fact the     *)
(* frame's memory writes miss those regions (the standard READ_OVER_WRITE /   *)
(* MAYCHANGE-preservation reasoning; htable_mem_dec unfolds to bytes128 reads *)
(* off htbl_p that are likewise disjoint).                                    *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ADD_PRESERVED = prove
 (`!(step:A->A->bool) P Q R C.
    ensures step P Q C /\ (!s s'. P s /\ C s s' ==> R s')
    ==> ensures step P (\s. Q s /\ R s) C`,
  REWRITE_TAC[ensures] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s0:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s':A. Q s' /\ C (s0:A) s' ==> (Q s' /\ R s') /\ C s0 s'`
    (MP_TAC o MATCH_MP EVENTUALLY_MONO) THENL
   [X_GEN_TAC `s1:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`s0:A`;`s1:A`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    DISCH_THEN(MP_TAC o SPECL [`step:A->A->bool`; `s0:A`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. Phase 2 hyp-gap fix: WBN_FRONT_BUF_EXT (session-005).                   *)
(*                                                                            *)
(* The i=0 invariant instance needs 3 loop-CONSTANTS at the loop head that    *)
(* WBN_FRONT_BUF's harvested postcond drops (session-003/004 GAP note above): *)
(*   read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes         *)
(*   read (memory :> bytes128 key_p) s = k0                                   *)
(*   htable_mem_dec h htbl_p s                                                *)
(* These are preserved by the front MAYCHANGE frame (which writes only        *)
(* out_p/xi_p/ivec_p/stack + Q-regs), PROVIDED out_p is disjoint from in_p/   *)
(* key_p/htbl_p.  wbn_front_hyps_tm was missing exactly those 3 out_p         *)
(* disjointness conjuncts (they ARE in wb.ml's <=8 band hyps, wb.ml:3854-57). *)
(*                                                                            *)
(* ROUTE (b) (session-004's ENSURES_ADD_PRESERVED), NOT route (a): we DON'T   *)
(* re-run the front sim with widened hyps (the build_state_postcond_tms2      *)
(* re-harvest the reviewer flagged as risky).  Instead keep the proven        *)
(* WBN_FRONT_BUF verbatim and STRENGTHEN its postcond with the 3 constants    *)
(* via ENSURES_ADD_PRESERVED: leg1 = WBN_FRONT_BUF (narrow hyps <= wide hyps, *)
(* closed by MATCH_MP_TAC + ASM_REWRITE), leg2 = the pure frame-preservation  *)
(* obligation (no sim).  Whole thing proves in ~4s.                           *)
(* ------------------------------------------------------------------------- *)

(* widened front hyps = wbn_front_hyps_tm + the 3 out_p disjointness conjuncts *)
let wbn_front_hyps_wide_tm =
  mk_conj(wbn_front_hyps_tm,
    `nonoverlapping (out_p:int64,16 * nblk) (in_p:int64,16 * nblk) /\
     nonoverlapping (out_p:int64,16 * nblk) (key_p:int64,240) /\
     nonoverlapping (out_p:int64,16 * nblk) (htbl_p:int64,192)`);;

(* the WBN_FRONT_BUF pieces (P = precond, Q0 = harvested postcond, C = frame) *)
let wbn_front_P_tm, wbn_front_Q0_tm, wbn_front_C_tm =
  let ens = snd(dest_imp(snd(strip_forall(concl WBN_FRONT_BUF)))) in
  rand(rator(rator ens)), rand(rator ens), rand ens;;

(* R = the 3 loop-constants, taken verbatim from WBN_FRONT_BUF's precond so
   they match wbn_loop_invariant's conjuncts syntactically. *)
let wbn_front_R_tm =
  let sv = fst(dest_abs wbn_front_P_tm) in
  mk_abs(sv, list_mk_conj
    [`read (memory :> bytes (in_p:int64,16 * nblk)) s = num_of_bytelist ibytes`;
     `read (memory :> bytes128 (key_p:int64)) s = (k0:int128)`;
     `htable_mem_dec h (htbl_p:int64) s`]);;

(* EXT goal: wide hyps ==> ensures arm P (\s. Q0 s /\ R s) C *)
let wbn_front_ext_goal =
  let newQ = mk_abs(fst(dest_abs wbn_front_P_tm),
    mk_conj(rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,fst(dest_abs wbn_front_P_tm))))),
            rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,fst(dest_abs wbn_front_P_tm))))))) in
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; newQ; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* leg2 helper: push a read through the whole MAYCHANGE write-chain to `read c s`
   using the goal's nonoverlapping assumptions (memory-vs-memory orthogonality),
   then close via the precond assumption `read c s = value`.  Uses the
   assumption-aware COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV (common/components).
   Applied once per R-conjunct (register writes fold away, memory writes need the
   nonoverlapping facts). *)
let WBN_PUSH_LHS_READ_TAC : tactic =
  W(fun (asl,w) ->
    let thl = map snd asl in
    let cxt = (NONOVERLAPPING_DRIVERS thl, FILTER_CANONIZE_ASSUMPTIONS thl) in
    CONV_TAC(LAND_CONV(COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV cxt))) THEN
  ASM_REWRITE_TAC[];;

let WBN_FRONT_BUF_EXT = prove(wbn_front_ext_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_BUF THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[htable_mem_dec] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
    WBN_PUSH_LHS_READ_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 8. Phase 2 CLOSE: WBN_LOOP_INVARIANT_ENTRY (session-005).                  *)
(*                                                                            *)
(* THE entry subgoal that ENSURES_WHILE_UP_TAC produces for the main loop:    *)
(*   ensures arm (\s. decodes /\ PC = pc+0x20 /\ precondition s)              *)
(*               (\s. decodes /\ PC = pc+0x4a0 /\ wbn_loop_invariant ... 0 s) *)
(*               frame                                                        *)
(* i.e. the front (entry -> loop head) establishes the i=0 invariant.  Proved *)
(* by weakening WBN_FRONT_BUF_EXT's postcond (Q0 /\ 3-loop-constants) down to *)
(* the i=0 invariant, via ENSURES_POSTCONDITION_THM.  The implication         *)
(* (Q0 s /\ R s) ==> inv 0 s is the session-003 Sec-4 closing recipe, PLUS a  *)
(* final numeral-normalization pass (session-005): after the recipe the goal  *)
(* is a conjunction of trivial `f (word n) = f (word (0+n))` /                 *)
(* `SUB_LIST(16*(0+k)..) = SUB_LIST(16*k..)` equalities + the j<8 store        *)
(* forall; ADD_CLAUSES + NUM_MULT_CONV + GCM_CTR_ADD_0 (block-0 = ctr0) close  *)
(* them against the postcond hyps.                                            *)
(* ------------------------------------------------------------------------- *)

(* i=0 invariant applied to all 27 loop params, as a (num->armstate->bool). *)
let wbn_inv_applied =
  list_mk_comb(`wbn_loop_invariant`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
     `k12:int128`;`k13:int128`;`k14:int128`]);;

(* post = \s. decodes /\ PC = pc+0x4a0 /\ inv 0 s *)
let wbn_entry_post =
  subst [wbn_inv_applied,`INVAPP:num->armstate->bool`]
    `\s:armstate. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
                  read PC s = word (pc + 0x4a0) /\
                  INVAPP (0:num) s`;;

let wbn_entry_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* the Q to weaken from: WBN_FRONT_BUF_EXT's postcond = \s. Q0 s /\ R s *)
let wbn_extQ =
  let sv = fst(dest_abs wbn_front_P_tm) in
  mk_abs(sv, mk_conj(
    rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,sv)))),
    rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,sv)))))) ;;

let WBN_LOOP_INVARIANT_ENTRY = prove(wbn_entry_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC wbn_extQ THEN CONJ_TAC THENL
   [(* (Q0 x /\ R x) ==> decodes /\ PC=pc+0x4a0 /\ inv 0 x *)
    GEN_TAC THEN REWRITE_TAC[wbn_loop_invariant] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
    REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
    REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
       GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
       GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
    REWRITE_TAC[GCM_CTR_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
    (* session-005 numeral-normalization tail: 0+n, 16*(0+k), block-0=ctr0 *)
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_LANES; GCM_CTR_ADD_0] THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[GCM_CTR_ADD_0] THEN
    (* session-008 Q30 residual: the only conjunct the session-005 closer leaves
       open after the Q30 patch.  The i=0 raw tower (top lane += 12 then += 1)
       collapses to gcm_ctr_raw (word 13) ctr0 = the invariant's 8*0+13 value.
       VALIDATED (session-008, shadow wbn_loop_invariant_v2). *)
    REWRITE_TAC[gcm_ctr_raw_def;
      WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
                 word_add x (word 13)`;
      WORD_ADD_0];
    (* the ensures = WBN_FRONT_BUF_EXT *)
    MATCH_MP_TAC WBN_FRONT_BUF_EXT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. Phase 4 launch: PC/decode-free CORE invariant + split (session-006).    *)
(*                                                                            *)
(* wbn_loop_invariant bakes in two conjuncts the ENSURES_WHILE tactics MUST   *)
(* own themselves:                                                            *)
(*   C1  aligned_bytes_loaded s (word pc) ...mc   (program_decodes)           *)
(*   C2  read PC s = word (pc + 1184)             (the loop-head PC)          *)
(* Every ENSURES_WHILE_* template threads `program_decodes` and `read PC =    *)
(* word pcX` around its OWN `loopinv i s`, applying loopinv at BOTH pc1 (head)*)
(* and pc2 (back-edge/exit).  A PC baked into the invariant is therefore      *)
(* redundant at pc1 and *contradictory* at pc2 (it would force PC=0x4a0 in a  *)
(* state whose PC is 0x9ec/0x9f0).  Standard s2n invariants (keccak,          *)
(* emontredc) are PC/decode-free for exactly this reason.                     *)
(*                                                                            *)
(* wbn_loop_inv_core = wbn_loop_invariant with C1,C2 removed (built by        *)
(* dropping the first two conjuncts, so it stays in sync with the frozen      *)
(* definition automatically).  WBN_INV_SPLIT is the bridge                    *)
(*   wbn_loop_invariant ... i s <=>                                           *)
(*     aligned_bytes_loaded s (word pc) mc /\ read PC s = word (pc+1184) /\   *)
(*     wbn_loop_inv_core ... i s                                              *)
(* so the ENTRY theorem (which yields the LHS at i=0) feeds any tactic that   *)
(* wants the RHS, and the loop body/exit can carry ONLY the core across the   *)
(* frame while the tactic supplies decode+PC.                                 *)
(* ------------------------------------------------------------------------- *)

let wbn_loop_inv_core =
  let eqn = snd(strip_forall(concl wbn_loop_invariant)) in
  let lhs_full, rhs_full = dest_eq eqn in
  let hd, params = strip_comb lhs_full in
  let ivars, body = strip_abs rhs_full in
  let cs = conjuncts body in
  (* C1 = aligned_bytes_loaded, C2 = read PC = word(pc+1184); drop both *)
  let core_body = list_mk_conj (List.tl (List.tl cs)) in
  let core_rhs = list_mk_abs(ivars, core_body) in
  let newhead = mk_var("wbn_loop_inv_core", type_of hd) in
  new_definition (mk_eq(list_mk_comb(newhead, params), core_rhs));;

let wbn_inv_args =
  snd(strip_comb(fst(dest_eq(snd(strip_forall(concl wbn_loop_invariant))))));;

let WBN_INV_SPLIT = prove
 (list_mk_forall(wbn_inv_args @ [`i:num`;`s:armstate`],
    mk_eq(
      list_mk_comb(`wbn_loop_invariant`, wbn_inv_args @ [`i:num`;`s:armstate`]),
      list_mk_conj[
        `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
        `read PC s = word (pc + 1184)`;
        list_mk_comb(`wbn_loop_inv_core`, wbn_inv_args @ [`i:num`;`s:armstate`])])),
  REWRITE_TAC[wbn_loop_invariant; wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* 9b. Phase 4 PREREQ: the RAW counter accumulator Q30 (session-007).          *)
(*                                                                            *)
(* CRITICAL FINDING (session-007): the frozen wbn_loop_invariant (Sec 4) is    *)
(* INCOMPLETE for the loop body.  The body's FIRST instruction                 *)
(*   0x4a0  rev32 v5, v30                                                       *)
(* reads Q30 -- the running CTR-block counter in its rev32-pending "raw" form  *)
(* -- but wbn_loop_invariant has NO Q30 conjunct, so Q5 immediately goes       *)
(* symbolic in `read Q30 s0` and the body cannot close.  Static live-in        *)
(* analysis of the whole body (0x4a0..0x9ec) shows Q30 is the ONLY vector      *)
(* register whose first use is a READ and which the invariant fails to pin     *)
(* (Q0..Q4, Q19, Q31 are live-in AND already pinned).                          *)
(*                                                                            *)
(* WBN_FRONT_BUF DID harvest a Q30 conjunct (its postcond conjunct 46), as a   *)
(* raw bit-tower; Sec 4's generalization to symbolic i simply dropped it.      *)
(* The value at the loop head (iteration i) is gcm_ctr_raw (word (8*i+13)) ctr0*)
(* -- CONFIRMED: WBN_FRONT_BUF's conjunct-46 term = gcm_ctr_raw (word 13) ctr0 *)
(* at i=0 (proved via gcm_ctr_raw_def + WORD_RULE add-merge + WORD_ADD_0).      *)
(*                                                                            *)
(* gcm_ctr_raw w ctr0 is the counter in the "byte-grouped, top-lane += w"      *)
(* representation the hardware keeps in v30: its top 32-bit lane is            *)
(* word_add (<brev of ctr0[96:128] bytes>) w, the low 96 bits are ctr0's low   *)
(* lanes byte-grouped.  The body does rev32(v30) -> AES keystream input for    *)
(* block 8i+13, then add v30,v30,v31 (v31 = word 2^96) to advance to 8i+14.    *)
(*                                                                            *)
(* THE FIX (next session): add a Q30 conjunct                                  *)
(*   read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0                          *)
(* to wbn_loop_invariant (and thus wbn_loop_inv_core auto-tracks it).  Then     *)
(* WBN_FRONT_BUF_EXT / WBN_LOOP_INVARIANT_ENTRY must re-establish it at i=0     *)
(* (from conjunct 46 via the gcm_ctr_raw (word 13) identity), and the step     *)
(* case advances it 8i+13 -> 8(i+1)+13 = 8i+21 over the 8 in-body increments.  *)
(* ------------------------------------------------------------------------- *)

(* gcm_ctr_raw_def moved to Sec 2 (session-008): the Sec-4 invariant now pins
   Q30 = gcm_ctr_raw (word (8*i+13)) ctr0, so the definition must precede Sec 4.
   Its body-only algebra lemmas remain here. *)

(* the 4 lane-extraction lemmas (used to prove GCM_CTR_RAW_INCR without a
   symbolic-w WORD_BLAST, which OOMs -- see Sec 2 AVOID note).  Each proves fast
   via WORD_SIMPLE_SUBWORD_CONV (extracts the lane) then WORD_BLAST (w appears
   only additively in the top lane, the addend never enters the BDD). *)
let SUBW_RAW_96 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (96,32):32 word =
   word_add (word_join (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
     (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word) w`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_64 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (64,32):32 word =
   word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
     (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_32 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (32,32):32 word =
   word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
     (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_0 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (0,32):32 word =
   word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
     (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;

(* the increment: `add v30.4s,v30.4s,v31.4s` (v31 = word 2^96) is a lane-wise
   32-bit add; the model emits it as word_join of word_add(word_subword v30 lane)(word c)
   with c=1 on the top lane, 0 elsewhere.  This advances the raw counter by 1. *)
let GCM_CTR_RAW_INCR = prove
 (`word_join
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (96,32):32 word) (word 1))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (64,32):32 word) (word 0)):64 word)
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (32,32):32 word) (word 0))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (0,32):32 word) (word 0)):64 word):int128 =
    gcm_ctr_raw (word_add w (word 1)) ctr0`,
  REWRITE_TAC[SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0; WORD_ADD_0] THEN
  GEN_REWRITE_TAC RAND_CONV [gcm_ctr_raw_def] THEN
  REWRITE_TAC[WORD_RULE
    `!(x:32 word) w. word_add (word_add x w) (word 1) = word_add x (word_add w (word 1))`]);;

(* REV32 fold: `rev32 v_,v30` (esize=32) applied to gcm_ctr_raw w ctr0 yields
   gcm_ctr_add w ctr0 -- the proper AES keystream input for CTR block w.  The
   arm_REV32_VEC tower is auto-generated by the stepper (~8k chars, deterministic),
   so the reusable form is a TACTIC that folds `read Qd sN` after a rev32-of-v30 step.
   VALIDATED recipe (session-007, proves in ~2s):
     <capture the rev32 tower T = rhs of `read Qd sN`>, then prove `T = gcm_ctr_add w ctr0` by
       REWRITE_TAC[gcm_ctr_raw_def] THEN
       GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
       <SPEC_TAC the `word_add <topbytes> w` atom to a fresh 32-word> THEN
       GEN_TAC THEN CONV_TAC WORD_BLAST
   CRUCIAL: unfold gcm_ctr_raw EVERYWHERE (plain REWRITE_TAC[gcm_ctr_raw_def], NOT ONCE_DEPTH)
   and unfold the RHS via GCM_CTR_ADD_LANES so BOTH sides carry only the shared symbolic-add
   atom; THEN SPEC_TAC that atom away before WORD_BLAST (WORD_BLAST on a live symbolic
   `word_add _ w` OOMs -- see Sec 2 AVOID).  The GCM_SIMD_SIMPLIFY_TAC used per body step may
   already collapse part of the rev32 tower; adapt the captured-tower shape accordingly.

   REV32_FOLD_TAC qd sn wtm: rewrite the assumption `read qd sn = <rev32 tower>` so its
   rhs becomes `gcm_ctr_add wtm ctr0`.  Proves the fold equation on the fly via the recipe,
   generalizing over wtm so WORD_BLAST never meets the symbolic addend. *)
let REV32_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  fun (asl,gl) ->
    let tower = tryfind (fun (_,th) -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),r)
          when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) -> r
      | _ -> fail()) asl in
    (* generalize wtm -> a fresh w:32 word, prove the fold for symbolic w, then re-specialize *)
    let tower_gen = subst [`w:32 word`, wtm] tower in
    let fold_thm = prove(mk_eq(tower_gen, `gcm_ctr_add w ctr0`),
      REWRITE_TAC[gcm_ctr_raw_def] THEN
      GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
      W(fun (_,gw) ->
         let atom = find_term (fun t -> match t with
           | Comb(Comb(Const("word_add",_),_),Var("w",_)) -> true | _ -> false) gw in
         SPEC_TAC(atom, `aa:32 word`)) THEN
      GEN_TAC THEN CONV_TAC WORD_BLAST) in
    let fold_spec = INST [wtm,`w:32 word`] fold_thm in
    RULE_ASSUM_TAC(REWRITE_RULE[fold_spec]) (asl,gl);;

(* ------------------------------------------------------------------------- *)
(* 10. Phase 4: fire the ENSURES_WHILE skeleton -> WBN_MAIN_LOOP (session-006)*)
(*                                                                            *)
(* The back-edge of .L256_dec_main_loop is                                    *)
(*   cmp x0,x5 @0x9e4 ; stp q6,q7,[x2],#32 @0x9e8 ; b.lt 0x4a0 @0x9ec         *)
(* i.e. the SIGNED conditional branch b.lt is the LAST body instruction and   *)
(* its flag-setting cmp is two instructions earlier -- BOTH inside the body.  *)
(* That is the ENSURES_WHILE_UP2_TAC shape (branch folded into the body): the *)
(* body postcondition PC is word(if i+1<k then pc1 else pc2), the flag never  *)
(* crosses a frame boundary, and the exit lands at the fall-through pc2.       *)
(* Count k = (nblk-9) DIV 8; pc1 = pc+0x4a0 (head); pc2 = pc+0x9f0 (exit).     *)
(*                                                                            *)
(* PROBLEM: ENSURES_WHILE_UP2_TAC's internal `C ,, C = C` conjunct is         *)
(* discharged by MAYCHANGE_IDEMPOT_TAC, which THROWS ASSIGNS_SEQ_ABSORB_CONV  *)
(* on this 4-memory-region frame (the MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_  *)
(* ABI macro doesn't canonicalize into the ASSIGNS sequence ABSORB expects).  *)
(* FIX: expand the ABI macro FIRST, then MAYCHANGE_IDEMPOT_TAC succeeds (~2s). *)
(* up2_pth is a verbatim re-proof of ENSURES_WHILE_UP2_TAC's internal pth, and *)
(* UP2_ABI_TAC is the closure at common/relational.ml:2137 with the ABI       *)
(* expand spliced into the idempotence CONJ_TAC leg.                          *)
(* ------------------------------------------------------------------------- *)

(* the applied PC-free core, as a (num->armstate->bool) and as a \i s. abstr. *)
let wbn_core_applied =
  list_mk_comb(`wbn_loop_inv_core`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
     `k12:int128`;`k13:int128`;`k14:int128`]);;

let wbn_core_iv = list_mk_abs([`i:num`;`s:armstate`],
  mk_comb(mk_comb(wbn_core_applied,`i:num`),`s:armstate`));;

(* ENSURES_WHILE_UP2_TAC's internal `pth` (common/relational.ml:1974), re-proved
   here so we can reach it with an ABI-aware idempotence discharge. *)
let up2_pth = prove(
  `forall k pc1 pc2 (loopinv:num->A->bool) C precond postcond
      (pcounter:(A,(N)word)component) step pc.
    C ,, C = C /\ ~(k = 0) /\
    ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv 0 s)
      C /\
    (forall i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
      ==> ensures step
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv i s)
        (\s. program_decodes s /\
             read pcounter s = word (if i + 1 < k then pc1 else pc2) /\
             loopinv (i + 1) s)
        C) /\
    ensures step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv k s)
        postcond C
    ==>
    ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      postcond C`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "HC HK HPRE HLOOP HPOST" THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  META_EXISTS_TAC THEN CONJ_TAC THENL
  [ALL_TAC; USE_THEN "HPOST" (UNIFY_ACCEPT_TAC [`Q:A->bool`])] THEN
  REMOVE_THEN "HPOST" (K ALL_TAC) THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `(\(s:A). program_decodes s /\
                       read pcounter s = (word pc1:(N)word) /\
                       loopinv (k - 1) s)` THEN
  CONJ_TAC THENL [
    ALL_TAC;
    USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `(k-1)` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]
    THEN REWRITE_TAC[LT_REFL]
  ] THEN
  SUBGOAL_THEN `k - 1 < k` MP_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SPEC_TAC (`k - 1`,`j:num`) THEN INDUCT_TAC THENL [
    ASM_REWRITE_TAC[] THEN NO_TAC;
    FIRST_X_ASSUM (fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN (LABEL_TAC "HPREVLOOP") THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
    META_EXISTS_TAC THEN CONJ_TAC THENL
    [USE_THEN "HPREVLOOP" (UNIFY_ACCEPT_TAC [`Q:A->bool`]); ALL_TAC] THEN
    USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `j:num` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM ADD1] THEN NO_TAC
  ]);;

(* ENSURES_WHILE_UP2_TAC caller with ABI-aware idempotence discharge. *)
let UP2_ABI_TAC k pc1 pc2 iv =
  MATCH_MP_TAC up2_pth THEN
  MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
  BETA_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC];;

(* the LOOP theorem: PC=0x4a0 /\ core 0  ==>  PC=0x9f0 /\ core k, over the front
   MAYCHANGE frame.  Entry/exit are trivial reflexive ensures (pre=post at the
   respective PC); count<>0 is DIVISION arithmetic (17<=nblk => (nblk-9)DIV8>=1).
   Body = the Phase-4 step case, CHEAT_TAC for now (see the big TODO below). *)
let wbn_main_loop_goal =
  let kk = `(nblk - 9) DIV 8` in
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x4a0)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let loop_post = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x9f0)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; loop_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_MAIN_LOOP = prove(wbn_main_loop_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UP2_ABI_TAC `(nblk - 9) DIV 8` `pc + 0x4a0` `pc + 0x9f0` wbn_core_iv THEN
  REPEAT CONJ_TAC THENL
   [ (* 1. count <> 0 : 17<=nblk => (nblk-1) DIV 8 >= 2 > 0 *)
    SUBGOAL_THEN `1 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC;
    (* 2. entry: PC=0x4a0 /\ core 0 -> same (0-step reflexive ensures) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC;
    (* 3. ===================== PHASE 4 LOOP BODY (TODO) ===================== *)
    (* Goal after `REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core] THEN   *)
    (* CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0"`:         *)
    (* state s0 at 0x4a0, iteration i, with (confirmed session-006, risk #2): *)
    (*   X0=in_p+128(i+1) X2=out_p+128(i+1) X4=in_p+16nblk                     *)
    (*   X5=128*((nblk-1)DIV8)+in_p X1=128nblk X9=16nblk X10=sp+64 X11=key_p   *)
    (*   X3=xi_p X6=htbl_p X16=ivec_p X15=word 4294967296 SP=stackpointer      *)
    (*   Q0..Q4 = gcm_ctr_add(8i+8..8i+12) ctr0   (store/counter stream ahead) *)
    (*   Q5,Q6,Q7 = plaintext(8i+5,8i+6,8i+7)     (+8i keystream, CONFIRMED)   *)
    (*   Q8..Q15 = raw ct blocks 8i+0..8i+7        (GHASH stream lags)         *)
    (*   Q19 = ghash_polyval_acc over blocks 0..8i-1                           *)
    (*   Q26=k12 Q27=k13 Q28=k14 Q31=word 79228162514264337593543950336        *)
    (*   Q30 = gcm_ctr_raw (word (8i+13)) ctr0  (session-008 patch; read by     *)
    (*         the body's first instr rev32 v5,v30; advances 8i+13 -> 8i+21).   *)
    (* Sim decodes cleanly (5 steps ~2.5s, session-006).  340 instrs, body     *)
    (* 0x4a0..0x9ec.  Target: core(i+1) at PC=if i+1<k then 0x4a0 else 0x9f0.  *)
    (* GHASH close via GHASH_ACC_8BLOCK_EXTEND (blk := \k. bytes_to_int128     *)
    (* (SUB_LIST(16*k,16) ibytes)).  Counter algebra: GCM_CTR_ADD_COMPOSE /    *)
    (* GCM_CTR_INC_ITER_ADD.  Signed back-edge b.lt @0x9ec resolved inside the *)
    (* body by WB_PTRCMP_FLAGS (x0 vs x5).  Use per-step GCM_SIMD_SIMPLIFY_TAC *)
    (* to control term growth (see WBN_FRONT_STEP_TAC pattern, Sec 3).         *)
    CHEAT_TAC;
    (* 4. exit: PC=0x9f0 /\ core k -> same (0-step reflexive ensures) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;
