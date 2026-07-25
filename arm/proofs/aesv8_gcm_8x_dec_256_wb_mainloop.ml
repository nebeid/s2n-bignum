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
