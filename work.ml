(* ========================================================================= *)
(* WB main-loop (nblk > 8) proof: ENSURES_WHILE invariant, JRH x4 style.     *)
(* Plan: _docs/wb-main-loop-plan.md.  Binary: aesv8_gcm_8x_dec_256_wb.o.     *)
(*                                                                           *)
(* VERIFIED FROM DISASSEMBLY (2026-07-24):                                   *)
(*  - GHASH IS staggered one 8-block group behind AES-CTR/stores, exactly as *)
(*    in encrypt.  Body (0x4a0..0x9ec): rev64+pmull on q8..q15 = ciphertext  *)
(*    group loaded LAST iteration; mid-body ldp q8..q15 loads the next group *)
(*    (raw ciphertext preserved in q8..q15 for next fold), eor3 into v0..v7  *)
(*    = plaintext, stores.  Dec-specific: GHASH input = the LOADED blocks.   *)
(*  - Scalar bound: x9 = 16*nblk (lsr x1,#3 @0x20); x5 = (16*nblk-1) & ~127  *)
(*    (sub @0x4c, and @0x2a0) then x5 += in_p (@0x300); x4 = in_p + 16*nblk  *)
(*    (@0x2fc).  So x5 = in_p + 128*((nblk-1) DIV 8).                        *)
(*  - 0x42c b.ge tail:      taken iff (nblk-1) DIV 8 = 0  iff nblk <= 8.     *)
(*  - 0x49c b.ge prepretail: at x0 = in_p+128; taken iff (nblk-1) DIV 8 <= 1 *)
(*    iff nblk <= 16 (loop body never runs for nblk in 9..16).               *)
(*  - backedge 0x9ec b.lt: body runs q = (nblk-9) DIV 8 times (nblk >= 9);   *)
(*    x0 at loop head after i bodies = in_p + 128*(i+1); exit when           *)
(*    x0 >= x5 = in_p + 128*(q+1).                                           *)
(*  - Both the q=0 path (0x49c b.ge -> 0x9f0) and the loop exit land at      *)
(*    0x9f0 (prepretail) in the SAME invariant(q) state: uniform seam.       *)
(*                                                                           *)
(* INVARIANT (loop head 0x4a0, after i of q body executions), NIST vocab:    *)
(*  - PC = pc+0x4a0; X0 = in_p+128*(i+1); X2 = out_p+128*(i+1);              *)
(*    X4 = in_p+16*nblk; X5 = in_p+128*(q+1); X9, X11 = htbl?/key ptrs.      *)
(*  - v30 counter reg; v0..v4 = rev32 counters 8(i+1)..8(i+1)+4 partially    *)
(*    prepared (v5..v7 completed at body start 0x4a0/0x4a8/...).             *)
(*  - q8..q15 = raw ciphertext blocks 8i..8i+7 (rev64 NOT yet applied).      *)
(*  - v19 = GHASH acc over blocks 0..8i-1 + tag, post-reduction pre-ext      *)
(*    form (front convention Q19_BREVXI: v19 = brev-xi-half-swap shape).     *)
(*  - stores: !j < 8*(i+1). out_p+16j = block j XOR aes256(ctr+j).           *)
(*  - htable_mem_8 / keys / SP frame invariant.                              *)
(*                                                                           *)
(* DELIVERABLE ORDER (plan sec 5):                                           *)
(*  1. scalar rung lemmas (below)                                            *)
(*  2. FRONT-N harvested statement entry(0x20) -> loop head 0x4a0            *)
(*  3. ENSURES_WHILE loop (q iterations) -> invariant(q) @ 0x9f0             *)
(*  4. PREPRETAIL 0x9f0 -> 0xec0 (GHASH fold of last in-flight group)        *)
(*  5. recompose with WB_TAIL_r dispatch (r = nblk - 8*(q+1) in 1..8)        *)
(* ========================================================================= *)

(* needs "arm/proofs/aesv8_gcm_8x_dec_256_wb_nist.ml";; *)

(* minimal deps so this file loads standalone on a fresh checkpoint:
   IVAL_WORD_LT lives in aes_xts_common; gcm_ctr_inc/_iter + LANES in
   gcm_ctr_helpers (both no-ops if wb_nist chain is already loaded) *)
needs "arm/proofs/utils/aes_xts_common.ml";;
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;

(* =========================================================================
   PROGRESS (2026-07-24, session 1):
   - Front-N sim VALIDATED LIVE to s288 = loop head pc+0x4a0 (nblk symbolic,
     hyps: 17 <= nblk, 128*nblk < 2^62, val in_p + 16*nblk < 2^63 [signed
     compare needs no-2^63-straddle], LENGTH ibytes = 16*nblk, band nonovers
     + out_p/in_p out_p/key etc).
   - Steps: wbn_init (prep: SUB_LIST, lane 0, USHR_128NBLK_ANY,
     AND_MASK_16NBLK_ANY) THEN WBN_LANES_TAC (lanes 0..7) THEN
     WBN_FRONT_STEP_TAC (1..259 = WB_FRONT_STEP_TAC modulo: mk_discard2[30]
     -> DISCARD_STALE_Q30_TAC + steps 255..259 straight) THEN
     WB_LOOPENTER_FLAGS rewrite (0x42c b.ge falls through) THEN
     per-step 260..287 with GCM_SIMD_SIMPLIFY_TAC + DISCARD_STALE_Q30_TAC
     [IMPORTANT: raw ARM_STEPS_TAC 260--287 in one block leaves ~57MB
     goalstate; the per-step simplify keeps Q0..Q4 at 1366ch each]
     THEN WBN_RESOLVE_49C_TAC (0x49c b.ge falls through iff 128 <
     128*((nblk-1) DIV 8) ie nblk>=17) THEN step 288 (the b.ge, not taken).
   - s288 state (post GSYM aes13 + GSYM GCM_CTR_INCk_LANES fold):
     PC = pc+1184 (0x4a0); X0 = in_p+128; X2 = out_p+128;
     X4 = in_p + 16*nblk; X5 = word_add (word (128*(nblk-1) DIV 8)) in_p;
     X9 = 16*nblk; X1 = 128*nblk; X3 = xi_p; X6 = htbl_p; X11 = key_p;
     X16 = ivec_p; X10 = sp+64; X15 = word 2^32;
     Q8..Q15 = bytes_to_int128 (SUB_LIST (16k,16) ibytes), k=0..7 (RAW ct);
     Q19 = word_bytereverse xi;  NO Q16/Q17/Q18 facts (GHASH acc = tag only);
     Q0..Q4 = rev32-lane forms of counters 8..12 (1366ch raw, contain
       word 8..word 12 adds);  Q30 = lane-accum form w/ top+13 pending;
     Q5..Q7 = plaintext-5..7 values = DEAD at loop head (overwritten by
       rev32 v5/v6/v7 at body start 0x4a0/0x4b8/0x4d0 before any read
       -> OMIT from invariant);
     out_p stores k=0..7: word_xor (word_xor ct_k (aes13 (inc^k ctr0) ..)) k14;
     Q26/Q27/Q28 = k12/k13/k14; htable/keys/in_p cells unchanged;
     stack slots sp+64 = word 13979173243358019584, sp+72 = 0;
     Q31 = word 79228162514264337593543950336.
   - PIPELINE INDEXING (verified): at loop head after i body executions:
     q8..q15 = ct blocks 8i..8i+7 (pending GHASH), stores = blocks 0..8(i+1)-1,
     GHASH acc (v19) = tag + blocks 0..8i-1, counters v0..v4 = 8(i+1)..8(i+1)+4,
     Q30 top-lane increment = 8(i+1)+5 pending; X0 = in_p + 128(i+1)+... wait
     X0 at head i = in_p + 128*(i+1) (lookahead loads happen mid-body).
     Body i: GHASH q8..q15 (blocks 8i..), ldp new q8..q15 = blocks 8(i+1)..,
     eor3+store plaintexts 8(i+1).., backedge cmp x0,x5.
   - Loop trip count: body executes q = (nblk-1) DIV 8 - 1 times
     (x0: in_p+128(i+1) at head; exits to prepretail when
      128*(i+2) >= 128*((nblk-1) DIV 8) -- CHECK: backedge taken while
      x0_after = in_p+128(i+2) < x5 = in_p + 128*((nblk-1) DIV 8)).
     For nblk in 9..16: (nblk-1) DIV 8 = 1, x5 = in_p+128 = x0@head0,
     0x49c b.ge TAKEN -> prepretail directly (loop never entered).
     [=> FRONT-N with 17<=nblk enters loop; a SEPARATE nblk in 9..16 leg
      goes front -> prepretail. Handle later via same seam at 0x9f0.]
   - NEXT STEPS:
     1. symbolic counter closed form: GCM_CTR_INC_ITER_INSERT (induction) +
        generic-w lanes lemma so Q0..Q4/Q30 fold to gcm_ctr_inc_iter forms
        with symbolic index (needed for invariant at symbolic i).
        [DONE session 2 -- see section 2 below: gcm_ctr_add layer.]
     2. harvest s288 -> FRONT-N postcond literal = INV(0); prove WBN_FRONT_BUF.
     3. ENSURES_WHILE_UP q with INV(i); body = 0x4a0..0x9ec (~340 instrs);
        backedge via WB_PTRCMP_FLAGS (a = 128*(i+2), d = 128*((nblk-1) DIV 8)).
     4. prepretail + tail recomposition.
   =========================================================================
   PROGRESS (2026-07-24, session 2 -- OOM POST-MORTEM + FIX):
   - Session 1 DIED at 09:01 UTC: OOM-killer took the 31GB ocaml-hol process.
     ROOT CAUSE: `prove(GCM_CTR_ADD_LANES, ... BITBLAST_TAC)` on the
     generic-w lane goal.  Unlike GCM_CTR_INC_LANES (add of CONSTANT word 1,
     BDD stays ~1.4k nodes), the abstract `w:32 word` makes every one of the
     32 sum bits depend on all lower w-bits AND ctr0-bits -> the BDD for the
     byte-extracted carry chain explodes exponentially.  First attempt hit
     the 300s eval timeout, hol_interrupt did NOT abort the BDD build
     (allocation continued in C-side loop), and the RETRY of the same prove
     doubled the pressure until the kernel killed it.
     LESSON: never BITBLAST a word_add with a symbolic addend on >=32-bit
     lanes; and after a timeout on a memory-heavy tactic, Gc.compact and
     VERIFY the goalstate -- do not re-fire the same tactic.
   - FIX (all proved, total <1s, this file section 2):
     factor into wiring-only BITBLASTs (constant-free: BREV_TOP_LANE,
     INSERT_BREV_WIRING) + the abstract add stays a free variable `s`,
     then GCM_CTR_ADD_LANES is pure REWRITE composition.  Also proved the
     algebra layer: GCM_CTR_ADD_COMPOSE, GCM_CTR_ADD_0/1,
     GCM_CTR_INC_ITER_ADD (`gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x`)
     -- the symbolic-index counter form the invariant needs (NEXT STEP 1).
   - Session-1 interactive defs salvaged from transcript into
     _docs/wbn_session1_salvage.ml (wbn_init/goal builders, WBN_LANES_TAC,
     WBN_RESOLVE_49C_TAC, DISCARD_STALE_Q30_TAC, WBN_FRONT_STEP_TAC 1..259,
     per-step 260..287 recipe).  Front sim itself must be re-run.
   ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. Scalar rung lemmas (nblk > 8 generalizations of USHR_128NBLK /         *)
(*    AND_MASK_16NBLK).  All pure word/arith, no sim.                        *)
(*                                                                           *)
(* NOTE (signed pointer compares): the 0x3e0/0x440/0x9e4 cmp x0,x5 feed      *)
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
