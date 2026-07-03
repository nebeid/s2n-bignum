(* ============================================================================
   AESV8_GCM_8X_DEC_256, the 49-64 byte band (decrypt): bit_len = 384 + 8*bl1,
   1<=bl1<=16.  THREE FULL blocks 0,1,2 (more_than_3/_2/_1, GHASH vs H^4,H^3,H^2)
   + one MASKED partial block 3 (less_than_1, symbolic mask MK = word(2 EXP(8*bl1)-1)).
   nfull = 3.  Decrypt analog, mirrors aesv8_gcm_8x_dec_256_le3block.ml with one
   extra full middle block + the 4-term GHASH bridge.  The bl1=16 endpoint is the
   whole-4-block (64 byte) case (all-ones mask = full block), so this band INCLUDES
   whole-4-block; whole-3-block (48 byte) is the bl1=16 endpoint of LE3BLOCK.

   Requires arm/proofs/aesv8_gcm_8x_dec_256_le3block.ml loaded (EXEC rule, MERGE_2BLK,
   the dec masked-tail machinery, BYTE_LIST_AT_NBLOCK_CTR / BYTE_LIST_AT_4BLOCKS, the
   common nblock GHASH layer with PMUL_KARATSUBA / GMULT_REDUCE_PROP3 / KARATSUBA_LIMBS /
   GHASH_POLYVAL_ACC_4, the bridge helpers (ABBREV_INNER_PMULS_TAC / MERGE_2BLK_TAC /
   WA_UNIFY_TAC / WV_UNIFY_TAC / ABBREV_WAWV_TAC / QQ0SPLIT / JOIN_EQ_SPLIT /
   LANE_FINISH_TAC / bubble_fix), and the front/store/tail step infrastructure).

   Two-layer structure (mirrors Mila PR #417's _CONCRETE / _ABS split; both triples
   are written out EXPLICITLY in source — no goal-surgery builders):
     - GMULT4_FULL_CORRECT_BA              : the 4-block fused multiply+reduce bridge lemma,
         built INSTANTLY by the fast GMULTn builder (PACK_N via XOR-AC + per-block PACK1,
         ~0.3s vs the old ~373s monolithic CONV_TAC WORD_RULE).
     - AESV8_GCM_8X_DEC_256_LE4BLOCK_BODY  : LAYER 1, the literal per-block band triple
         (per-block cphk reads in / per-block plaintext stores + GHASH out); the ARM
         simulation target.  Proved by the full simulation.
     - AESV8_GCM_8X_DEC_256_LE4BLOCK       : LAYER 2, the READABLE public theorem with
         byte_list_at for BOTH input and output, derived sim-free from BODY via
         BYTE_LIST_AT_4BLOCKS (input) and BYTE_LIST_AT_NBLOCK_CTR + AES_CTR_4_EL (output).
   All hyps=0, axioms()=3, no cheats.

   TWO ROOT-CAUSE INSIGHTS that unblocked the hard parts:
   (1) Opaque-Q7 masked-block keystream: v7 = ctr+3 = the ORIGINAL v3 keystream,
       propagated up by the tail shift-register movs (0xee0-0xf5c).  The standard bulk
       discard `mk_discard2 [3;4;5;6;7]` KILLS original-v3, leaving an opaque `read Q7`.
       FIX: keep Q3 in the bulk (discard only [4;5;6;7]); at s269 ABBREV the 4 surviving
       keystreams to atoms; step the cascade with PLAIN ARM_STEPS (VSTEPS OOMs on the
       conditional-PC terms).  v0..v7 = ctr+0..ctr+7 from the bulk; the 4-block
       fall-through shift lands v5=ctr+1, v6=ctr+2, v7=ctr+3.
   (2) Masked GHASH input must be collapsed to cphm BEFORE the rev64 that feeds the
       masked GHASH round.  `and v9,v9,v0` at 0x1174 (s368); rev64 v8,v9 at 0x1180 (s371).
       Collapse Q9 to `word_and cph3 MK` at s368, NOT later, or the bridge's masked qq
       atom carries the raw `word_and(insert(aese..))` form and won't merge.

   The 4-term GHASH bridge (BRIDGE_CLOSE_TAC_4) is taken at s392 = pc+4568 (AFTER the
   shared `eor v19,v19,v18` at 0x11d4) — the same off-by-one discipline as le3.

   No CHEAT_TAC, no new axioms.
   ============================================================================ *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_le3block.ml";;
(* Recursive whole-buffer decrypt spec (gcm_dec_pt_bytes / gcm_dec_final_xi) +
   the per-N unfold lemmas (GCM_DEC_PT_BYTES_N / GCM_DEC_GHASH_BLOCKS_N) — the dec
   analogue of Mila's gcm_ghash_blocks/gcm_final_xi.  The readable LAYER 2 wrapper
   states its postcondition over the whole input buffer x via these specs, moving
   the per-block expansion off the theorem statement into the recursive definition. *)
needs "arm/proofs/utils/aes_gcm_dec_spec.ml";;

(* ===========================================================================
   PART 0 — the GMULT4 bridge lemma, built INSTANTLY by the shared fast GMULTn
   builder (common/gmult_nblock_lemmas.ml).  GMULT4_FULL_CORRECT_BA is the
   4-block analog of GMULT2/GMULT3; building it via build_GMULTn_fast costs ~0.3s
   vs the old ~373s monolithic CONV_TAC WORD_RULE PACK (which never finished at N=4).
   =========================================================================== *)

needs "common/gmult_nblock_lemmas.ml";;

(* GMULT4 (the le4block bridge lemma) — instant via the fast builder. *)
let PACK4_ID, GMULT4_FULL_CORRECT_BA = build_GMULTn_fast 4;;

(* ===========================================================================
   PART 1 — LE4BLOCK cascade/counter helper lemmas (bound 48+bl1<=64, x5=word(48+bl1)).
   =========================================================================== *)

let USHR_384_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (384 + 8 * bl1):int64) 3 = word (48 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (384 + 8 * bl1):int64) = 384 + 8 * bl1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let X5_ZERO_LEMMA4 = prove
 (`!bl1. 1 <= bl1 /\ bl1 <= 16
        ==> word_and (word_sub (word (48 + bl1)) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [WORD_RULE `word_sub (word (48 + bl1):int64) (word 1) = word (47 + bl1)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `j < 7` THENL
   [REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `~bit j (word 18446744073709551488:int64)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `j < 7` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[BIT_WORD] THEN
    SUBGOAL_THEN `47 + bl1 < 2 EXP j` (fun th -> SIMP_TAC[th; DIV_LT; ODD; DE_MORGAN_THM]) THEN
    TRANS_TAC LTE_TRANS `2 EXP 7` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;

let IVAL_WORD_LE64 = prove
 (`!b. b <= 64 ==> ival (word b:int64) = &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival] THEN
  SUBGOAL_THEN `val (word b:int64) = b` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_SIMP_TAC[ARITH_RULE `b <= 64 ==> b < 2 EXP (64 - 1)`]);;

let IVAL_WSUB_LE64 = prove
 (`!b k. b <= 64 /\ k <= 112
          ==> ival (word_sub (word b) (word k):int64) = &b - &k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let X1_MOD128_BRIDGE4 = prove
 (`!bl1. bl1 <= 16
    ==> word_and (word (384 + 8 * bl1):int64) (word 127) =
        word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (384 + 8 * bl1):int64) = 384 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `384 + 8 * bl1 = 8 * bl1 + 3 * 128`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let GCM_CTR_INC3_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`,
        subst [`word 3:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let AES_CTR_4_EL = prove
 (`EL 0 (aes_ctr ctr0 [pt0;pt1;pt2;pt3] keys) = word_xor pt0 (aes256_encrypt ctr0 keys) /\
   EL 1 (aes_ctr ctr0 [pt0;pt1;pt2;pt3] keys) =
     word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys) /\
   EL 2 (aes_ctr ctr0 [pt0;pt1;pt2;pt3] keys) =
     word_xor pt2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) keys) /\
   EL 3 (aes_ctr ctr0 [pt0;pt1;pt2;pt3] keys) =
     word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) keys)`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; ARITH_RULE `2 = SUC(SUC 0)`; ARITH_RULE `3 = SUC(SUC(SUC 0))`; EL; HD; TL] THEN
  REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_INC_ITER_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[gcm_ctr_inc_iter]);;

(* spec-side fold for 4 blocks: ghash_polyval_acc 4-block = prop3 of the H-power
   pmul-sum, under the LEFT-NESTED h2/h3/h4 byteswap relations (matching the
   htable's H-power layout that GHASH_POLYVAL_ACC_4 produces). *)
let spec_to_byteform_4 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cphm] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h4))
           (word_pmul (word_bytereverse cph1) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h2)))
         (word_pmul (word_bytereverse cphm) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cphm:int128`] GHASH_POLYVAL_ACC_4)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ===========================================================================
   PART 2 — cascade resolvers (bound 48+bl1<=64, x5=word(48+bl1)).
   #112/#96/#80 fall through (dec_bl4_resolve); #64 is a BOUNDARY (48+bl1=64 at
   bl1=16; strict b.gt still falls through, bl4_resolve_pc_bdy); #48 is TAKEN ->
   more_than_3 (pc+4212, bl4_resolve_pc48_taken).
   =========================================================================== *)
let bl4_resolve_pc sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `48 + bl1 <= 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`48 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE64) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE64] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf "&(48 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
     [MP_TAC(ASSUME `bl1 <= 16`) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]; ALL_TAC]);;
let bl4_resolve_pc_bdy sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `48 + bl1 <= 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`48 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE64) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE64] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC (parse_term (Printf.sprintf "48 + bl1 = %d" k)) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      SUBGOAL_THEN (parse_term (Printf.sprintf "&(48 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
       [MP_TAC(ASSUME `bl1 <= 16`) THEN MP_TAC(ASSUME (parse_term (Printf.sprintf "~(48 + bl1 = %d)" k))) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]]; ALL_TAC]);;
let bl4_resolve_pc48_taken sN target =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s target)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false) then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `word_sub (word (48+bl1):int64) (word 48) = word bl1` (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `val (word bl1:int64) = bl1` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[IVAL_WORD_LE64; ARITH_RULE `bl1 <= 16 ==> bl1 <= 64`; ARITH_RULE `bl1 <= 16 ==> 48 + bl1 <= 64`] THEN
    SUBGOAL_THEN `~(bl1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(48+bl1) - &48:int = &bl1` (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `~(&bl1:int < &0)`];
    ALL_TAC]);;
let dec_bl4_resolve_stale = dec_bl3_resolve_stale;;
let dec_bl4_resolve sN k fall = bl4_resolve_pc sN k fall THEN dec_bl4_resolve_stale;;

(* ===========================================================================
   PART 3 — the proof tactics (front / stores / masked-tail / 4-term bridge).
   =========================================================================== *)
let keys15 = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;

(* FRONT: prologue + CTR/AES bulk + cascade to more_than_3 (s303, pc+4212).
   KEYSTREAM FIX: keep Q3 in the bulk (discard only [4;5;6;7]); abbreviate the 4
   surviving keystreams at s269; step the cascade with PLAIN ARM_STEPS so the
   shift-register movs materialize read Q7 s303 = ctr+3 (see header note 1). *)
let full_le4_tac_front =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (1--5) THEN
  MP_TAC(SPEC `bl1:num` USHR_384_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [4;5;6;7]) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (31--84) THEN mk_discard2 [4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (85--173) THEN mk_discard2 [4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (174--177) THEN GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (178--184) THEN mk_discard2 [4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (185--254) THEN mk_discard2 [4;5;6;7;30] THEN GCM_SIMD_SIMPLIFY_TAC THEN
  MP_TAC(SPEC `bl1:num` X5_ZERO_LEMMA4) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [255] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (256--265) THEN mk_discard2 [4;5;6;7;30] THEN
  MP_TAC(SPEC `bl1:num` USHR_384_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub (word_add in_p (word (48 + bl1):int64)) in_p = word (48 + bl1)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (266--269) THEN
  ABBREV_TAC `ks0:int128 = read Q0 s269` THEN
  ABBREV_TAC `ks1:int128 = read Q1 s269` THEN
  ABBREV_TAC `ks2:int128 = read Q2 s269` THEN
  ABBREV_TAC `ks3:int128 = read Q3 s269` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt0:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (270--270) THEN dec_bl4_resolve 270 112 3808 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (271--282) THEN dec_bl4_resolve 282 96 3856 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (283--290) THEN dec_bl4_resolve 290 80 3888 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (291--297) THEN bl4_resolve_pc_bdy 297 64 3916 THEN dec_bl4_resolve_stale THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (298--303) THEN bl4_resolve_pc48_taken 303 4212 THEN dec_bl4_resolve_stale;;

(* STORES: 3 full plaintext stores pt0/pt1/pt2 to s350. *)
let full_le4_tac_stores =
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (304--312) THEN
  SUBGOAL_THEN `read (memory :> bytes128 out_p) (s312:armstate) = pt0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt0" THEN REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s312" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC [313] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph1:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc ctr0:int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt1:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph1:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc ctr0:int128`),keys15)))) THEN
  DISCARD_OLDSTATE_TAC "s313" THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (314--327) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 16))) (s327:armstate) = pt1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s327" THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (328--334) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph2:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc ctr0):int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt2:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph2:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc ctr0):int128`),keys15)))) THEN
  DISCARD_OLDSTATE_TAC "s334" THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (335--350) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 32))) (s350:armstate) = pt2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s350";;

(* MASKED TAIL: pt3 capture, GHASH masked round (collapse Q9 to cphm at s368 BEFORE
   the rev64 at s371), masked-blend store at out_p+48, to the bridge state s392. *)
let full_le4_tac_tail =
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph3:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC3_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt3:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph3:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`),keys15)))) THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (351--357) THEN
  MP_TAC(SPEC `bl1:num` X1_MOD128_BRIDGE4) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  DISCARD_OLDSTATE_TAC "s357" THEN
  ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (358--368) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_and cph3 (word (2 EXP (8 * bl1) - 1)):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  REWRITE_TAC[INSERT2_JOIN] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
  ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (369--373) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor (word_and (pt3:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "pt3" THEN REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN
    REWRITE_TAC[BLEND_OR_XOR] THEN REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  DISCARD_OLDSTATE_TAC "s373" THEN
  ABBREV_TAC `cphm:int128 = word_and cph3 (word (2 EXP (8 * bl1) - 1))` THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (374--385) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 48))) (s385:armstate) =
       word_xor (word_and (pt3:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 48))) s385` with _ -> false)
       && (try is_comb(rand(concl th)) && fst(dest_const(rator(rator(rand(concl th))))) = "word_xor" with _ -> false)
    then MP_TAC th else NO_TAC) THEN DISCARD_OLDSTATE_TAC "s385" THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (386--392) THEN
  DISCARD_OLDSTATE_TAC "s392";;

(* 4-TERM BRIDGE: read Q19 s392 = ghash_polyval_acc (bsw h)(brev xi)[brev cph0..cphm].
   Like le3's BRIDGE_CLOSE_TAC but folds TWO machine-side middle mids explicitly
   (cph1.h3, cph2.h2); the masked-block mid auto-folds in MERGE once it is cphm
   (header note 2).  The folds use the SHARED multiplier-keyed FOLD_MID_HPOW
   from le3block.ml (STEP A of _docs/dec-band-homogenization-convergence-plan.md). *)

let BRIDGE_CLOSE_TAC_4 : tactic = fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->try lhs(concl th)=`read Q19 s392` with _->false) asl) in
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
  let gmult4_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
            `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
            `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
            `word_bytereverse cphm:int128`; `byteswap128 h:int128`] GMULT4_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_4 (end_itlist CONJ [h2asm;h3asm;h4asm])) (GSYM gmult4_dec) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   FOLD_MID_HPOW "H3" THEN FOLD_MID_HPOW "H2" THEN
   WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC)
  (asl,w);;

(* POST-BRIDGE: assert + close the bridge, then rev64 + st1 xi_p (s393-395),
   ENSURES_FINAL_STATE, MONOTONE_MAYCHANGE.  Exit pc+4580. *)
let full_le4_tac_bridge =
  SUBGOAL_THEN `read Q19 (s392:armstate) = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cphm]`
    (fun th -> ASSUME_TAC th) THENL [BRIDGE_CLOSE_TAC_4; ALL_TAC] THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let c = concl th in is_eq c && (try lhs c = `read Q19 s392` with _->false) &&
    not(try fst(dest_const(repeat rator (rhs c)))="ghash_polyval_acc" with _->false)) THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cphm]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (393--394) THEN
  DISCARD_OLDSTATE_TAC "s394" THEN
  SUBGOAL_THEN `read Q19 (s394:armstate) = word_bytereverse (gval:int128)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `read Q19 s394` with _ -> false)
      then ACCEPT_TAC(GEN_REWRITE_RULE RAND_CONV [BREV_JOIN_REV8] th) else NO_TAC); ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [395] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BREV_JOIN_REV8] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

(* ---- LAYER 1 (= Mila PR #417 _CONCRETE): the literal per-block band triple,
   the ARM-simulation target, with its statement WRITTEN OUT EXPLICITLY.
   bit_len = 384 + 8*bl1, 1<=bl1<=16: three FULL ciphertext blocks 0,1,2 + one
   MASKED partial tail block 3 (mask = word(2 EXP (8*bl1) - 1)).  Input is the four
   per-block ciphertext reads cph0/cph1/cph2/cph3; output is the four per-block
   plaintext stores (block 3 masked-blended with outprev) + the GHASH tag in xi_p. ---- *)
let AESV8_GCM_8X_DEC_256_LE4BLOCK_BODY = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 cph2 h3 h3k cph3 h4.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,64) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,64) (xi_p,16) /\
    nonoverlapping (out_p,64) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,64) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,64) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,64) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,64) (in_p,64) /\
    nonoverlapping (out_p,64) (key_p,240) /\
    nonoverlapping (out_p,64) (htbl_p,192) /\
    nonoverlapping (out_p,64) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    word_subword h3k (64,64) = word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (384 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             read (memory :> bytes128 in_p) s = cph0 /\
             read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
             read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
             read (memory :> bytes128 (word_add in_p (word 48))) s = cph3 /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 48))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
             read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
             read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k /\
             read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4)
        (\s. read PC s = word (pc + 4580) /\
             read (memory :> bytes128 out_p) s =
             word_xor cph0 (aes256_encrypt ctr0 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 16))) s =
             word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 32))) s =
             word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 48))) s =
             word_xor
             (word_and
              (word_xor cph3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]))
             (word (2 EXP (8 * bl1) - 1)))
             (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
             read (memory :> bytes128 xi_p) s =
             word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
                 word_bytereverse (word_and cph3 (word (2 EXP (8 * bl1) - 1)))]))
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,64); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  full_le4_tac_front THEN full_le4_tac_stores THEN full_le4_tac_tail THEN full_le4_tac_bridge);;

(* ============================================================================
   LAYER 2 (= Mila PR #417 _ABS): the READABLE public theorem
   AESV8_GCM_8X_DEC_256_LE4BLOCK.  ONE explicit `ensures arm` Hoare triple with
   `byte_list_at` for BOTH the input ciphertext buffer (64 bytes) and the output
   plaintext buffer (48 + bl1 bytes = 3 full blocks ++ first bl1 bytes of the
   masked tail).  Proved sim-free from BODY via BYTE_LIST_AT_4BLOCKS (input) and
   BYTE_LIST_AT_NBLOCK_CTR + AES_CTR_4_EL (output), through
   ENSURES_PRE/POSTCONDITION_THM.  hyps=0, axioms()=3, no cheats.
   ============================================================================ *)
let le4_body_spec_args =
  [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;`in_p:int64`;`key_p:int64`;`htbl_p:int64`;
   `bytes_to_int128 (SUB_LIST (0,16) (x:byte list))`;
   `bytes_to_int128 (SUB_LIST (16,16) (x:byte list))`;
   `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;
   `k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;
   `h:int128`;`hk:int128`;`h2:int128`;`outprev:int128`;`bl1:num`;
   `bytes_to_int128 (SUB_LIST (32,16) (x:byte list))`;`h3:int128`;`h3k:int128`;
   `bytes_to_int128 (SUB_LIST (48,16) (x:byte list))`;`h4:int128`];;

let AESV8_GCM_8X_DEC_256_LE4BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    x xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 h3 h3k h4.
    LENGTH x = 64 /\
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,64) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,64) (xi_p,16) /\
    nonoverlapping (out_p,64) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,64) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,64) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,64) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,64) (in_p,64) /\
    nonoverlapping (out_p,64) (key_p,240) /\
    nonoverlapping (out_p,64) (htbl_p,192) /\
    nonoverlapping (out_p,64) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    word_subword h3k (64,64) = word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (384 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             byte_list_at x in_p (word 64) s /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 48))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
             read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
             read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k /\
             read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4)
        (\s. read PC s = word (pc + 4580) /\
             byte_list_at
               (gcm_dec_pt_bytes (48 + bl1) x ctr0
                 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14])
               out_p (word (48 + bl1)) s /\
             read (memory :> bytes128 xi_p) s = gcm_dec_final_xi (48 + bl1) x xi h)
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,64); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Unfold the recursive whole-buffer spec to the explicit 4-block list the BODY
     produces (nfull=3, tail=bl1), so the rest of the proof is unchanged. *)
  ASM_SIMP_TAC[gcm_dec_final_xi; GCM_DEC_GHASH_BLOCKS_4; GCM_DEC_PT_BYTES_4; MAP] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
    (rand(rator(rator(rand(concl(SPECL le4_body_spec_args AESV8_GCM_8X_DEC_256_LE4BLOCK_BODY)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`0`; `x:byte list`; `in_p:int64`; `word 64:int64`; `s:armstate`] BYTE_LIST_AT_4BLOCKS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `val (word 64:int64) = 64` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
      (rand(rator(rand(concl(SPECL le4_body_spec_args AESV8_GCM_8X_DEC_256_LE4BLOCK_BODY))))) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BYTE_LIST_AT_NBLOCK_CTR THEN EXISTS_TAC `outprev:int128` THEN
      REWRITE_TAC[AES_CTR_4_EL] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `val (word (48 + bl1):int64) = 48 + bl1` SUBST1_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ARITH_TAC;
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        X_GEN_TAC `kk:num` THEN REWRITE_TAC[ARITH_RULE `kk < 3 <=> kk = 0 \/ kk = 1 \/ kk = 2`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0; AES_CTR_4_EL] THEN ASM_REWRITE_TAC[AES_CTR_4_EL];
        REWRITE_TAC[ARITH_RULE `16 * 3 = 48`] THEN ASM_REWRITE_TAC[AES_CTR_4_EL]];
      MATCH_MP_TAC AESV8_GCM_8X_DEC_256_LE4BLOCK_BODY THEN ASM_REWRITE_TAC[]]]);;
