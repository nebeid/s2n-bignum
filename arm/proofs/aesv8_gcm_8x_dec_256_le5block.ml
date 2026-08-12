(* ============================================================================
   AESV8_GCM_8X_DEC_256, the 65-80 byte band (decrypt): bit_len = 512 + 8*bl1,
   1<=bl1<=16.  FOUR FULL blocks 0,1,2,3 (more_than_4/_3/_2/_1, GHASH vs
   H^5,H^4,H^3,H^2) + one MASKED partial block 4 (less_than_1, symbolic mask
   MK = word(2 EXP(8*bl1)-1)).  nfull = 4.  Decrypt analog, mirrors
   aesv8_gcm_8x_dec_256_le4block.ml with one extra full middle block + the 5-term
   GHASH bridge.  The bl1=16 endpoint is the whole-5-block (80 byte) case
   (all-ones mask = full block), so this band INCLUDES whole-5-block.

   Requires arm/proofs/aesv8_gcm_8x_dec_256_le4block.ml loaded (EXEC rule, MERGE_2BLK,
   the dec masked-tail machinery, BYTE_LIST_AT_NBLOCK_CTR / BYTE_LIST_AT_5BLOCKS, the
   common nblock GHASH layer with PMUL_KARATSUBA / GMULT_REDUCE_PROP3 / KARATSUBA_LIMBS /
   GHASH_POLYVAL_ACC_5, the bridge helpers (ABBREV_INNER_PMULS_TAC / MERGE_2BLK_TAC /
   WA_UNIFY_TAC / WV_UNIFY_TAC / ABBREV_WAWV_TAC / QQ0SPLIT / JOIN_EQ_SPLIT /
   LANE_FINISH_TAC / FOLD_MID_HPOW / bubble_fix), and the front/store/tail step infra).

   Two-layer structure (mirrors Mila PR #417's _CONCRETE / _ABS split):
     - GMULT5_FULL_CORRECT_BA              : the 5-block fused multiply+reduce bridge,
         built INSTANTLY by the shared fast GMULTn builder.
     - AESV8_GCM_8X_DEC_256_LE5BLOCK_BODY  : LAYER 1, the literal per-block band triple;
         the ARM simulation target.
     - AESV8_GCM_8X_DEC_256_LE5BLOCK       : LAYER 2, the READABLE public theorem with
         byte_list_at for BOTH input and output, derived sim-free from BODY via
         BYTE_LIST_AT_5BLOCKS (input) and BYTE_LIST_AT_NBLOCK_CTR + AES_CTR_5_EL (output),
         through the recursive whole-buffer spec gcm_dec_pt_bytes / gcm_dec_final_xi.
   All hyps=0, axioms()=3, no cheats.

   Cascade (x5 = byte length = 64+bl1): fall #112/#96, boundary #80 (fall, incl bl1=16),
   TAKEN #64 -> more_than_4 (0x103c = pc+4156).  H-power htable lanes: h5@htbl+96,
   h5k@htbl+112.  5-term GHASH bridge taken at the shared `eor v19,v19,v18` (pc+4564).
   No CHEAT_TAC, no new axioms.
   ============================================================================ *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_le4block.ml";;
needs "arm/proofs/utils/aes_gcm_dec_spec.ml";;
needs "common/gmult_nblock_lemmas.ml";;

(* ===========================================================================
   PART 0 — the GMULT5 bridge lemma (instant via the shared fast GMULTn builder).
   =========================================================================== *)

let PACK5_ID, GMULT5_FULL_CORRECT_BA = build_GMULTn_fast 5;;

(* ===========================================================================
   PART 1 — LE5BLOCK cascade/counter helper lemmas (bound 64+bl1<=80, x5=word(64+bl1)).
   =========================================================================== *)

let USHR_512_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (512 + 8 * bl1):int64) 3 = word (64 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (512 + 8 * bl1):int64) = 512 + 8 * bl1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let X5_ZERO_LEMMA5 = prove
 (`!bl1. 1 <= bl1 /\ bl1 <= 16
        ==> word_and (word_sub (word (64 + bl1)) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [WORD_RULE `word_sub (word (64 + bl1):int64) (word 1) = word (63 + bl1)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `j < 7` THENL
   [REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `~bit j (word 18446744073709551488:int64)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `j < 7` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[BIT_WORD] THEN
    SUBGOAL_THEN `63 + bl1 < 2 EXP j` (fun th -> SIMP_TAC[th; DIV_LT; ODD; DE_MORGAN_THM]) THEN
    TRANS_TAC LTE_TRANS `2 EXP 7` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;

let X1_MOD128_BRIDGE5 = prove
 (`!bl1. bl1 <= 16
    ==> word_and (word (512 + 8 * bl1):int64) (word 127) =
        word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (512 + 8 * bl1):int64) = 512 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `512 + 8 * bl1 = 8 * bl1 + 4 * 128`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* ival bounds for the length reg (64+bl1 <= 80), used by the cascade resolvers. *)
let IVAL_WORD_LE80 = prove
 (`!b. b <= 80 ==> ival (word b:int64) = &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival] THEN
  SUBGOAL_THEN `val (word b:int64) = b` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_SIMP_TAC[ARITH_RULE `b <= 80 ==> b < 2 EXP (64 - 1)`]);;

let IVAL_WSUB_LE80 = prove
 (`!b k. b <= 80 /\ k <= 112
          ==> ival (word_sub (word b) (word k):int64) = &b - &k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let GCM_CTR_INC4_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`,
        subst [`word 4:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let AES_CTR_5_EL = prove
 (`EL 0 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4] keys) = word_xor pt0 (aes256_encrypt ctr0 keys) /\
   EL 1 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4] keys) =
     word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys) /\
   EL 2 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4] keys) =
     word_xor pt2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) keys) /\
   EL 3 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4] keys) =
     word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) keys) /\
   EL 4 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4] keys) =
     word_xor pt4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))) keys)`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_output_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; ARITH_RULE `2 = SUC(SUC 0)`; ARITH_RULE `3 = SUC(SUC(SUC 0))`;
              ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; EL; HD; TL] THEN
  REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_INC_ITER_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[gcm_ctr_inc_iter]);;

let GHASH_POLYVAL_ACC_5 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot h h) : 256 word)
        (word_pmul t h : 256 word)))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* spec-side fold for 5 blocks: left-nested h2..h5 byteswap relations. *)
let spec_to_byteform_5 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cphm] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h5))
            (word_pmul (word_bytereverse cph1) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph2) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph3) (byteswap128 h2)))
         (word_pmul (word_bytereverse cphm) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cphm:int128`] GHASH_POLYVAL_ACC_5)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ===========================================================================
   PART 2 — cascade resolvers (bound 64+bl1<=80, x5=word(64+bl1)).
   #112/#96 fall through (dec_bl5_resolve); #80 is a BOUNDARY (64+bl1=80 at
   bl1=16; strict b.gt still falls through, bl5_resolve_pc_bdy); #64 is TAKEN ->
   more_than_4 (pc+4156, bl5_resolve_pc64_taken).
   =========================================================================== *)
let bl5_resolve_pc sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `64 + bl1 <= 80` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`64 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE80) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE80] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf "&(64 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
     [MP_TAC(ASSUME `bl1 <= 16`) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]; ALL_TAC]);;
let bl5_resolve_pc_bdy sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `64 + bl1 <= 80` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`64 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE80) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE80] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC (parse_term (Printf.sprintf "64 + bl1 = %d" k)) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      SUBGOAL_THEN (parse_term (Printf.sprintf "&(64 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
       [MP_TAC(ASSUME `bl1 <= 16`) THEN MP_TAC(ASSUME (parse_term (Printf.sprintf "~(64 + bl1 = %d)" k))) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]]; ALL_TAC]);;
let bl5_resolve_pc64_taken sN target =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s target)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false) then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `word_sub (word (64+bl1):int64) (word 64) = word bl1` (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `val (word bl1:int64) = bl1` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[IVAL_WORD_LE80; ARITH_RULE `bl1 <= 16 ==> bl1 <= 80`; ARITH_RULE `bl1 <= 16 ==> 64 + bl1 <= 80`] THEN
    SUBGOAL_THEN `~(bl1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(64+bl1) - &64:int = &bl1` (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `~(&bl1:int < &0)`];
    ALL_TAC]);;
let dec_bl5_resolve_stale = dec_bl4_resolve_stale;;
let dec_bl5_resolve sN k fall = bl5_resolve_pc sN k fall THEN dec_bl5_resolve_stale;;

(* ===========================================================================
   PART 3 — proof tactics (front / stores / masked-tail / 5-term bridge).
   Step indices are the le4 map shifted by +1 GHASH round for the extra full
   block; the exact ranges were discovered by interactive stepping.
   =========================================================================== *)
let keys15 = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;

(* FRONT: prologue + CTR/AES bulk + cascade to more_than_4 (s297, pc+4156).
   Same bulk as le4 (nfull-independent) with USHR_512/X5_ZERO_LEMMA5 and the
   word(64+bl1) length; the cascade is one rung shorter (fall #112/#96, boundary
   #80, taken #64 -> more_than_4).  ks0..ks3 abbreviated at s269, pt0 captured. *)
let full_le5_tac_front =
  DEC_FRONT_TAC USHR_512_8BL_LEMMA X5_ZERO_LEMMA5 [5;6;7] [5;6;7;30] 64 5 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (270--270) THEN dec_bl5_resolve 270 112 3808 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (271--282) THEN dec_bl5_resolve 282 96 3856 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (283--290) THEN bl5_resolve_pc_bdy 290 80 3888 THEN dec_bl5_resolve_stale THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (291--297) THEN bl5_resolve_pc64_taken 297 4156 THEN dec_bl5_resolve_stale;;

(* STORES: 4 full plaintext stores pt0/pt1/pt2/pt3.  Discovered store landmarks:
   pt0 store @ s312 (pc+4216), pt1 @ s320 (pc+4248), pt2 @ s336 (pc+4312), pt3 @ ~s344.
   Each more_than_k round does the block-(k-1) GHASH vs H^(5-k+1) and the pt store;
   Q12 is abbreviated to pt_k = word_xor cph_k (aes256_encrypt (ctr+k) keys) before
   the store, then the store readback asserted and old state discarded (mirrors le4).
   PARTIAL — front (to s297) + pt0..pt2 stores + pt3 capture VALIDATED interactively;
   remaining pt3 store + masked block 4 (less_than_1) + 5-term bridge to be filled.
   Cadence: block k GHASHes vs H-power lane loaded into Q20/Q25/... (h5,h4,h3,h2,h). *)
let full_le5_tac_stores =
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (298--312) THEN
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
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (314--320) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 16))) (s320:armstate) = pt1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s320" THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph2:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc ctr0):int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt2:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph2:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc ctr0):int128`),keys15)))) THEN
  DISCARD_OLDSTATE_TAC "s320" THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (321--336) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 32))) (s336:armstate) = pt2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s336" THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph3:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC3_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt3:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph3:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`),keys15)))) THEN
  DISCARD_OLDSTATE_TAC "s336" THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (337--352) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 48))) (s352:armstate) = pt3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s352";;

(* MASKED TAIL: pt4 capture, GHASH masked round (collapse Q9 to cphm at s376 BEFORE
   the rev64), masked-blend store at out_p+64 (s392), to the bridge state s399. *)
let full_le5_tac_tail =
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (353--357) THEN
  MP_TAC(SPEC `bl1:num` X1_MOD128_BRIDGE5) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  DISCARD_OLDSTATE_TAC "s357" THEN
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_DEC_256_EXEC (358--376) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_and cph4 (word (2 EXP (8 * bl1) - 1)):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  REWRITE_TAC[INSERT2_JOIN] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
  (* block-4 plaintext eor3 forms Q12 at s377; capture pt4 HERE (Q12 is still pt3 before this). *)
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_DEC_256_EXEC (377--377) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph4:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))):int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC4_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt4:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph4:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))):int128`),keys15)))) THEN
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_DEC_256_EXEC (378--380) THEN
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_DEC_256_EXEC (381--381) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor (word_and (pt4:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "pt4" THEN REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN
    REWRITE_TAC[BLEND_OR_XOR] THEN REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  DISCARD_OLDSTATE_TAC "s381" THEN
  ABBREV_TAC `cphm:int128 = word_and cph4 (word (2 EXP (8 * bl1) - 1))` THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (382--393) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 64))) (s393:armstate) =
       word_xor (word_and (pt4:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 64))) s393` with _ -> false)
       && (try is_comb(rand(concl th)) && fst(dest_const(rator(rator(rand(concl th))))) = "word_xor" with _ -> false)
    then MP_TAC th else NO_TAC) THEN DISCARD_OLDSTATE_TAC "s393" THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (394--400) THEN
  DISCARD_OLDSTATE_TAC "s400";;

(* 5-TERM GHASH bridge: read Q19 s399 = ghash_polyval_acc (bsw h)(brev xi)[brev cph0..cphm].
   Like le4's BRIDGE_CLOSE_TAC_4 but folds THREE machine-side middle mids explicitly
   (cph1.h4, cph2.h3, cph3.h2); the masked-block mid auto-folds via MERGE.  The folds
   use the SHARED multiplier-keyed FOLD_MID_HPOW from le3block.ml (STEP A of
   _docs/dec-band-homogenization-convergence-plan.md). *)

let BRIDGE_CLOSE_TAC_5 : tactic =
  DEC_BRIDGE_CLOSE_TAC 5 400 GMULT5_FULL_CORRECT_BA spec_to_byteform_5 ALL_TAC;;

(* POST-BRIDGE: assert + close the bridge, then rev64 + st1 xi_p (s400-402),
   ENSURES_FINAL_STATE, MONOTONE_MAYCHANGE.  Exit pc+4580. *)
let full_le5_tac_bridge =
  SUBGOAL_THEN `read Q19 (s400:armstate) = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cphm]`
    (fun th -> ASSUME_TAC th) THENL [BRIDGE_CLOSE_TAC_5; ALL_TAC] THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let c = concl th in is_eq c && (try lhs c = `read Q19 s400` with _->false) &&
    not(try fst(dest_const(repeat rator (rhs c)))="ghash_polyval_acc" with _->false)) THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cphm]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (401--402) THEN
  DISCARD_OLDSTATE_TAC "s402" THEN
  SUBGOAL_THEN `read Q19 (s402:armstate) = word_bytereverse (gval:int128)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `read Q19 s402` with _ -> false)
      then ACCEPT_TAC(GEN_REWRITE_RULE RAND_CONV [BREV_JOIN_REV8] th) else NO_TAC); ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [403] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BREV_JOIN_REV8] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;


(* ---- LAYER 1: the literal per-block band triple (ARM-sim target).
   bit_len = 512 + 8*bl1, 1<=bl1<=16: four FULL ciphertext blocks 0,1,2,3 + one
   MASKED partial tail block 4.  Input = five per-block ciphertext reads
   cph0..cph4; output = four full plaintext stores + block-4 masked-blend + GHASH tag. ---- *)
let AESV8_GCM_8X_DEC_256_LE5BLOCK_BODY = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 cph2 h3 h3k cph3 h4 cph4 h5 h5k.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,80) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,80) (xi_p,16) /\
    nonoverlapping (out_p,80) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,80) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,80) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,80) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,80) (in_p,80) /\
    nonoverlapping (out_p,80) (key_p,240) /\
    nonoverlapping (out_p,80) (htbl_p,192) /\
    nonoverlapping (out_p,80) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    word_subword h3k (64,64) = word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64)) /\
    word_subword h5k (0,64) = word_xor (word_subword h5 (0,64):64 word) (word_subword h5 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (512 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             read (memory :> bytes128 in_p) s = cph0 /\
             read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
             read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
             read (memory :> bytes128 (word_add in_p (word 48))) s = cph3 /\
             read (memory :> bytes128 (word_add in_p (word 64))) s = cph4 /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 64))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4 /\
             read (memory :> bytes128 (word_add htbl_p (word 96))) s = h5 /\
             read (memory :> bytes128 (word_add htbl_p (word 112))) s = h5k)
        (\s. read PC s = word (pc + 4580) /\
             read (memory :> bytes128 out_p) s =
             word_xor cph0 (aes256_encrypt ctr0 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 16))) s =
             word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 32))) s =
             word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 48))) s =
             word_xor cph3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 64))) s =
             word_xor
             (word_and
              (word_xor cph4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]))
             (word (2 EXP (8 * bl1) - 1)))
             (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
             read (memory :> bytes128 xi_p) s =
             word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3;
                 word_bytereverse (word_and cph4 (word (2 EXP (8 * bl1) - 1)))]))
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,80); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  full_le5_tac_front THEN full_le5_tac_stores THEN full_le5_tac_tail THEN full_le5_tac_bridge);;

(* ============================================================================
   LAYER 2: the READABLE public theorem AESV8_GCM_8X_DEC_256_LE5BLOCK.
   byte_list_at for BOTH input (80 bytes) and output (64 + bl1 bytes), stated over
   the whole input buffer x via the recursive spec gcm_dec_pt_bytes / gcm_dec_final_xi.
   Proved sim-free from BODY via BYTE_LIST_AT_5BLOCKS (input) and BYTE_LIST_AT_NBLOCK_CTR
   + AES_CTR_5_EL (output).  hyps=0, axioms()=3, no cheats.
   ============================================================================ *)
let le5_body_spec_args =
  [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;`in_p:int64`;`key_p:int64`;`htbl_p:int64`;
   `bytes_to_int128 (SUB_LIST (0,16) (x:byte list))`;
   `bytes_to_int128 (SUB_LIST (16,16) (x:byte list))`;
   `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;
   `k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;
   `h:int128`;`hk:int128`;`h2:int128`;`outprev:int128`;`bl1:num`;
   `bytes_to_int128 (SUB_LIST (32,16) (x:byte list))`;`h3:int128`;`h3k:int128`;
   `bytes_to_int128 (SUB_LIST (48,16) (x:byte list))`;`h4:int128`;
   `bytes_to_int128 (SUB_LIST (64,16) (x:byte list))`;`h5:int128`;`h5k:int128`];;

let AESV8_GCM_8X_DEC_256_LE5BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    x xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 h3 h3k h4 h5 h5k.
    LENGTH x = 80 /\
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,80) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,80) (xi_p,16) /\
    nonoverlapping (out_p,80) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,80) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,80) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,80) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,80) (in_p,80) /\
    nonoverlapping (out_p,80) (key_p,240) /\
    nonoverlapping (out_p,80) (htbl_p,192) /\
    nonoverlapping (out_p,80) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    word_subword h3k (64,64) = word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64)) /\
    word_subword h5k (0,64) = word_xor (word_subword h5 (0,64):64 word) (word_subword h5 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (512 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             byte_list_at x in_p (word 80) s /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 64))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4 /\
             read (memory :> bytes128 (word_add htbl_p (word 96))) s = h5 /\
             read (memory :> bytes128 (word_add htbl_p (word 112))) s = h5k)
        (\s. read PC s = word (pc + 4580) /\
             byte_list_at
               (gcm_dec_pt_bytes (64 + bl1) x ctr0
                 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14])
               out_p (word (64 + bl1)) s /\
             read (memory :> bytes128 xi_p) s = gcm_dec_final_xi (64 + bl1) x xi h)
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,80); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[gcm_dec_final_xi; GCM_DEC_GHASH_BLOCKS_5; GCM_DEC_PT_BYTES_5; MAP] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
    (rand(rator(rator(rand(concl(SPECL le5_body_spec_args AESV8_GCM_8X_DEC_256_LE5BLOCK_BODY)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`0`; `x:byte list`; `in_p:int64`; `word 80:int64`; `s:armstate`] BYTE_LIST_AT_5BLOCKS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `val (word 80:int64) = 80` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
      (rand(rator(rand(concl(SPECL le5_body_spec_args AESV8_GCM_8X_DEC_256_LE5BLOCK_BODY))))) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BYTE_LIST_AT_NBLOCK_CTR THEN EXISTS_TAC `outprev:int128` THEN
      REWRITE_TAC[AES_CTR_5_EL] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `val (word (64 + bl1):int64) = 64 + bl1` SUBST1_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ARITH_TAC;
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        X_GEN_TAC `kk:num` THEN REWRITE_TAC[ARITH_RULE `kk < 4 <=> kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0; AES_CTR_5_EL] THEN ASM_REWRITE_TAC[AES_CTR_5_EL];
        REWRITE_TAC[ARITH_RULE `16 * 4 = 64`] THEN ASM_REWRITE_TAC[AES_CTR_5_EL]];
      MATCH_MP_TAC AESV8_GCM_8X_DEC_256_LE5BLOCK_BODY THEN ASM_REWRITE_TAC[]]]);;
