(* ============================================================================
   AESV8_GCM_8X_DEC_256, the 97-112 byte band (decrypt): bit_len = 768 + 8*bl1,
   1<=bl1<=16.  SIX FULL blocks 0..5 (more_than_6/_5/_4/_3/_2/_1, GHASH vs
   H^7,H^6,H^5,H^4,H^3,H^2) + one MASKED partial block 6 (less_than_1, mask
   MK = word(2 EXP(8*bl1)-1)).  nfull = 6.  Mirror of le6block with one extra full
   middle block + the 7-term GHASH bridge.  bl1=16 endpoint = whole-7-block (112B).

   Two-layer structure (BODY = literal per-block triple; LE7BLOCK = readable byte_list_at
   wrapper for in 112B / out 96+bl1).  Cascade x5=96+bl1: #112 is the BOUNDARY rung
   (bl7_resolve_pc_bdy), #96 strictly TAKEN -> more_than_6 (0xfc8 = pc+4040, s282).  Store
   cadence pt0..pt5 complete by s368; masked block 6: Q9->cphm @ s392 (pc+4480), block-6
   eor3+blend @ s393, masked store out_p+96 @ s409 (pc+4548).  7-term GHASH bridge @ s414
   (pc+4568); exit pc+4580.  KEY: Q6 (block-6 masked keystream) is KEPT RAW in the front
   (discard [7] not [6;7]) so the pt6 blend-capture closes by WORD_BLAST.  H-power htable:
   h6@htbl+128, h7@htbl+144, h7k@htbl+160.  All stepping uses the per-step-discard steppers
   (tips-doc).  All hyps=0, axioms()=3, no CHEAT_TAC, no new axioms.
   ============================================================================ *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_le6block.ml";;
needs "arm/proofs/utils/aes_gcm_dec_spec.ml";;
needs "common/gmult_nblock_lemmas.ml";;

(* ===========================================================================
   PART 0 — the GMULT7 bridge lemma (instant via the shared fast GMULTn builder).
   =========================================================================== *)

let PACK7_ID, GMULT7_FULL_CORRECT_BA = build_GMULTn_fast 7;;

(* ===========================================================================
   PART 1 — LE7BLOCK cascade/counter helper lemmas (bound 64+bl1<=80, x5=word(64+bl1)).
   =========================================================================== *)

let USHR_768_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (768 + 8 * bl1):int64) 3 = word (96 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (768 + 8 * bl1):int64) = 768 + 8 * bl1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let X5_ZERO_LEMMA7 = prove
 (`!bl1. 1 <= bl1 /\ bl1 <= 16
        ==> word_and (word_sub (word (96 + bl1)) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [WORD_RULE `word_sub (word (96 + bl1):int64) (word 1) = word (95 + bl1)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `j < 7` THENL
   [REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `~bit j (word 18446744073709551488:int64)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `j < 7` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[BIT_WORD] THEN
    SUBGOAL_THEN `95 + bl1 < 2 EXP j` (fun th -> SIMP_TAC[th; DIV_LT; ODD; DE_MORGAN_THM]) THEN
    TRANS_TAC LTE_TRANS `2 EXP 7` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;

let X1_MOD128_BRIDGE7 = prove
 (`!bl1. bl1 <= 16
    ==> word_and (word (768 + 8 * bl1):int64) (word 127) =
        word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (768 + 8 * bl1):int64) = 768 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `768 + 8 * bl1 = 8 * bl1 + 6 * 128`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* ival bounds for the length reg (96+bl1 <= 112), used by the cascade resolvers. *)
let IVAL_WORD_LE112 = prove
 (`!b. b <= 112 ==> ival (word b:int64) = &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival] THEN
  SUBGOAL_THEN `val (word b:int64) = b` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_SIMP_TAC[ARITH_RULE `b <= 112 ==> b < 2 EXP (64 - 1)`]);;

let IVAL_WSUB_LE112 = prove
 (`!b k. b <= 112 /\ k <= 112
          ==> ival (word_sub (word b) (word k):int64) = &b - &k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let GCM_CTR_INC6_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))`,
        subst [`word 6:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let AES_CTR_7_EL = prove
 (`EL 0 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6] keys) = word_xor pt0 (aes256_encrypt ctr0 keys) /\
   EL 1 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6] keys) = word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys) /\
   EL 2 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6] keys) = word_xor pt2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) keys) /\
   EL 3 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6] keys) = word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) keys) /\
   EL 4 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6] keys) = word_xor pt4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))) keys) /\
   EL 5 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6] keys) = word_xor pt5 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))) keys) /\
   EL 6 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6] keys) = word_xor pt6 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))) keys)`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; ARITH_RULE `2 = SUC(SUC 0)`; ARITH_RULE `3 = SUC(SUC(SUC 0))`;
              ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; ARITH_RULE `5 = SUC(SUC(SUC(SUC(SUC 0))))`;
              ARITH_RULE `6 = SUC(SUC(SUC(SUC(SUC(SUC 0)))))`; EL; HD; TL] THEN
  REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_INC_ITER_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[gcm_ctr_inc_iter]);;

let GHASH_POLYVAL_ACC_7 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot h h) : 256 word)
        (word_pmul v h : 256 word)))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* spec-side fold for 7 blocks: left-nested h2..h7 byteswap relations. *)
let spec_to_byteform_7 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5; word_bytereverse cphm] =
       polyval_reduce_prop3
        (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h7))
          (word_pmul (word_bytereverse cph1) (byteswap128 h6)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h5)))
          (word_pmul (word_bytereverse cph3) (byteswap128 h4)))
          (word_pmul (word_bytereverse cph4) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph5) (byteswap128 h2)))
         (word_pmul (word_bytereverse cphm) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`; `word_bytereverse cphm:int128`] GHASH_POLYVAL_ACC_7)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* BYTE_LIST_AT_7BLOCKS: 7-block input-buffer read helper (local to le7). *)
let byte_list_subgoal_tac_w wid base offidx =
  MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) wid) (base--(base+15)) THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
  NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC (ISPECL [`bl:byte list`; offidx] SUB_LIST_16) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;;
let BYTE_LIST_AT_7BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x70 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x20))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x20, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x30))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x30, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x40))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x40, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x50))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x50, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x60))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x60, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ byte_list_subgoal_tac_w `0x70` 0 `pos:num`;
    byte_list_subgoal_tac_w `0x70` 16 `(pos+0x10):num`;
    byte_list_subgoal_tac_w `0x70` 32 `(pos+0x20):num`;
    byte_list_subgoal_tac_w `0x70` 48 `(pos+0x30):num`;
    byte_list_subgoal_tac_w `0x70` 64 `(pos+0x40):num`;
    byte_list_subgoal_tac_w `0x70` 80 `(pos+0x50):num`;
    byte_list_subgoal_tac_w `0x70` 96 `(pos+0x60):num` ]);;

(* ===========================================================================
   PART 2 — cascade resolvers (bound 96+bl1<=112, x5=word(96+bl1)).
   #112 is a BOUNDARY (96+bl1=112 at bl1=16, bl7_resolve_pc_bdy); #96 is TAKEN ->
   more_than_6 (0xfc8 = pc+4040, bl7_resolve_pc96_taken).  (le6 had #96 bdy / #80 taken.)
    
   =========================================================================== *)
let bl7_resolve_pc sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `96 + bl1 <= 112` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`96 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE112) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE112] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf "&(96 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
     [MP_TAC(ASSUME `bl1 <= 16`) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]; ALL_TAC]);;
let bl7_resolve_pc_bdy sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `96 + bl1 <= 112` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`96 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE112) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE112] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC (parse_term (Printf.sprintf "96 + bl1 = %d" k)) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      SUBGOAL_THEN (parse_term (Printf.sprintf "&(96 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
       [MP_TAC(ASSUME `bl1 <= 16`) THEN MP_TAC(ASSUME (parse_term (Printf.sprintf "~(96 + bl1 = %d)" k))) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]]; ALL_TAC]);;
let bl7_resolve_pc96_taken sN target =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s target)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false) then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `word_sub (word (96+bl1):int64) (word 96) = word bl1` (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `val (word bl1:int64) = bl1` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[IVAL_WORD_LE112; ARITH_RULE `bl1 <= 16 ==> bl1 <= 112`; ARITH_RULE `bl1 <= 16 ==> 96 + bl1 <= 112`] THEN
    SUBGOAL_THEN `~(bl1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(96+bl1) - &96:int = &bl1` (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `~(&bl1:int < &0)`];
    ALL_TAC]);;
let dec_bl7_resolve_stale = dec_bl4_resolve_stale;;
let dec_bl7_resolve sN k fall = bl7_resolve_pc sN k fall THEN dec_bl7_resolve_stale;;

(* ===========================================================================
   PART 3 — proof tactics (front / stores / masked-tail / 5-term bridge).
   Step indices are the le4 map shifted by +1 GHASH round for the extra full
   block; the exact ranges were discovered by interactive stepping.
   =========================================================================== *)
let keys15 = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;

(* FRONT: prologue + CTR/AES bulk + cascade to more_than_4 (s297, pc+4156).
   Same bulk as le4 (nfull-independent) with USHR_512/X5_ZERO_LEMMA7 and the
   word(64+bl1) length; the cascade is one rung shorter (fall #112/#96, boundary
   #80, taken #64 -> more_than_4).  ks0..ks3 abbreviated at s269, pt0 captured. *)
let full_le7_tac_front =
  DEC_FRONT_TAC USHR_768_8BL_LEMMA X5_ZERO_LEMMA7 [7] [7;30] 96 6 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (270--270) THEN bl7_resolve_pc_bdy 270 112 3808 THEN dec_bl7_resolve_stale THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (271--282) THEN bl7_resolve_pc96_taken 282 4040 THEN dec_bl7_resolve_stale;;

(* STORES: 5 full plaintext stores pt0..pt4 (pt0@s312, pt1@s320, pt2@s336, pt3@s352,
   pt4@s360; entry more_than_5 @ s290).  UNIFORM DIRECT-ASSERT method (robust to le6's
   more_than_K pipeline offset, and per-step-discard optimized per the tips doc): step all
   the way to s360 with ARM_STEPS_FOLD_DISCARD_TAC (each block-k store readback propagates
   as the clean full aes-tower for out_p+16k, and pt0 = the front's pt0 abbrev), then
   abbrev pt1..pt4 and assert each store readback = pt_k by EXPAND + GCM_CTR_INCk_LANES +
   aes unfold + WORD_BLAST.  No per-block `read Q12` capture (that was the le5 idiom and
   breaks here because le6's extra leading block delays each block's eor3). *)
let full_le7_tac_stores =
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (291--376) THEN
  ABBREV_TAC `pt1:int128 = word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ABBREV_TAC `pt2:int128 = word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ABBREV_TAC `pt3:int128 = word_xor cph3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ABBREV_TAC `pt4:int128 = word_xor cph4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 16))) (s376:armstate) = pt1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt1" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 32))) (s376:armstate) = pt2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt2" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 48))) (s376:armstate) = pt3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt3" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC3_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 64))) (s376:armstate) = pt4` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt4" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC4_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC `pt5:int128 = word_xor cph5 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 80))) (s376:armstate) = pt5` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt5" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC5_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC];;

(* MASKED TAIL (block 5): X1_MOD128_BRIDGE7 after step to s365; masked GHASH round
   366-384; collapse Q9 -> cphm at s384 (pc+4472); block-5 eor3 forms Q12 @ s385, capture
   pt5 = word_xor cph5 (aes256_encrypt (gcm_ctr_inc^5 ctr0) keys) via GCM_CTR_INC6_LANES
   (works because Q5 kept raw — see the front note); masked-blend @ s389; masked store
   readback out_p+80 @ s401 (pc+4540); step to the shared bridge eor v19,v19,v18 -> s408
   (pc+4568).  Uses per-step-discard steppers throughout (tips-doc optimized). *)
let full_le7_tac_tail =
  MP_TAC(SPEC `bl1:num` X1_MOD128_BRIDGE7) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (377--400) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_and cph6 (word (2 EXP (8 * bl1) - 1)):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  REWRITE_TAC[INSERT2_JOIN] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
  (* block-6 eor3 + masked blend form Q12 @ s401 (Q6 kept raw -> full aes tower inline).
     NOTE: the pt5 store (out_p+80) lands at s376, INSIDE the 374--400 window, which is why
     the Q9 mask-collapse is at s400 (pc+4480), +8 vs le6. *)
  ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (401--401) THEN
  ABBREV_TAC `pt6:int128 = word_xor cph6 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor (word_and (pt6:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "pt6" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC6_LANES] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN
    REWRITE_TAC[BLEND_OR_XOR] THEN REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  DISCARD_OLDSTATE_TAC "s401" THEN
  ABBREV_TAC `cphm:int128 = word_and cph6 (word (2 EXP (8 * bl1) - 1))` THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (402--417) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 96))) (s417:armstate) =
       word_xor (word_and (pt6:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 96))) s417` with _ -> false)
       && (try is_comb(rand(concl th)) && fst(dest_const(rator(rator(rand(concl th))))) = "word_xor" with _ -> false)
    then MP_TAC th else NO_TAC) THEN DISCARD_OLDSTATE_TAC "s417" THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (418--422) THEN
  DISCARD_OLDSTATE_TAC "s422";;

(* 7-TERM GHASH bridge: read Q19 s414 = ghash_polyval_acc (bsw h)(brev xi)[brev cph0..cphm].
   GMULT7_FULL_CORRECT_BA (14-arg SPECL incl h7/cphm) + spec_to_byteform_7 (6 hpower
   conjuncts h2..h7) + FIVE machine-side middle mids (cph1.h6, cph2.h5, cph3.h4, cph4.h3,
   cph5.h2); the masked-block mid auto-folds via MERGE.  The folds use the SHARED
   multiplier-keyed FOLD_MID_HPOW from le3block.ml (STEP A of
   _docs/dec-band-homogenization-convergence-plan.md). *)

let BRIDGE_CLOSE_TAC_7 : tactic =
  DEC_BRIDGE_CLOSE_TAC 7 422 GMULT7_FULL_CORRECT_BA spec_to_byteform_7 ALL_TAC;;

(* POST-BRIDGE: assert + close the bridge, then rev64 + st1 xi_p (s423-425),
   ENSURES_FINAL_STATE, MONOTONE_MAYCHANGE.  The final CONV_TAC WORD_BLAST discharges the
   remaining out_p+80 (pt5, 6th full block) postcond: its store readback (raw aes tower)
   equals word_xor cph5 (aes256_encrypt (gcm_ctr_inc^5 ctr0) keys) via GCM_CTR_INC5_LANES.
   Exit pc+4580. *)
let full_le7_tac_bridge =
  SUBGOAL_THEN `read Q19 (s422:armstate) = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5; word_bytereverse cphm]`
    (fun th -> ASSUME_TAC th) THENL [BRIDGE_CLOSE_TAC_7; ALL_TAC] THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let c = concl th in is_eq c && (try lhs c = `read Q19 s422` with _->false) &&
    not(try fst(dest_const(repeat rator (rhs c)))="ghash_polyval_acc" with _->false)) THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5; word_bytereverse cphm]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (423--424) THEN
  DISCARD_OLDSTATE_TAC "s424" THEN
  SUBGOAL_THEN `read Q19 (s424:armstate) = word_bytereverse (gval:int128)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `read Q19 s424` with _ -> false)
      then ACCEPT_TAC(GEN_REWRITE_RULE RAND_CONV [BREV_JOIN_REV8] th) else NO_TAC); ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [425] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BREV_JOIN_REV8] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;


(* ---- LAYER 1: the literal per-block band triple (ARM-sim target).
   bit_len = 512 + 8*bl1, 1<=bl1<=16: four FULL ciphertext blocks 0,1,2,3 + one
   MASKED partial tail block 4.  Input = five per-block ciphertext reads
   cph0..cph4; output = four full plaintext stores + block-4 masked-blend + GHASH tag. ---- *)
let AESV8_GCM_8X_DEC_256_LE7BLOCK_BODY = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 cph2 h3 h3k cph3 h4 cph4 h5 h5k cph5 h6 cph6 h7 h7k.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,112) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,112) (xi_p,16) /\
    nonoverlapping (out_p,112) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,112) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,112) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,112) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,112) (in_p,112) /\
    nonoverlapping (out_p,112) (key_p,240) /\
    nonoverlapping (out_p,112) (htbl_p,192) /\
    nonoverlapping (out_p,112) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    word_subword h3k (64,64) = word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64)) /\
    word_subword h5k (0,64) = word_xor (word_subword h5 (0,64):64 word) (word_subword h5 (64,64)) /\
    word_subword h5k (64,64) = word_xor (word_subword h6 (0,64):64 word) (word_subword h6 (64,64)) /\
    word_subword h7k (0,64) = word_xor (word_subword h7 (0,64):64 word) (word_subword h7 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (768 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             read (memory :> bytes128 in_p) s = cph0 /\
             read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
             read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
             read (memory :> bytes128 (word_add in_p (word 48))) s = cph3 /\
             read (memory :> bytes128 (word_add in_p (word 64))) s = cph4 /\
             read (memory :> bytes128 (word_add in_p (word 80))) s = cph5 /\
             read (memory :> bytes128 (word_add in_p (word 96))) s = cph6 /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 96))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 112))) s = h5k /\
             read (memory :> bytes128 (word_add htbl_p (word 128))) s = h6 /\
             read (memory :> bytes128 (word_add htbl_p (word 144))) s = h7 /\
             read (memory :> bytes128 (word_add htbl_p (word 160))) s = h7k)
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
             word_xor cph4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 80))) s =
             word_xor cph5 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 96))) s =
             word_xor
             (word_and
              (word_xor cph6 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]))
             (word (2 EXP (8 * bl1) - 1)))
             (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
             read (memory :> bytes128 xi_p) s =
             word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
                 word_bytereverse (word_and cph6 (word (2 EXP (8 * bl1) - 1)))]))
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,112); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  full_le7_tac_front THEN full_le7_tac_stores THEN full_le7_tac_tail THEN full_le7_tac_bridge);;

(* ============================================================================
   LAYER 2: the READABLE public theorem AESV8_GCM_8X_DEC_256_LE7BLOCK.
   byte_list_at for BOTH input (80 bytes) and output (64 + bl1 bytes), stated over
   the whole input buffer x via the recursive spec gcm_dec_pt_bytes / gcm_dec_final_xi.
   Proved sim-free from BODY via BYTE_LIST_AT_7BLOCKS (input) and BYTE_LIST_AT_NBLOCK_CTR
   + AES_CTR_7_EL (output).  hyps=0, axioms()=3, no cheats.
   ============================================================================ *)
(* BODY var order: ...cph0 cph1 xi ctr0 k0..k14 h hk h2 outprev bl1 cph2 h3 h3k cph3 h4
   cph4 h5 h5k cph5 h6 cph6 h7 h7k.  Map each cphK to bytes_to_int128 (SUB_LIST (16K,16) x). *)
let le7_body_spec_args =
  [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;`in_p:int64`;`key_p:int64`;`htbl_p:int64`;
   `bytes_to_int128 (SUB_LIST (0,16) (x:byte list))`;
   `bytes_to_int128 (SUB_LIST (16,16) (x:byte list))`;
   `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;
   `k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;
   `h:int128`;`hk:int128`;`h2:int128`;`outprev:int128`;`bl1:num`;
   `bytes_to_int128 (SUB_LIST (32,16) (x:byte list))`;`h3:int128`;`h3k:int128`;
   `bytes_to_int128 (SUB_LIST (48,16) (x:byte list))`;`h4:int128`;
   `bytes_to_int128 (SUB_LIST (64,16) (x:byte list))`;`h5:int128`;`h5k:int128`;
   `bytes_to_int128 (SUB_LIST (80,16) (x:byte list))`;`h6:int128`;
   `bytes_to_int128 (SUB_LIST (96,16) (x:byte list))`;`h7:int128`;`h7k:int128`];;

let AESV8_GCM_8X_DEC_256_LE7BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    x xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 h3 h3k h4 h5 h5k h6 h7 h7k.
    LENGTH x = 112 /\
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,112) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,112) (xi_p,16) /\
    nonoverlapping (out_p,112) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,112) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,112) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,112) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,112) (in_p,112) /\
    nonoverlapping (out_p,112) (key_p,240) /\
    nonoverlapping (out_p,112) (htbl_p,192) /\
    nonoverlapping (out_p,112) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    word_subword h3k (64,64) = word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64)) /\
    word_subword h5k (0,64) = word_xor (word_subword h5 (0,64):64 word) (word_subword h5 (64,64)) /\
    word_subword h5k (64,64) = word_xor (word_subword h6 (0,64):64 word) (word_subword h6 (64,64)) /\
    word_subword h7k (0,64) = word_xor (word_subword h7 (0,64):64 word) (word_subword h7 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (768 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             byte_list_at x in_p (word 112) s /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 96))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 112))) s = h5k /\
             read (memory :> bytes128 (word_add htbl_p (word 128))) s = h6 /\
             read (memory :> bytes128 (word_add htbl_p (word 144))) s = h7 /\
             read (memory :> bytes128 (word_add htbl_p (word 160))) s = h7k)
        (\s. read PC s = word (pc + 4580) /\
             byte_list_at
               (gcm_dec_pt_bytes (96 + bl1) x ctr0
                 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14])
               out_p (word (96 + bl1)) s /\
             read (memory :> bytes128 xi_p) s = gcm_dec_final_xi (96 + bl1) x xi h)
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,112); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[gcm_dec_final_xi; GCM_DEC_GHASH_BLOCKS_7; GCM_DEC_PT_BYTES_7; MAP] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
    (rand(rator(rator(rand(concl(SPECL le7_body_spec_args AESV8_GCM_8X_DEC_256_LE7BLOCK_BODY)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`0`; `x:byte list`; `in_p:int64`; `word 112:int64`; `s:armstate`] BYTE_LIST_AT_7BLOCKS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `val (word 112:int64) = 112` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
      (rand(rator(rand(concl(SPECL le7_body_spec_args AESV8_GCM_8X_DEC_256_LE7BLOCK_BODY))))) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BYTE_LIST_AT_NBLOCK_CTR THEN EXISTS_TAC `outprev:int128` THEN
      REWRITE_TAC[AES_CTR_7_EL] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `val (word (96 + bl1):int64) = 96 + bl1` SUBST1_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ARITH_TAC;
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        X_GEN_TAC `kk:num` THEN REWRITE_TAC[ARITH_RULE `kk < 6 <=> kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3 \/ kk = 4 \/ kk = 5`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0; AES_CTR_7_EL] THEN ASM_REWRITE_TAC[AES_CTR_7_EL];
        REWRITE_TAC[ARITH_RULE `16 * 6 = 96`] THEN ASM_REWRITE_TAC[AES_CTR_7_EL]];
      MATCH_MP_TAC AESV8_GCM_8X_DEC_256_LE7BLOCK_BODY THEN ASM_REWRITE_TAC[]]]);;
