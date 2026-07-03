(* ============================================================================
   AESV8_GCM_8X_DEC_256, the 113-128 byte band (decrypt): bit_len = 896 + 8*bl1,
   1<=bl1<=16.  SEVEN FULL blocks 0..6 (more_than_7/_6/_5/_4/_3/_2/_1, GHASH vs
   H^8,H^7,H^6,H^5,H^4,H^3,H^2) + one MASKED partial block 7 (less_than_1, mask
   MK = word(2 EXP(8*bl1)-1)).  nfull = 7.  Mirror of le7block with one extra full
   middle block + the 8-term GHASH bridge.  bl1=16 endpoint = whole-8-block (128B).

   Two-layer structure (BODY = literal per-block triple; LE8BLOCK = readable byte_list_at
   wrapper for in 128B / out 112+bl1).  Cascade x5=112+bl1: #112 is STRICT TAKEN (no
   boundary rung — 112+bl1>112 for all bl1>=1), -> more_than_7 (0xf98 = pc+3992).  All 7
   full plaintext stores complete before the masked block 7; masked block 7 uses Q7 kept
   RAW (front discard [] then [30], so no keystream register is abbreviated away for block 7)
   so the pt7 blend-capture closes by WORD_BLAST.  8-term GHASH bridge; exit pc+4580.
   H-power htable: h7@htbl+144, h7k@htbl+160, h8@htbl+176 (full 192B = 12 slots exactly).
   All stepping uses the per-step-discard steppers (tips-doc).  All hyps=0, axioms()=3,
   no CHEAT_TAC, no new axioms.
   ============================================================================ *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_le7block.ml";;
needs "arm/proofs/utils/aes_gcm_dec_spec.ml";;
needs "common/gmult_nblock_lemmas.ml";;

(* ===========================================================================
   PART 0 — the GMULT8 bridge lemma (instant via the shared fast GMULTn builder).
   =========================================================================== *)

let PACK8_ID, GMULT8_FULL_CORRECT_BA = build_GMULTn_fast 8;;

(* ===========================================================================
   PART 1 — LE8BLOCK cascade/counter helper lemmas (bound 64+bl1<=80, x5=word(64+bl1)).
   =========================================================================== *)

let USHR_896_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (896 + 8 * bl1):int64) 3 = word (112 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (896 + 8 * bl1):int64) = 896 + 8 * bl1` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let X5_ZERO_LEMMA8 = prove
 (`!bl1. 1 <= bl1 /\ bl1 <= 16 ==> word_and (word_sub (word (112 + bl1)) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [WORD_RULE `word_sub (word (112 + bl1):int64) (word 1) = word (111 + bl1)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `j < 7` THENL
   [REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `~bit j (word 18446744073709551488:int64)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `j < 7` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[BIT_WORD] THEN
    SUBGOAL_THEN `111 + bl1 < 2 EXP j` (fun th -> SIMP_TAC[th; DIV_LT; ODD; DE_MORGAN_THM]) THEN
    TRANS_TAC LTE_TRANS `2 EXP 7` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;

let X1_MOD128_BRIDGE8 = prove
 (`!bl1. bl1 <= 16 ==> word_and (word (896 + 8 * bl1):int64) (word 127) = word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (896 + 8 * bl1):int64) = 896 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `896 + 8 * bl1 = 8 * bl1 + 7 * 128`] THEN REWRITE_TAC[MOD_MULT_ADD]);;

let IVAL_WORD_LE128 = prove
 (`!b. b <= 128 ==> ival (word b:int64) = &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival] THEN
  SUBGOAL_THEN `val (word b:int64) = b` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_SIMP_TAC[ARITH_RULE `b <= 128 ==> b < 2 EXP (64 - 1)`]);;

let IVAL_WSUB_LE128 = prove
 (`!b k. b <= 128 /\ k <= 128 ==> ival (word_sub (word b) (word k):int64) = &b - &k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let GCM_CTR_INC7_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))`,
        subst [`word 7:32 word`, `word 1:32 word`] (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let AES_CTR_8_EL = prove
 (`EL 0 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6;pt7] keys) = word_xor pt0 (aes256_encrypt ctr0 keys) /\
   EL 1 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6;pt7] keys) = word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys) /\
   EL 2 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6;pt7] keys) = word_xor pt2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) keys) /\
   EL 3 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6;pt7] keys) = word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) keys) /\
   EL 4 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6;pt7] keys) = word_xor pt4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))) keys) /\
   EL 5 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6;pt7] keys) = word_xor pt5 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))) keys) /\
   EL 6 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6;pt7] keys) = word_xor pt6 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))) keys) /\
   EL 7 (aes_ctr ctr0 [pt0;pt1;pt2;pt3;pt4;pt5;pt6;pt7] keys) = word_xor pt7 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))) keys)`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; ARITH_RULE `2 = SUC(SUC 0)`; ARITH_RULE `3 = SUC(SUC(SUC 0))`;
              ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; ARITH_RULE `5 = SUC(SUC(SUC(SUC(SUC 0))))`;
              ARITH_RULE `6 = SUC(SUC(SUC(SUC(SUC(SUC 0)))))`; ARITH_RULE `7 = SUC(SUC(SUC(SUC(SUC(SUC(SUC 0))))))`; EL; HD; TL] THEN
  REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_INC_ITER_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[gcm_ctr_inc_iter]);;

let GHASH_POLYVAL_ACC_8 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128) (w:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v; w] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul v (polyval_dot h h) : 256 word)
        (word_pmul w h : 256 word))))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v; w]`; `a:int128`; `p:int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

let spec_to_byteform_8 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h8 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5; word_bytereverse cph6; word_bytereverse cphm] =
       polyval_reduce_prop3
        (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h8))
          (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
          (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
          (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
          (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
         (word_pmul (word_bytereverse cphm) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`; `word_bytereverse cph6:int128`; `word_bytereverse cphm:int128`] GHASH_POLYVAL_ACC_8)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

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
let BYTE_LIST_AT_8BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s ==> LENGTH bl = val len ==> pos + 0x80 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s = bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s = bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x20))) s = bytes_to_int128 (SUB_LIST (pos + 0x20, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x30))) s = bytes_to_int128 (SUB_LIST (pos + 0x30, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x40))) s = bytes_to_int128 (SUB_LIST (pos + 0x40, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x50))) s = bytes_to_int128 (SUB_LIST (pos + 0x50, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x60))) s = bytes_to_int128 (SUB_LIST (pos + 0x60, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x70))) s = bytes_to_int128 (SUB_LIST (pos + 0x70, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN REPEAT STRIP_TAC THENL
  [ byte_list_subgoal_tac_w `0x80` 0 `pos:num`; byte_list_subgoal_tac_w `0x80` 16 `(pos+0x10):num`;
    byte_list_subgoal_tac_w `0x80` 32 `(pos+0x20):num`; byte_list_subgoal_tac_w `0x80` 48 `(pos+0x30):num`;
    byte_list_subgoal_tac_w `0x80` 64 `(pos+0x40):num`; byte_list_subgoal_tac_w `0x80` 80 `(pos+0x50):num`;
    byte_list_subgoal_tac_w `0x80` 96 `(pos+0x60):num`; byte_list_subgoal_tac_w `0x80` 112 `(pos+0x70):num` ]);;

let bl8_resolve_pc112_taken sN target =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s target)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false) then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `word_sub (word (112+bl1):int64) (word 112) = word bl1` (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `val (word bl1:int64) = bl1` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[IVAL_WORD_LE128; ARITH_RULE `bl1 <= 16 ==> bl1 <= 128`; ARITH_RULE `bl1 <= 16 ==> 112 + bl1 <= 128`] THEN
    SUBGOAL_THEN `~(bl1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(112+bl1) - &112:int = &bl1` (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `~(&bl1:int < &0)`]; ALL_TAC]);;
let dec_bl8_resolve_stale = dec_bl5_resolve_stale;;

let keys15 = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;

(* Keep-GHASH-accumulator stepper: like ARM_STEPS_FOLD_DISCARD_TAC but NEVER discards reads of
   Q16/Q17/Q18/Q19 (the GHASH low/high/mid accumulator lanes).  In the whole-8 (nfull=7) band the
   7 full-block GHASH rounds run INSIDE the stores window (271--392); the plain per-step discard
   drops Q18's carry (it isn't written on the final store steps), leaving `read Q18 s400` opaque in
   the tail bridge.  Keeping Q16-Q19 alive across the window makes the tail's Q18/Q19 close to a
   full closed word term so the 8-term bridge can proceed.  (Q18 s392 present+closed with this;
   ABSENT with ARM_STEPS_FOLD_DISCARD_TAC.) *)
let DISCARD_OLDSTATE_KEEPGH_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;
let ARM_STEPS_FOLD_KEEPGH_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_OLDSTATE_KEEPGH_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* Predicate to DISCARD the GHASH-accumulator reads for states BEFORE s374 (once the blocks-0-6 mid
   at s374 has been captured as `midacc`).  Keeps the hyp pile bounded (~546 -> ~143) while retaining
   the midacc definition (a var-eqn, not a state-read).  See the midacc-capture note below. *)
let discard_ghreg_before_374 (thm:thm) =
  let rec find_read t = match t with
      Comb(Comb(Const("read",_),cmp),st) ->
        (match cmp with Const(n,_) when (n="Q16"||n="Q17"||n="Q18"||n="Q19") ->
           (match st with Var(sn,_) when String.length sn>1 && sn.[0]='s' ->
              (try int_of_string(String.sub sn 1 (String.length sn-1)) < 374 with _ -> false)
            | _ -> false)
         | _ -> false)
    | Comb(a,b) -> find_read a || find_read b | Abs(_,b) -> find_read b | _ -> false in
  find_read (concl thm);;

let full_le8_tac_front =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (1--5) THEN
  MP_TAC(SPEC `bl1:num` USHR_896_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 []) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (31--84) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (85--173) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (174--177) THEN GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (178--184) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (185--254) THEN mk_discard2 [30] THEN GCM_SIMD_SIMPLIFY_TAC THEN
  MP_TAC(SPEC `bl1:num` X5_ZERO_LEMMA8) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [255] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (256--265) THEN mk_discard2 [30] THEN
  MP_TAC(SPEC `bl1:num` USHR_896_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub (word_add in_p (word (112 + bl1):int64)) in_p = word (112 + bl1)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (266--269) THEN
  ABBREV_TAC `ks0:int128 = read Q0 s269` THEN ABBREV_TAC `ks1:int128 = read Q1 s269` THEN
  ABBREV_TAC `ks2:int128 = read Q2 s269` THEN ABBREV_TAC `ks3:int128 = read Q3 s269` THEN
  ABBREV_TAC `ks4:int128 = read Q4 s269` THEN ABBREV_TAC `ks5:int128 = read Q5 s269` THEN
  ABBREV_TAC `ks6:int128 = read Q6 s269` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt0:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (270--270) THEN bl8_resolve_pc112_taken 270 3992 THEN dec_bl8_resolve_stale;;

(* STORES: 7 full plaintext stores pt0..pt6 (out_p+0..+96); entry more_than_7 @ s270.
   le8 = le7 + one more full block, and #112 is STRICT TAKEN (no boundary), so the whole
   store cadence shifts: all 7 full stores complete by **s392 (pc+4480)** as ONE
   ARM_STEPS_FOLD_DISCARD window (291--392) — and at s392 the machine has ALREADY executed
   the block-7 mask (and v9,v9,v0 @ 0x1174) and blend (bif v12,v26,v0 @ 0x117c), so Q9 s392 =
   word_and(rawmask) cph7 and Q12 s392 = the masked blend.  UNIFORM DIRECT-ASSERT: after the
   fold-discard, abbrev pt1..pt6 and assert each store readback = pt_k via EXPAND +
   GCM_CTR_INCk_LANES + aes unfold + WORD_BLAST (pt0 = front's pt0 abbrev). The masked block-7
   handling (X1_MOD128, Q9->cphm, pt7 capture) is done in full_le8_tac_tail starting AT s392. *)
let full_le8_tac_stores =
  (* MIDACC-CAPTURE: KEEPGH to s374 (the LAST v18 mid-write, blocks-0-6 GHASH mid), abbreviate
     midacc = read Q18 s374 (the expanded 15-pmul blocks-0-6 mid), then DISCARD the pre-s374 GHASH
     reads (hyp pile 546 -> 143, midacc def survives), then KEEPGH the rest of the stores window
     375-392.  This materializes the machine's carried GHASH mid so the reduced Q19 at the bridge is
     a CLOSED word term (no opaque `read Q18 s400`).  Without this the whole-8 tail cannot resolve the
     main-loop mid.  See the multi-session root-cause in project_le8block_wip memory. *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_EXEC (271--374) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s374` THEN
  DISCARD_ASSUMPTIONS_TAC discard_ghreg_before_374 THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_EXEC (375--392) THEN
  ABBREV_TAC `pt1:int128 = word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ABBREV_TAC `pt2:int128 = word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ABBREV_TAC `pt3:int128 = word_xor cph3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ABBREV_TAC `pt4:int128 = word_xor cph4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ABBREV_TAC `pt5:int128 = word_xor cph5 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ABBREV_TAC `pt6:int128 = word_xor cph6 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 16))) (s392:armstate) = pt1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt1" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 32))) (s392:armstate) = pt2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt2" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 48))) (s392:armstate) = pt3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt3" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC3_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 64))) (s392:armstate) = pt4` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt4" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC4_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 80))) (s392:armstate) = pt5` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt5" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC5_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 96))) (s392:armstate) = pt6` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt6" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC6_LANES] THEN ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; ALL_TAC];;

(* MASKED TAIL (block 7).  Entry state s392 (pc+4480): all 7 full stores done; machine has
   ALREADY masked v9 (0x1174) and blended v12 (0x117c), so Q9 s392 = word_and(rawmask) cph7 and
   Q12 s392 = the blend.  Sequence (validated live): X1_MOD128_BRIDGE8; collapse Q9 -> word_and
   cph7 mask (SPEC + MASK_LEMMA + WORD_RULE); abbrev pt7 = word_xor cph7 (aes256_encrypt
   (gcm_ctr_inc^7 ctr0) keys); capture Q12 = masked blend via GCM_CTR_INC7_LANES + MASK_LEMMA +
   BLEND_OR_XOR; DISCARD s392; abbrev cphm = word_and cph7 mask; step 393->414 (masked GHASH
   round + masked store out_p+112 @ s410 (pc+4552)); the final MODULO folds into v19: the reduced
   GHASH accumulator is **read Q19 s415** (right after `eor v19,v19,v18` @ pc+4568; whole-8 analog of
   le7's read Q19 s422). rev64 v19 @ s416 (pc+4572); st1 {v19},[x3] @ s417 (pc+4576, exit pc+4580).
   Q14 s414 is the karatsuba tidy `v14 = v17^v19` (a pre-fold intermediate) — a RED HERRING, NOT the
   target. KEEPGH (keep Q16/Q17/Q18/Q19 through the tail) is REQUIRED so read Q19 s415 survives the
   eor (plain fold-discard drops it via the s410-store old-state boundary).
   *** REMAINING BLOCKER (precisely diagnosed): at the read-Q19-s415 bridge, the prefix (16-arg
   GMULT8 spec_eq over h2..h8 + ABBREV_INNER_PMULS + MERGE_2BLK) reaches a BALANCED 5-vs-5 pmul state;
   FOLD_MID is unnecessary (SKIP it) and WA_UNIFY_TAC succeeds. The ONLY residual is the WV hi/low
   lane fact  read Q18 s400 = qq28 xor qq29 xor qq30 xor qq31 xor qq32 xor qq33 xor qq40  (the machine
   carried-in GHASH mid for blocks 0-6 = XOR of the 7 spec block-mid pmuls). read Q18 s400 is OPAQUE:
   Q18 is first written at s401; its s400 value is the MAIN 8-block GHASH-LOOP mid, computed and then
   DISCARDED in the front/stores. WV_UNIFY_TAC's monolithic BITBLAST on this times out. FIX (next
   session): preserve the main-loop mid (Q18) EXPANDED through the stores window (271-392) so read Q18
   s400 becomes a concrete pmul tree that matches the qq mids by PMUL_CONG; then WV lane closes.
   le8 (whole-8) is the ONLY band that runs the main 8-block loop before the tail, which is why le1..le7
   never hit this. Full diagnosis + validated pipeline in project_le8block_wip memory. *)
let full_le8_tac_tail =
  MP_TAC(SPEC `bl1:num` X1_MOD128_BRIDGE8) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_and cph7 (word (2 EXP (8 * bl1) - 1)):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  REWRITE_TAC[INSERT2_JOIN] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
  ABBREV_TAC `pt7:int128 = word_xor cph7 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))) [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor (word_and (pt7:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "pt7" THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC7_LANES] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN
    REWRITE_TAC[BLEND_OR_XOR] THEN REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  DISCARD_OLDSTATE_TAC "s392" THEN
  ABBREV_TAC `cphm:int128 = word_and cph7 (word (2 EXP (8 * bl1) - 1))` THEN
  (* Tail 393-414 MUST use the keep-GHASH stepper (Q16/Q17/Q18/Q19 never discarded), NOT
     ARM_STEPS_FOLD_DISCARD: the machine GHASH mid accumulator Q18 (read Q18 s400 = the full-blocks
     0..6 mid sum, set ~s392) is referenced by the reduced Q19 s414; a discarding stepper drops it
     -> `read Q18 s400` stays opaque -> the WV bridge lane has an unresolvable residual.  KEEPGH
     preserves Q18 s400..s414 (and Q19 = the machine-reduced value with its Wpmul) so the bridge
     WV lane's residual (read Q18 s400 <-> the qq28..qq40 mid-sum) cancels and the lane closes. *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_EXEC (393--409) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 112))) (s409:armstate) =
       word_xor (word_and (pt7:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 112))) s409` with _ -> false)
       && (try is_comb(rand(concl th)) && fst(dest_const(rator(rator(rand(concl th))))) = "word_xor" with _ -> false)
    then MP_TAC th else NO_TAC) THEN DISCARD_OLDSTATE_TAC "s409" THEN DISCH_TAC THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_EXEC (410--414);;

(* 8-TERM GHASH bridge: read Q19 s414 = ghash_polyval_acc (bsw h)(brev xi)[brev cph0..cph6; brev cphm].
   *** BRIDGE STATE IS s414, NOT s415. *** objdump: 0x11d4(pc+4564)=`eor v19,v19,v18` (final fold);
   0x11d8(pc+4568)=`ext v19,v19,v19,#8` (byte-rotate = 64-bit HALF-SWAP); 0x11dc(pc+4572)=`rev64 v19`;
   0x11e0(pc+4576)=`st1`.  At s414 PC=pc+4568, so read Q19 s414 = post-eor / PRE-ext = the clean
   ghash accumulator (matches le7's convention).  read Q19 s415 = POST-ext = swap_halves(ghash) — a
   64-bit lane transposition (this off-by-one was the multi-session "half-swap" blocker).  The ext +
   rev64 are handled POST-bridge (s415,s416) via BREV_JOIN_REV8 = word_bytereverse.

   FOLD_MID_HPOW keys on the pmul's MULTIPLIER (2nd arg = h-power key), NOT find_term over the whole
   pmul (whose INPUT carries lower h-powers in the whole-8 karatsuba).  The block-1 machine mid (qq39)
   carries a stale `ins v18.d[0]` k13 high-half; QQ39_FIX_TAC establishes qq39=qq28 (clean spec mid)
   via the k13-kill rewrites so WV_UNIFY's inputs become bit-equal.  See project_le8block_wip memory.
   pmul_mult_hpow / is_pmul128_tm / LE8_K13_FIX / FOLD_MID_HPOW / QQ39_FIX_TAC are SHARED machinery,
   defined in le3block.ml (STEP A of _docs/dec-band-homogenization-convergence-plan.md). *)

let BRIDGE_CLOSE_TAC_8 : tactic = fun (asl,w) ->
  let ha n = snd(List.find(fun(_,th)->try lhs(concl th)=parse_term(Printf.sprintf "byteswap128 %s" n) with _->false) asl) in
  let q19asm = snd(List.find(fun(_,th)->try lhs(concl th)=`read Q19 s414` with _->false) asl) in
  let gmult8_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h8:int128`;
            `word_bytereverse cph1:int128`; `byteswap128 h7:int128`;
            `word_bytereverse cph2:int128`; `byteswap128 h6:int128`;
            `word_bytereverse cph3:int128`; `byteswap128 h5:int128`;
            `word_bytereverse cph4:int128`; `byteswap128 h4:int128`;
            `word_bytereverse cph5:int128`; `byteswap128 h3:int128`;
            `word_bytereverse cph6:int128`; `byteswap128 h2:int128`;
            `word_bytereverse cphm:int128`; `byteswap128 h:int128`] GMULT8_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_8 (end_itlist CONJ [ha "h2";ha "h3";ha "h4";ha "h5";ha "h6";ha "h7";ha "h8"])) (GSYM gmult8_dec) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   FOLD_MID_HPOW "H6" THEN FOLD_MID_HPOW "H5" THEN FOLD_MID_HPOW "H4" THEN
   FOLD_MID_HPOW "H3" THEN FOLD_MID_HPOW "H2" THEN
   WA_UNIFY_TAC THEN QQ39_FIX_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC)
  (asl,w);;

(* POST-BRIDGE: assert + close the bridge (read Q19 s414 = ghash), then ext + rev64 (s415,s416) =
   word_bytereverse via BREV_JOIN_REV8, then st1 xi_p (s417).  ENSURES_FINAL_STATE, MONOTONE_MAYCHANGE.
   Exit pc+4580. *)
let full_le8_tac_bridge =
  SUBGOAL_THEN `read Q19 (s414:armstate) = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5; word_bytereverse cph6; word_bytereverse cphm]`
    (fun th -> ASSUME_TAC th) THENL [BRIDGE_CLOSE_TAC_8; ALL_TAC] THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let c = concl th in is_eq c && (try lhs c = `read Q19 s414` with _->false) &&
    not(try fst(dest_const(repeat rator (rhs c)))="ghash_polyval_acc" with _->false)) THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5; word_bytereverse cph6; word_bytereverse cphm]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (415--416) THEN
  DISCARD_OLDSTATE_TAC "s416" THEN
  SUBGOAL_THEN `read Q19 (s416:armstate) = word_bytereverse (gval:int128)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `read Q19 s416` with _ -> false)
      then ACCEPT_TAC(GEN_REWRITE_RULE RAND_CONV [BREV_JOIN_REV8] th) else NO_TAC); ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [417] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BREV_JOIN_REV8] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;


(* ---- LAYER 1: the literal per-block band triple (ARM-sim target).
   bit_len = 896 + 8*bl1, 1<=bl1<=16: SEVEN FULL ciphertext blocks 0..6 + one
   MASKED partial tail block 7.  Input = eight per-block ciphertext reads
   cph0..cph7; output = seven full plaintext stores + block-7 masked-blend + GHASH tag. ---- *)
let AESV8_GCM_8X_DEC_256_LE8BLOCK_BODY = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 cph2 h3 h3k cph3 h4 cph4 h5 h5k cph5 h6 cph6 h7 h7k cph7 h8.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,128) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,128) (xi_p,16) /\
    nonoverlapping (out_p,128) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,128) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,128) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,128) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,128) (in_p,128) /\
    nonoverlapping (out_p,128) (key_p,240) /\
    nonoverlapping (out_p,128) (htbl_p,192) /\
    nonoverlapping (out_p,128) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h8 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    word_subword h3k (64,64) = word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64)) /\
    word_subword h5k (0,64) = word_xor (word_subword h5 (0,64):64 word) (word_subword h5 (64,64)) /\
    word_subword h5k (64,64) = word_xor (word_subword h6 (0,64):64 word) (word_subword h6 (64,64)) /\
    word_subword h7k (0,64) = word_xor (word_subword h7 (0,64):64 word) (word_subword h7 (64,64)) /\
    word_subword h7k (64,64) = word_xor (word_subword h8 (0,64):64 word) (word_subword h8 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (896 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             read (memory :> bytes128 in_p) s = cph0 /\
             read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
             read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
             read (memory :> bytes128 (word_add in_p (word 48))) s = cph3 /\
             read (memory :> bytes128 (word_add in_p (word 64))) s = cph4 /\
             read (memory :> bytes128 (word_add in_p (word 80))) s = cph5 /\
             read (memory :> bytes128 (word_add in_p (word 96))) s = cph6 /\
             read (memory :> bytes128 (word_add in_p (word 112))) s = cph7 /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 112))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 160))) s = h7k /\
             read (memory :> bytes128 (word_add htbl_p (word 176))) s = h8)
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
             word_xor cph6 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 112))) s =
             word_xor
             (word_and
              (word_xor cph7 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]))
             (word (2 EXP (8 * bl1) - 1)))
             (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
             read (memory :> bytes128 xi_p) s =
             word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5; word_bytereverse cph6;
                 word_bytereverse (word_and cph7 (word (2 EXP (8 * bl1) - 1)))]))
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,128); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  full_le8_tac_front THEN full_le8_tac_stores THEN full_le8_tac_tail THEN full_le8_tac_bridge);;

(* ============================================================================
   LAYER 2: the READABLE public theorem AESV8_GCM_8X_DEC_256_LE8BLOCK.
   byte_list_at for BOTH input (80 bytes) and output (64 + bl1 bytes), stated over
   the whole input buffer x via the recursive spec gcm_dec_pt_bytes / gcm_dec_final_xi.
   Proved sim-free from BODY via BYTE_LIST_AT_8BLOCKS (input) and BYTE_LIST_AT_NBLOCK_CTR
   + AES_CTR_8_EL (output).  hyps=0, axioms()=3, no cheats.
   ============================================================================ *)
(* BODY var order: ...cph0 cph1 xi ctr0 k0..k14 h hk h2 outprev bl1 cph2 h3 h3k cph3 h4
   cph4 h5 h5k cph5 h6 cph6 h7 h7k.  Map each cphK to bytes_to_int128 (SUB_LIST (16K,16) x). *)
let le8_body_spec_args =
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
   `bytes_to_int128 (SUB_LIST (96,16) (x:byte list))`;`h7:int128`;`h7k:int128`;
   `bytes_to_int128 (SUB_LIST (112,16) (x:byte list))`;`h8:int128`];;

let AESV8_GCM_8X_DEC_256_LE8BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    x xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 h3 h3k h4 h5 h5k h6 h7 h7k h8.
    LENGTH x = 128 /\
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,128) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,128) (xi_p,16) /\
    nonoverlapping (out_p,128) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,128) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,128) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,128) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,128) (in_p,128) /\
    nonoverlapping (out_p,128) (key_p,240) /\
    nonoverlapping (out_p,128) (htbl_p,192) /\
    nonoverlapping (out_p,128) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h8 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
    word_subword h3k (64,64) = word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64)) /\
    word_subword h5k (0,64) = word_xor (word_subword h5 (0,64):64 word) (word_subword h5 (64,64)) /\
    word_subword h5k (64,64) = word_xor (word_subword h6 (0,64):64 word) (word_subword h6 (64,64)) /\
    word_subword h7k (0,64) = word_xor (word_subword h7 (0,64):64 word) (word_subword h7 (64,64)) /\
    word_subword h7k (64,64) = word_xor (word_subword h8 (0,64):64 word) (word_subword h8 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (896 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             byte_list_at x in_p (word 128) s /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 112))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 160))) s = h7k /\
             read (memory :> bytes128 (word_add htbl_p (word 176))) s = h8)
        (\s. read PC s = word (pc + 4580) /\
             byte_list_at
               (gcm_dec_pt_bytes (112 + bl1) x ctr0
                 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14])
               out_p (word (112 + bl1)) s /\
             read (memory :> bytes128 xi_p) s = gcm_dec_final_xi (112 + bl1) x xi h)
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,128); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[gcm_dec_final_xi; GCM_DEC_GHASH_BLOCKS_8; GCM_DEC_PT_BYTES_8; MAP] THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
    (rand(rator(rator(rand(concl(SPECL le8_body_spec_args AESV8_GCM_8X_DEC_256_LE8BLOCK_BODY)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`0`; `x:byte list`; `in_p:int64`; `word 128:int64`; `s:armstate`] BYTE_LIST_AT_8BLOCKS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `val (word 128:int64) = 128` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
      (rand(rator(rand(concl(SPECL le8_body_spec_args AESV8_GCM_8X_DEC_256_LE8BLOCK_BODY))))) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BYTE_LIST_AT_NBLOCK_CTR THEN EXISTS_TAC `outprev:int128` THEN
      REWRITE_TAC[AES_CTR_8_EL] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `val (word (112 + bl1):int64) = 112 + bl1` SUBST1_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ARITH_TAC;
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        X_GEN_TAC `kk:num` THEN REWRITE_TAC[ARITH_RULE `kk < 7 <=> kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3 \/ kk = 4 \/ kk = 5 \/ kk = 6`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0; AES_CTR_8_EL] THEN ASM_REWRITE_TAC[AES_CTR_8_EL];
        REWRITE_TAC[ARITH_RULE `16 * 7 = 112`] THEN ASM_REWRITE_TAC[AES_CTR_8_EL]];
      MATCH_MP_TAC AESV8_GCM_8X_DEC_256_LE8BLOCK_BODY THEN ASM_REWRITE_TAC[]]]);;
