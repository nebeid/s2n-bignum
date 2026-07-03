(* ============================================================================
   AESV8_GCM_8X_DEC_256, the 33-47 byte band (decrypt): bit_len = 256 + 8*bl1,
   1<=bl1<=16.  TWO FULL blocks 0,1 (more_than_2 / more_than_1, GHASH vs H^3, H^2)
   + one MASKED partial block 2 (less_than_1, symbolic mask MK = word(2 EXP(8*bl1)-1)).
   nfull = 2.  Decrypt analog, mirrors aesv8_gcm_8x_dec_256_le2block.ml with one extra
   full middle block + the 3-term GHASH bridge.

   Requires arm/proofs/aesv8_gcm_8x_dec_256_le2block.ml loaded (EXEC rule, MERGE_2BLK,
   the dec masked-tail machinery, BYTE_LIST_AT_NBLOCK_CTR, the common nblock GHASH layer
   with PMUL_KARATSUBA / GMULT_REDUCE_PROP3 / KARATSUBA_LIMBS / GHASH_POLYVAL_ACC_3, and
   the XTS byte-list substrate READ_BYTES_AND_BYTE128_MERGE / SUB_LIST_LENGTH_IMPLIES).

   Two-layer structure (mirrors Mila PR #417's _CONCRETE / _ABS split; both triples
   are written out EXPLICITLY in source — no goal-surgery builders):
     - GMULT3_FULL_CORRECT_BA              : the 3-block fused multiply+reduce bridge lemma.
     - AESV8_GCM_8X_DEC_256_LE3BLOCK_BODY  : LAYER 1, the literal per-block band triple
         (per-block cphk reads in / per-block plaintext stores + GHASH out); the ARM
         simulation target (concrete int128 lanes).  Proved by the ~780s simulation.
     - INPUT_BYTES_TO_BYTE128_LANES / INPUT_BYTES_FULL / INPUT_BRIDGE_3 : the input
         byte_list_at -> per-block lane-read bridge (reusable, ARM-free).
     - AESV8_GCM_8X_DEC_256_LE3BLOCK       : LAYER 2, the READABLE public theorem with
         byte_list_at for BOTH input and output (XTS / Mila presentation).  Derived
         sim-free from BODY via INPUT_BRIDGE_3 (input) and BYTE_LIST_AT_NBLOCK_CTR +
         AES_CTR_3_EL (output), through ENSURES_PRE/POSTCONDITION_THM.
   All hyps=0, axioms()=3, no cheats.

   THE KEY INSIGHT (root cause of ~8 prior failed attempts): the GHASH bridge must be
   taken at s381 = pc+4568 (AFTER the `eor v19,v19,v18` at 0x11d4), NOT s380.  At s380 the
   register Q19 is the INCOMPLETE reduced value (missing the v18 high-reduction term), so the
   bridge goal is subtly false and every close diverges.  At s381 the close goes through:
   spec -> GMULT3-byteform; ABBREV_INNER_PMULS + MERGE_2BLK (share products); fold qq8; unify
   the two W-rounds (wa by PMUL_CONG, wv by a ~1.8s BITBLAST input-equality); abbreviate both
   W-pmuls opaque; QQ0SPLIT + JOIN_EQ_SPLIT; each 64-bit lane closes by subword normalization
   + SJ_COLLAPSE + bubble_fix (XOR-AC canonicalise, ported from Mila's gcm_aesgcm_nblock_helpers).

   No CHEAT_TAC, no new axioms.

   VERIFIED loadt-clean from a fresh checkpoint (all theorems hyps=0, axioms()=3;
   cost ~ le2block dep + PACK3_ID ~373s + the BODY ARM sim ~780s; the LAYER 2
   readable theorem is sim-free, ~0.2s).
   ============================================================================ *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_le2block.ml";;
(* Recursive whole-buffer decrypt spec (the dec analogue of Mila's gcm_ghash_blocks/
   gcm_final_xi) + per-N unfold lemmas; the readable LAYER 2 wrapper states its
   postcondition over the whole buffer x via gcm_dec_pt_bytes / gcm_dec_final_xi. *)
needs "arm/proofs/utils/aes_gcm_dec_spec.ml";;

(* ===========================================================================
   PART 1 — GMULT3 machinery (3-block fused multiply+reduce).
   GMULT3_FULL_CORRECT_BA is now built INSTANTLY by the shared fast GMULTn builder
   (common/gmult_nblock_lemmas.ml) — ~0.2s vs the old ~373s monolithic
   CONV_TAC WORD_RULE PACK3_ID on a 256-bit term.  The build reproduces the old
   hand-written dec3_tL + PACK3_ID derivation's concl EXACTLY.
   =========================================================================== *)

needs "common/gmult_nblock_lemmas.ml";;

let PACK3_ID, GMULT3_FULL_CORRECT_BA = build_GMULTn_fast 3;;

(* ---- nfull=2 band helper lemmas (all proven in session) ---- *)

let USHR_256_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (256 + 8 * bl1):int64) 3 = word (32 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (256 + 8 * bl1):int64) = 256 + 8 * bl1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let X5_ZERO_LEMMA3 = prove
 (`!bl1. 1 <= bl1 /\ bl1 <= 16
        ==> word_and (word_sub (word (32 + bl1)) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [WORD_RULE `word_sub (word (32 + bl1):int64) (word 1) = word (31 + bl1)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `j < 7` THENL
   [REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `~bit j (word 18446744073709551488:int64)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `j < 7` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[BIT_WORD] THEN
    SUBGOAL_THEN `31 + bl1 < 2 EXP j` (fun th -> SIMP_TAC[th; DIV_LT; ODD; DE_MORGAN_THM]) THEN
    TRANS_TAC LTE_TRANS `2 EXP 7` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;

let IVAL_WORD_LE48 = prove
 (`!b. b <= 48 ==> ival (word b:int64) = &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival] THEN
  SUBGOAL_THEN `val (word b:int64) = b` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  ASM_SIMP_TAC[ARITH_RULE `b <= 48 ==> b < 2 EXP (64 - 1)`]);;

let IVAL_WSUB_LE48 = prove
 (`!b k. b <= 48 /\ k <= 112
          ==> ival (word_sub (word b) (word k):int64) = &b - &k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let X1_MOD128_BRIDGE3 = prove
 (`!bl1. bl1 <= 16
    ==> word_and (word (256 + 8 * bl1):int64) (word 127) =
        word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (256 + 8 * bl1):int64) = 256 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 + 8 * bl1 = 8 * bl1 + 2 * 128`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* gcm_ctr_inc applied twice = the lane form with `word 2` (block-2 counter). *)
let GCM_CTR_INC2_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc ctr0)`,
        subst [`word 2:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

(* spec-side fold: ghash_polyval_acc 3-block spec = prop3 of the H-power pmul-sum,
   under the h2/h3 byteswap128 relations.  Pairs with GMULT3 (GSYM gmult3_dec). *)
let spec_to_byteform = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h))
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cphm] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h3))
          (word_pmul (word_bytereverse cph1) (byteswap128 h2)))
         (word_pmul (word_bytereverse cphm) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cphm:int128`] GHASH_POLYVAL_ACC_3)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ===========================================================================
   PART 2 — helper lemmas, bridge-close machinery, LAYER 1 (explicit BODY) proof.
   =========================================================================== *)


(* ---- helper lemmas ---- *)
let SJ_COLLAPSE = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (0,64):64 word
                = word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let SJ_COLLAPSE2 = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (64,64):64 word
                = word_subword w (0,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let BREV_JOIN_REV8 = prove
 (`!w:int128. word_join (word_reversefields 8 (word_subword w (0,64):64 word):64 word)
                        (word_reversefields 8 (word_subword w (64,64):64 word):64 word):int128
              = word_bytereverse w`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ---- XOR-AC canonicaliser (ported from Mila's gcm_aesgcm_nblock_helpers.ml) ---- *)
let word_xor_left_comm = WORD_RULE `word_xor (a:64 word) (word_xor b c) = word_xor b (word_xor a c)`;;
let xor_pair_comm = WORD_RULE `word_xor (a:64 word) b = word_xor b a`;;
let term_leq t1 t2 = String.compare (string_of_term t1) (string_of_term t2) <= 0;;
let rec bubble_conv tm = match tm with
  | Comb(Comb(Const("word_xor",_), a), b) ->
    (match b with
     | Comb(Comb(Const("word_xor",_), b1), _) ->
       if term_leq a b1 then AP_TERM (mk_comb(rator(rator tm), a)) (bubble_conv b)
       else let th1 = PART_MATCH lhs word_xor_left_comm tm in
         let new_rhs = rhs(concl th1) in TRANS th1 (AP_TERM (rator new_rhs) (bubble_conv (rand new_rhs)))
     | _ -> if term_leq a b then REFL tm else PART_MATCH lhs xor_pair_comm tm)
  | _ -> REFL tm;;
let rec bubble_sort_conv tm =
  let rec count_xors t = match t with Comb(Comb(Const("word_xor",_), _), r) -> 1 + count_xors r | _ -> 0 in
  let n = count_xors tm in
  let rec apply_n_times k acc = if k <= 0 then acc else apply_n_times (k-1) (TRANS acc (bubble_conv (rhs(concl acc)))) in
  apply_n_times n (REFL tm);;
let rec bubble_fix tm = let th = bubble_sort_conv tm in let r = rhs(concl th) in
  if r = tm then th else TRANS th (bubble_fix r);;

(* ---- nfull=2 cascade resolvers (x5 = word(32+bl1); LE48 ival lemmas) ---- *)
let bl3_resolve_pc sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `32 + bl1 <= 48` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`32 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE48) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE48] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf "&(32 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
     [MP_TAC(ASSUME `bl1 <= 16`) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]; ALL_TAC]);;

let bl3_resolve_pc_bdy sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `32 + bl1 <= 48` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`32 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE48) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE48] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC (parse_term (Printf.sprintf "32 + bl1 = %d" k)) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[];
      SUBGOAL_THEN (parse_term (Printf.sprintf "&(32 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
       [MP_TAC(ASSUME `bl1 <= 16`) THEN MP_TAC(ASSUME (parse_term (Printf.sprintf "~(32 + bl1 = %d)" k))) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]]; ALL_TAC]);;

let bl3_resolve_pc32_taken sN target =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s target)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false) then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `word_sub (word (32+bl1):int64) (word 32) = word bl1` (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `val (word bl1:int64) = bl1` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[IVAL_WORD_LE48; ARITH_RULE `bl1 <= 16 ==> bl1 <= 48`; ARITH_RULE `bl1 <= 16 ==> 32 + bl1 <= 48`] THEN
    SUBGOAL_THEN `~(bl1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(32+bl1) - &32:int = &bl1` (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `~(&bl1:int < &0)`];
    ALL_TAC]);;

let dec_bl3_resolve_stale =
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let s = string_of_term(concl th) in
    (try String.length s > 8 && String.sub s 0 8 = "read PC " &&
         (let n = length (find_terms (fun u -> try fst(dest_const(rator u))="word" with _->false) (concl th)) in n > 1)
     with _ -> false));;
let dec_bl3_resolve sN k fall = bl3_resolve_pc sN k fall THEN dec_bl3_resolve_stale;;

(* ---- bridge-close machinery ---- *)
let collect_pmuls p t = let rec collect t acc = let acc = if p t then t::acc else acc in
  match t with Comb(a,b)->collect a (collect b acc)|Abs(_,b)->collect b acc|_->acc in setify(collect t []);;
let isWpmul t = try fst(dest_const(repeat rator t))="word_pmul" && rand t=`word 13979173243358019584:64 word` with _->false;;

let LANE_FINISH_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

let QQ8_FOLD_TAC : tactic = fun (asl,w) ->
  let l=lhs w in
  let ishpmul t=try fst(dest_const(repeat rator t))="word_pmul" && type_of t = `:128 word`
    && rand t <> `word 13979173243358019584:64 word`
    && can (find_term(fun u->u=`h2:int128`)) t && not(can (find_term(fun u->isWpmul u)) t) with _->false in
  let qq8th = snd(List.find(fun(_,th)->let c=concl th in is_eq c && (try rhs c=`qq8:128 word` with _->false)) asl) in
  (match collect_pmuls ishpmul l with
   | gp8t::_ -> (SUBGOAL_THEN (mk_eq(gp8t, `qq8:128 word`)) (fun th -> REWRITE_TAC[th]) THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM qq8th] THEN
       ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST) ORELSE
        (ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)); ALL_TAC])
   | [] -> ALL_TAC) (asl,w);;

let WA_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let wa_eq = prove(mk_eq(rwa,lwa), MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_RULE) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;

let WV_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswv t = isWpmul t && (can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwv=hd(collect_pmuls iswv l) and rwv=hd(collect_pmuls iswv r) in
  if lwv=rwv then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwv), rand(rator lwv))) in
  let wv_eq = AP_THM (AP_TERM `word_pmul:64 word->64 word->128 word` in_eq) `word 13979173243358019584:64 word` in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wv_eq] (asl,w);;

let ABBREV_WAWV_TAC : tactic = fun (asl,w) ->
  let l=lhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) in
  (ABBREV_TAC (mk_eq(`WAz:128 word`, lwa)) THEN
   (fun (asl,w) -> let l=lhs w in
     (match collect_pmuls isWpmul l with wv::_ -> ABBREV_TAC (mk_eq(`WVz:128 word`, wv)) | [] -> ALL_TAC) (asl,w)))
  (asl,w);;

(* ---- multiplier-keyed mid folding (SHARED by the le4..le8 bridge closers) ----
   FOLD_MID_HPOW keys on the pmul's MULTIPLIER (2nd arg = h-power key), NOT find_term
   over the whole pmul: in the whole-8 band the karatsuba INPUT (1st arg) carries
   lower h-powers, so whole-term keying is fragile (this was the le8 rewrite's root
   cause).  Promoted from le8block per STEP A of
   _docs/dec-band-homogenization-convergence-plan.md.  Each band's bridge closer
   folds its machine-side middle mids with FOLD_MID_HPOW "H<n-1>" .. "H2" uniformly. *)

(* Which h-power key (or W) is the MULTIPLIER (2nd arg) of a 128-bit word_pmul mid. *)
let pmul_mult_hpow t =
  let m = rand t in
  if can(find_term(fun u->u=`h2:int128`)) m then "H2" else
  if can(find_term(fun u->u=`h3:int128`)) m then "H3" else
  if can(find_term(fun u->u=`h4:int128`)) m then "H4" else
  if can(find_term(fun u->u=`h5:int128`)) m then "H5" else
  if can(find_term(fun u->u=`h6:int128`)) m then "H6" else
  if can(find_term(fun u->u=`h7:int128`)) m then "H7" else
  if can(find_term(fun u->u=`h8:int128`)) m then "H8" else
  if can(find_term(fun u->u=`h:int128`)) m then "H1" else
  if can(find_term(fun u->u=`word 13979173243358019584:64 word`)) m then "W" else "?";;
let is_pmul128_tm t = try fst(dest_const(repeat rator t))="word_pmul" && type_of t = `:128 word` with _->false;;
(* k13-carry kill set: collapses a stale `ins v18.d[0]` high half + rf8-dup joins so a machine
   block mid matches the clean spec qq by PMUL_CONG.  Only le8's block-1 mid actually carries
   the ins-k13 half (from the whole-8 main loop); for le4..le7 the plain WORD_BLAST branch
   fires first and this set is never consulted. *)
let LE8_K13_FIX = [WORD_SUBWORD_INSERT_INNER; WORD_SUBWORD_INSERT_OUTER; INSERT_SUBWORD_KILL;
                   WORD_INSERT_SUBWORD; JOINMID; JOIN_SUBWORD_RULES; RF8_SUBWORD;
                   WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR];;
let FOLD_MID_HPOW hp : tactic = fun (asl,w) ->
  let l = lhs w in
  let mid = hd(List.filter (fun t -> pmul_mult_hpow t = hp) (setify(find_terms is_pmul128_tm l))) in
  let cands = List.filter (fun (_,th) ->
      try let r=rhs(concl th) and lft=lhs(concl th) in
          is_var r && (let n=fst(dest_var r) in String.length n>=2 && String.sub n 0 2="qq") &&
          is_pmul128_tm lft && pmul_mult_hpow lft = hp
      with _->false) asl in
  let try_qq (_,th) =
    let qq = rhs(concl th) in
    (SUBGOAL_THEN (mk_eq(mid,qq)) (fun e->REWRITE_TAC[e]) THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM th] THEN
       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
       (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC LE8_K13_FIX THEN CONV_TAC WORD_BLAST)); ALL_TAC]) in
  (FIRST (map try_qq cands)) (asl,w);;

(* Establish qq39 = qq28 (le8 block-1 mid, machine-vs-spec) and rewrite it into the goal, so
   WV_UNIFY's two W-pmul inputs become bit-equal.  qq39 carries the stale ins-k13 high half;
   the k13-kill set collapses it to qq28's clean form.  ONLY the whole-8 band (le8) runs the
   main 8-block loop that produces the ins-carry, so only its bridge calls this. *)
let QQ39_FIX_TAC : tactic = fun (asl,w) ->
  let g v = snd(List.find (fun (_,th)-> try rhs(concl th)=mk_var(v,`:int128`) with _->false) asl) in
  let g39 = g "qq39" and g28 = g "qq28" in
  (SUBGOAL_THEN `qq39:int128 = qq28` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM g39] THEN GEN_REWRITE_TAC RAND_CONV [GSYM g28] THEN
    REWRITE_TAC LE8_K13_FIX THEN
    ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST) ORELSE CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
   FIRST_X_ASSUM(fun th -> if (try lhs(concl th)=`qq39:int128` with _->false)
      then GEN_REWRITE_TAC ONCE_DEPTH_CONV [th] else NO_TAC))
  (asl,w);;

(* Bridge subgoal: read Q19 s381 = ghash_polyval_acc (bsw h)(brev xi)[brev cph0;brev cph1;brev cphm].
   Builds spec_eq_byteform from goal h2/h3 byteswap hyps; folds; MERGE; unify; split; lane-close. *)
let BRIDGE_CLOSE_TAC : tactic = fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->try lhs(concl th)=`read Q19 s381` with _->false) asl) in
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let gmult3_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
            `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
            `word_bytereverse cphm:int128`; `byteswap128 h:int128`] GMULT3_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform (CONJ h2asm h3asm)) (GSYM gmult3_dec) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   QQ8_FOLD_TAC THEN WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC)
  (asl,w);;

(* ---- the full proof tactic, in 3 stages ---- *)
let keys15 = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;

let full_le3_tac_front =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (1--5) THEN
  MP_TAC(SPEC `bl1:num` USHR_256_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [3;4;5;6;7]) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (31--84) THEN mk_discard2 [3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (85--173) THEN mk_discard2 [3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (174--177) THEN GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (178--184) THEN mk_discard2 [3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (185--254) THEN mk_discard2 [3;4;5;6;7;30] THEN GCM_SIMD_SIMPLIFY_TAC THEN
  MP_TAC(SPEC `bl1:num` X5_ZERO_LEMMA3) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [255] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (256--265) THEN mk_discard2 [3;4;5;6;30] THEN
  MP_TAC(SPEC `bl1:num` USHR_256_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub (word_add in_p (word (32 + bl1):int64)) in_p = word (32 + bl1)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (266--269) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt0:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (270--270) THEN dec_bl3_resolve 270 112 3808 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (271--282) THEN dec_bl3_resolve 282 96 3856 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (283--290) THEN dec_bl3_resolve 290 80 3888 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (291--297) THEN dec_bl3_resolve 297 64 3916 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (298--303) THEN bl3_resolve_pc_bdy 303 48 3940 THEN dec_bl3_resolve_stale THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (304--309) THEN bl3_resolve_pc32_taken 309 4280 THEN dec_bl3_resolve_stale;;

let full_le3_tac_stores =
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (310--316) THEN
  SUBGOAL_THEN `read (memory :> bytes128 out_p) (s316:armstate) = pt0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt0" THEN REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s316" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (317--317) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph1:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc ctr0:int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt1:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph1:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc ctr0:int128`),keys15)))) THEN
  DISCARD_OLDSTATE_TAC "s317" THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (318--322) THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (323--331) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 16))) (s331:armstate) = pt1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt1" THEN REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s331" THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (332--336) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph2:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc ctr0):int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt2:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph2:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc ctr0):int128`),keys15)))) THEN
  DISCARD_OLDSTATE_TAC "s336";;

let full_le3_tac_tail =
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (337--343) THEN
  MP_TAC(SPEC `bl1:num` X1_MOD128_BRIDGE3) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (344--358) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_and cph2 (word (2 EXP (8 * bl1) - 1)):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  REWRITE_TAC[INSERT2_JOIN] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_DEC_256_EXEC (359--359) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor (word_and (pt2:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "pt2" THEN REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN
    REWRITE_TAC[BLEND_OR_XOR] THEN REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  DISCARD_OLDSTATE_TAC "s359" THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (360--366) THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (367--373) THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (374--374) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 32))) (s374:armstate) =
       word_xor (word_and (pt2:int128) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 32))) s374` with _ -> false)
       && (try is_comb(rand(concl th)) && fst(dest_const(rator(rator(rand(concl th))))) = "word_xor" with _ -> false)
    then MP_TAC th else NO_TAC) THEN DISCARD_OLDSTATE_TAC "s374" THEN DISCH_TAC THEN
  ABBREV_TAC `cphm:int128 = word_and cph2 (word (2 EXP (8 * bl1) - 1))` THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (375--380) THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (381--381) THEN
  SUBGOAL_THEN `read Q19 (s381:armstate) = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cphm]`
    (fun th -> ASSUME_TAC th) THENL [BRIDGE_CLOSE_TAC; ALL_TAC] THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let c = concl th in is_eq c && (try lhs c = `read Q19 s381` with _->false) &&
    not(try fst(dest_const(repeat rator (rhs c)))="ghash_polyval_acc" with _->false)) THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cphm]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (382--383) THEN
  DISCARD_OLDSTATE_TAC "s383" THEN
  SUBGOAL_THEN `read Q19 (s383:armstate) = word_bytereverse (gval:int128)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `read Q19 s383` with _ -> false)
      then ACCEPT_TAC(GEN_REWRITE_RULE RAND_CONV [BREV_JOIN_REV8] th) else NO_TAC); ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [384] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BREV_JOIN_REV8] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

(* ---- LAYER 1 (= Mila PR #417 _CONCRETE): the literal per-block band triple,
   the ARM-simulation target, with its statement WRITTEN OUT EXPLICITLY (no goal
   surgery).  bit_len = 256 + 8*bl1, 1<=bl1<=16: two FULL ciphertext blocks 0,1 +
   one MASKED partial tail block 2 (mask = word(2 EXP (8*bl1) - 1)).  Input is the
   three per-block ciphertext reads cph0/cph1/cph2; output is the three per-block
   plaintext stores (block 2 masked-blended with outprev) + the GHASH tag in xi_p.
   Proven by the full ARM simulation (~780s). ---- *)
let AESV8_GCM_8X_DEC_256_LE3BLOCK_BODY = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 cph2 h3 h3k.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,48) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,48) (xi_p,16) /\
    nonoverlapping (out_p,48) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,48) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,48) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,48) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,48) (in_p,48) /\
    nonoverlapping (out_p,48) (key_p,240) /\
    nonoverlapping (out_p,48) (htbl_p,192) /\
    nonoverlapping (out_p,48) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (256 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             read (memory :> bytes128 in_p) s = cph0 /\
             read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
             read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 32))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k)
        (\s. read PC s = word (pc + 4580) /\
             read (memory :> bytes128 out_p) s =
             word_xor cph0 (aes256_encrypt ctr0 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 16))) s =
             word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14]) /\
             read (memory :> bytes128 (word_add out_p (word 32))) s =
             word_xor (word_and (word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14])) (word (2 EXP (8 * bl1) - 1))) (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
             read (memory :> bytes128 xi_p) s =
             word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse (word_and cph2 (word (2 EXP (8 * bl1) - 1)))]))
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,48); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  full_le3_tac_front THEN full_le3_tac_stores THEN full_le3_tac_tail);;

(* ---- per-block CTR list reductions (the 3 output blocks of aes_ctr), used by
   the LAYER 2 output bridge below.  Reusable, ARM-free. ---- *)
let AES_CTR_3_EL = prove
 (`EL 0 (aes_ctr ctr0 [pt0;pt1;pt2] keys) = word_xor pt0 (aes256_encrypt ctr0 keys) /\
   EL 1 (aes_ctr ctr0 [pt0;pt1;pt2] keys) =
     word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys) /\
   EL 2 (aes_ctr ctr0 [pt0;pt1;pt2] keys) =
     word_xor pt2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) keys)`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; ARITH_RULE `2 = SUC(SUC 0)`; EL; HD; TL] THEN
  REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_INC_ITER_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[gcm_ctr_inc_iter]);;

(* ============================================================================
   SCALABILITY TO <=4 / <=8 (assessment, 2026-06-26).
   ----------------------------------------------------------------------------
   The dec tail bands are STRUCTURALLY IDENTICAL per block (verified via objdump):
   each more_than_K entry (0x1074=_3, 0x10b8=_2, 0x10f4=_1) does exactly one
   full-block GHASH round (rev64 v8; eor mask; mov v27; pmull v26/pmull2 v28/
   pmull2 v27 with H^(K+1) at [x6,#16K] and its mid key; eor into Q17/Q18/Q19)
   then st1 the prior plaintext + eor3 the next.  The closing reduction
   (0x1138 less_than_1 ... 0x11d4 eor v19,v19,v18 ... 0x11dc rev64 ... 0x11e0 st1)
   is SHARED across all bands.

   So LE4BLOCK (nfull=3, 49-63 bytes = 3 full + 1 masked) = LE3BLOCK + one more
   full-block round.  The proof recipe generalizes directly:
   - front+cascade: #48 b.gt now TAKEN -> more_than_3 (0x1074=pc+4212); resolvers
     identical with byte_len = 48 + bl1, bound 48+bl1<=64, x5=word(48+bl1)
     (USHR_384/X5_ZERO_LEMMA4/IVAL_*_LE64 — same proofs, larger bound).
   - stores: pt0/pt1/pt2 full + pt3 masked (one extra ARM_VSTEPS store-capture span;
     pt3 counter = gcm_ctr_inc^3 ctr0, needs GCM_CTR_INC3_LANES, analog of _INC2).
   - bridge AT s(381+round_len) = AFTER the eor v19,v19,v18 (the SAME off-by-one fix!).
   - GMULT4_FULL_CORRECT_BA: the 4-block analog of GMULT3_FULL_CORRECT_BA, built the
     SAME way (dec4_tL = XOR of 4 Karatsuba packs; PACK4_ID via GEN_REWRITE PMUL_KARATSUBA
     + WORD_ZX_XOR + WORD_SHL_XOR + WORD_RULE; then SPEC dec4_tL into GMULT_REDUCE_PROP3;
     TRANS + AP_TERM PACK4_ID).  ALL ingredients present: PMUL_KARATSUBA, GMULT_REDUCE_PROP3,
     KARATSUBA_LIMBS, GHASH_POLYVAL_ACC_4 (in common/ghash_nblock_karatsuba.ml).
   - spec_to_byteform_4: GHASH_POLYVAL_ACC_4 + the h2/h3/h4 byteswap preconds (h4 = H^4
     read from htbl_p+? ; new precond byteswap128 h4 = polyval_dot(bsw h)(...h^3)).
   - BRIDGE_CLOSE_TAC generalizes UNCHANGED in shape: MERGE_2BLK shares qq names;
     fold the extra middle-block mid (qq-analog of qq8, one per full middle block);
     wa unify (PMUL_CONG), wv unify (BITBLAST in_eq — still ONE wv-round, shared
     reduction); ABBREV W-pmuls opaque; QQ0SPLIT+JOIN_EQ_SPLIT; lanes close by
     WORD_SIMPLE_SUBWORD + SJ_COLLAPSE + bubble_fix.  The lane multiset just has more
     qq terms; bubble_fix is flat in the term count, so NO new algebraic obstruction.

   TIME/SCALE: each band adds ~1 GHASH-round sim span (~60-100s) + the GMULTn build
   (PACK_N_ID is the cost driver: PACK3_ID ~373s WORD_RULE on 256-bit; PACK4_ID similar,
   ONE-TIME at load).  The bridge close itself is ~3-4 min (dominated by MERGE + the
   per-lane bubble_fix).  Recommended for nfull=3..7: a GMULTn builder (parameterize
   dec_N_tL over the block list — the dec_tL OCaml constructor here is the start) + a
   band-generic driver (parameterize the front-cascade resolvers + store count + the
   bridge state s(381 + 17*(nfull-2)) over nfull) to avoid 5 near-copies.

   NO FUNDAMENTAL OBSTACLE to <=4 or <=8: the s381 off-by-one fix + GMULT_REDUCE_PROP3
   (one abstract BITBLAST, flat in N) + bubble_fix lane close all generalize.  The 3-block
   GF wall that blocked prior sessions was purely the s380/s381 off-by-one, now resolved.
   ============================================================================ *)

(* ===========================================================================
   PART 3 — generic-input byte-buffer bridge (input side of LAYER 2).
   =========================================================================== *)


(* General N-block input bridge (induction on n via the XTS MERGE primitive):
   a prefix byte-read at 16*n determines every block lane k<n. *)
let INPUT_BYTES_TO_BYTE128_LANES = prove
 (`!n (in_p:int64) (x:byte list) s.
    16 * n <= LENGTH x /\
    read (memory :> bytes (in_p, 16 * n)) s = num_of_bytelist (SUB_LIST (0, 16 * n) x)
    ==> !k. k < n ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s =
                      bytes_to_int128 (SUB_LIST (16 * k, 16) x)`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `16 * n`; `x:byte list`; `s:armstate`] READ_BYTES_AND_BYTE128_MERGE) THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`in_p:int64`; `x:byte list`; `s:armstate`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]]);;

(* Convenience corollary: an EXACT 16*n-byte buffer gives all N lanes directly. *)
let INPUT_BYTES_FULL = prove
 (`!n (in_p:int64) (x:byte list) s.
    LENGTH x = 16 * n /\
    read (memory :> bytes (in_p, 16 * n)) s = num_of_bytelist x
    ==> !k. k < n ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s =
                      bytes_to_int128 (SUB_LIST (16 * k, 16) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INPUT_BYTES_TO_BYTE128_LANES THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  SUBGOAL_THEN `SUB_LIST (0, 16 * n) (x:byte list) = x` (fun th->ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]);;

(* Concrete N=3 instance (LE3BLOCK input: cph0,cph1,cph2 as one 48-byte buffer).
   in_p+0/+16/+32 lanes; use with bl1<=16 (the partial tail block is over-read full
   then masked in-register, so the buffer is 3 FULL 16-byte blocks = 48 bytes). *)
let INPUT_BRIDGE_3 = prove
 (`!(in_p:int64) (x:byte list) s.
    LENGTH x = 48 /\
    read (memory :> bytes (in_p, 48)) s = num_of_bytelist x
    ==> read (memory :> bytes128 in_p) s = bytes_to_int128 (SUB_LIST (0,16) x) /\
        read (memory :> bytes128 (word_add in_p (word 16))) s = bytes_to_int128 (SUB_LIST (16,16) x) /\
        read (memory :> bytes128 (word_add in_p (word 32))) s = bytes_to_int128 (SUB_LIST (32,16) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`3`; `in_p:int64`; `x:byte list`; `s:armstate`] INPUT_BYTES_FULL) THEN
  ASM_REWRITE_TAC[ARITH_RULE `16 * 3 = 48`] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])));;

(* ============================================================================
   LAYER 2 (= Mila PR #417 _ABS): the READABLE public theorem
   AESV8_GCM_8X_DEC_256_LE3BLOCK.  ONE explicit `ensures arm` Hoare triple with
   `byte_list_at` for BOTH the input ciphertext buffer and the output plaintext
   buffer — exactly the AES-XTS (CIPHER_STEALING_CORRECT) and Mila AES256_GCM
   (PR #417) presentation:
     - INPUT  : byte_list_at x in_p (word 48) s            (x = 48 ciphertext bytes)
     - OUTPUT : byte_list_at (aes_ctr_full_tail_bytes ctr0 [cph0;cph1;cph2] keys 2 bl1)
                  out_p (word (32 + bl1)) s                (2 full plaintext blocks ++
                  first bl1 bytes of the masked tail block, cphk read from the input bytes)
     - TAG    : xi_p holds the byte-reversed GHASH polyval over the 3 reversed
                ciphertext blocks (masked tail included).

   Proved sim-free from the LAYER-1 BODY: only the input/output presentations
   differ, and they are discharged by the shared, ARM-free bridges
     - input  : INPUT_BRIDGE_3            (byte_list_at -> 3 per-block lane reads)
     - output : BYTE_LIST_AT_NBLOCK_CTR + AES_CTR_3_EL  (per-block stores -> byte_list_at)
   via ENSURES_PRECONDITION_THM / ENSURES_POSTCONDITION_THM.  No re-simulation,
   no goal-surgery.  hyps=0, axioms()=3, no cheats.
   ============================================================================ *)

let AESV8_GCM_8X_DEC_256_LE3BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    x xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1 h3 h3k.
    LENGTH x = 48 /\
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc,4612) (stackpointer,80) /\
    nonoverlapping (word pc,4612) (out_p,48) /\
    nonoverlapping (word pc,4612) (xi_p,16) /\
    nonoverlapping (word pc,4612) (ivec_p,16) /\
    nonoverlapping (out_p,48) (xi_p,16) /\
    nonoverlapping (out_p,48) (ivec_p,16) /\
    nonoverlapping (xi_p,16) (ivec_p,16) /\
    nonoverlapping (ivec_p,16) (in_p,48) /\
    nonoverlapping (ivec_p,16) (key_p,240) /\
    nonoverlapping (ivec_p,16) (htbl_p,192) /\
    nonoverlapping (in_p,48) (stackpointer,80) /\
    nonoverlapping (key_p,240) (stackpointer,80) /\
    nonoverlapping (htbl_p,192) (stackpointer,80) /\
    nonoverlapping (ivec_p,16) (stackpointer,80) /\
    nonoverlapping (xi_p,16) (in_p,48) /\
    nonoverlapping (xi_p,16) (key_p,240) /\
    nonoverlapping (xi_p,16) (htbl_p,192) /\
    nonoverlapping (xi_p,16) (stackpointer,80) /\
    nonoverlapping (out_p,48) (in_p,48) /\
    nonoverlapping (out_p,48) (key_p,240) /\
    nonoverlapping (out_p,48) (htbl_p,192) /\
    nonoverlapping (out_p,48) (stackpointer,80) /\
    word_subword hk (0,64) = word_xor (word_subword h (0,64):64 word) (word_subword h (64,64)) /\
    word_subword hk (64,64) = word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64)) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h)) /\
    word_subword h3k (0,64) = word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64))
    ==> ensures arm
        (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
             read PC s = word (pc + 24) /\
             read SP s = stackpointer /\
             C_ARGUMENTS [in_p; word (256 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
             read Q30 s = ctr0 /\
             byte_list_at x in_p (word 48) s /\
             read (memory :> bytes128 xi_p) s = xi /\
             read (memory :> bytes128 ivec_p) s = ctr0 /\
             read (memory :> bytes128 (word_add out_p (word 32))) s = outprev /\
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
             read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k)
        (\s. read PC s = word (pc + 4580) /\
             byte_list_at
               (gcm_dec_pt_bytes (32 + bl1) x ctr0
                 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9; k10; k11; k12; k13; k14])
               out_p (word (32 + bl1)) s /\
             read (memory :> bytes128 xi_p) s = gcm_dec_final_xi (32 + bl1) x xi h)
        (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
         MAYCHANGE [memory :> bytes (out_p,48); memory :> bytes (xi_p,16); memory :> bytes (ivec_p,16); memory :> bytes (word_add stackpointer (word 64),16)] ,,
         MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Unfold the recursive whole-buffer spec to the explicit 3-block list (nfull=2, tail=bl1). *)
  ASM_SIMP_TAC[gcm_dec_final_xi; GCM_DEC_GHASH_BLOCKS_3; GCM_DEC_PT_BYTES_3; MAP] THEN
  (* INPUT: strengthen precondition byte_list_at x  ->  the 3 per-block cphk lane reads. *)
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
    (rand(rator(rator(rand(concl(SPECL
       [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;`in_p:int64`;`key_p:int64`;`htbl_p:int64`;
        `bytes_to_int128 (SUB_LIST (0,16) (x:byte list))`;
        `bytes_to_int128 (SUB_LIST (16,16) (x:byte list))`;
        `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;
        `k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;
        `h:int128`;`hk:int128`;`h2:int128`;`outprev:int128`;`bl1:num`;
        `bytes_to_int128 (SUB_LIST (32,16) (x:byte list))`;`h3:int128`;`h3k:int128`]
       AESV8_GCM_8X_DEC_256_LE3BLOCK_BODY)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`0`; `x:byte list`; `in_p:int64`; `word 48:int64`; `s:armstate`] BYTE_LIST_AT_3BLOCKS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `val (word 48:int64) = 48` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    (* OUTPUT: weaken postcondition per-block plaintext stores  ->  byte_list_at. *)
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
      (rand(rator(rand(concl(SPECL
         [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;`in_p:int64`;`key_p:int64`;`htbl_p:int64`;
          `bytes_to_int128 (SUB_LIST (0,16) (x:byte list))`;
          `bytes_to_int128 (SUB_LIST (16,16) (x:byte list))`;
          `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;
          `k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;
          `h:int128`;`hk:int128`;`h2:int128`;`outprev:int128`;`bl1:num`;
          `bytes_to_int128 (SUB_LIST (32,16) (x:byte list))`;`h3:int128`;`h3k:int128`]
         AESV8_GCM_8X_DEC_256_LE3BLOCK_BODY))))) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BYTE_LIST_AT_NBLOCK_CTR THEN EXISTS_TAC `outprev:int128` THEN
      REWRITE_TAC[AES_CTR_3_EL] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `val (word (32 + bl1):int64) = 32 + bl1` SUBST1_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        ARITH_TAC;
        REWRITE_TAC[LENGTH] THEN ARITH_TAC;
        X_GEN_TAC `kk:num` THEN REWRITE_TAC[ARITH_RULE `kk < 2 <=> kk = 0 \/ kk = 1`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0; AES_CTR_3_EL] THEN ASM_REWRITE_TAC[AES_CTR_3_EL];
        REWRITE_TAC[ARITH_RULE `16 * 2 = 32`] THEN ASM_REWRITE_TAC[AES_CTR_3_EL]];
      MATCH_MP_TAC AESV8_GCM_8X_DEC_256_LE3BLOCK_BODY THEN ASM_REWRITE_TAC[]]]);;
