(* ============================================================================
   AESV8_GCM_8X_DEC_256, the 17-31 byte band (decrypt): bit_len = 128 + 8*bl1,
   1<=bl1<=16.  One FULL block 0 (more_than_1, GHASH vs H^2) + one MASKED partial
   block 1 (less_than_1, symbolic mask MK = word(2 EXP (8*bl1)-1)).

   Decrypt analog / mirror of AESV8_GCM_8X_ENC_256_LE2BLOCK
   (arm/proofs/aesv8_gcm_8x_enc_256_le2block.ml), with the dec dataflow (pt->cph;
   dec GHASHes the loaded INPUT ciphertext, so the block-1 GHASH element is
   word_bytereverse (word_and cph1 MK)) and the GMULT2 fast bridge from the dec
   2-block proof (DEC_2BLK_GMULT2_BRIDGE_TAC, parameterised over the block-1
   ciphertext atom).

   Requires arm/proofs/aesv8_gcm_8x_dec_256_2block.ml loaded (EXEC rule, the
   GMULT2 bridge + GMULT2_FULL_CORRECT_BA + MERGE_2BLK + helpers) and the dec
   1-block file (MASK_LEMMA / BLEND_OR_XOR / INSERT2_JOIN / bl_resolve machinery /
   X5_ZERO_LEMMA / USHR_8BL_LEMMA / AESV8_GCM_8X_DEC_256_LE1BLOCK).

   Scalable: the masked-tail spec is aes_ctr_full_tail_bytes at nfull=1, tail=bl1,
   bridged to byte_list_at by the generic BYTE_LIST_AT_NBLOCK_CTR (which is
   nfull/tail-generic, so 33..N-byte bands reuse it at nfull>=2 unchanged).

   No CHEAT_TAC, no new axioms.
   ============================================================================ *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_2block.ml";;

(* ---- symbolic-bit_len helper lemmas (2-block band: bit_len = 128 + 8*bl1) ---- *)

(* X9 = ushr(bit_len, 3) = number of full+partial bytes/blocks = 16 + bl1. *)
let USHR_128_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (128 + 8 * bl1):int64) 3 = word (16 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (128 + 8 * bl1):int64) = 128 + 8 * bl1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

(* X5 = ((16+bl1-1) & ~0x7f) = 0 (since 16+bl1 <= 32 < 128), so X5 = in_p. *)
let X5_ZERO_LEMMA2 = prove
 (`!bl1. 1 <= bl1 /\ bl1 <= 16
        ==> word_and (word_sub (word (16 + bl1)) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [WORD_RULE `word_sub (word (16 + bl1):int64) (word 1) = word (15 + bl1)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `j < 7` THENL
   [REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `~bit j (word 18446744073709551488:int64)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `j < 7` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[BIT_WORD] THEN
    SUBGOAL_THEN `15 + bl1 < 2 EXP j` (fun th -> SIMP_TAC[th; DIV_LT; ODD; DE_MORGAN_THM]) THEN
    TRANS_TAC LTE_TRANS `2 EXP 7` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;

(* looser <=32 ival lemmas for the symbolic 2-block tail cascade (x5 = 16+bl1). *)
let IVAL_WORD_LE32 = prove
 (`!b. b <= 32 ==> ival (word b:int64) = &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival] THEN
  SUBGOAL_THEN `val (word b:int64) = b` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  ASM_SIMP_TAC[ARITH_RULE `b <= 32 ==> b < 2 EXP (64 - 1)`]);;

let IVAL_WSUB_LE32 = prove
 (`!b k. b <= 32 /\ k <= 112
          ==> ival (word_sub (word b) (word k):int64) = &b - &k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

(* X1 = bit_len = 128 + 8*bl1; the routine masks with X1 AND 0x7f; 128 = 0 mod 128
   so (128+8*bl1) AND 127 = (8*bl1) AND 127, letting MASK_LEMMA apply with bl:=bl1. *)
let X1_MOD128_BRIDGE = prove
 (`!bl1. bl1 <= 16
    ==> word_and (word (128 + 8 * bl1):int64) (word 127) =
        word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (128 + 8 * bl1):int64) = 128 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `128 + 8 * bl1 = 8 * bl1 + 1 * 128`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* XOR-comm helper for the wal lane (the two byteforms present qq1l^qq6l in
   opposite operand order through MERGE). *)
let DEC2_WXSYM = WORD_RULE `word_xor qq6l qq1l = word_xor qq1l qq6l`;;

(* ---- symbolic tail-cascade resolvers (x5 = word(16+bl1)).  bl2_resolve_pc:
   cmp #k fall-through (16+bl1 < k).  _bdy: boundary 16+bl1=k allowed (k=32).
   _16_taken: cmp #16 b.gt TAKEN (16+bl1 > 16 since bl1>=1) -> more_than_1. ---- *)
let bl2_resolve_pc sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `16 + bl1 <= 32` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`16 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE32) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE32] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf "&(16 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
     [MP_TAC(ASSUME `bl1 <= 16`) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]; ALL_TAC]);;

let bl2_resolve_pc_bdy sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `16 + bl1 <= 32` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`16 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE32) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE32] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC (parse_term (Printf.sprintf "16 + bl1 = %d" k)) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[];
      SUBGOAL_THEN (parse_term (Printf.sprintf "&(16 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
       [MP_TAC(ASSUME `bl1 <= 16`) THEN MP_TAC(ASSUME (parse_term (Printf.sprintf "~(16 + bl1 = %d)" k))) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]]; ALL_TAC]);;

let bl2_resolve_pc16_taken sN target =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s target)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false) then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `word_sub (word (16+bl1):int64) (word 16) = word bl1` (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `val (word bl1:int64) = bl1` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[IVAL_WORD_LE32; ARITH_RULE `bl1 <= 16 ==> bl1 <= 32`; ARITH_RULE `bl1 <= 16 ==> 16 + bl1 <= 32`] THEN
    SUBGOAL_THEN `~(bl1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(16+bl1) - &16:int = &bl1` (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `~(&bl1:int < &0)`];
    ALL_TAC]);;

(* resolve a symbolic b.gt PC at state sN to the fall PC, discarding the stale
   conditional PC assumption (the one with >1 `word(pc+..)` subterm). *)
let dec_bl2_resolve sN k fall =
  bl2_resolve_pc sN k fall THEN
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let s = string_of_term(concl th) in
    (try String.length s > 8 && String.sub s 0 8 = "read PC " &&
         (let n = length (find_terms (fun u -> try fst(dest_const(rator u))="word" with _->false) (concl th)) in n > 1)
     with _ -> false));;

let dec_bl2_resolve_stale =
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let s = string_of_term(concl th) in
    (try String.length s > 8 && String.sub s 0 8 = "read PC " &&
         (let n = length (find_terms (fun u -> try fst(dest_const(rator u))="word" with _->false) (concl th)) in n > 1)
     with _ -> false));;

(* ---- STEP C (shared): ONE parameterized front generator for the le2..le8 bands ----
   The front (states 1..269 + pt0-capture) is IDENTICAL across the multi-block bands
   except: ushr_lemma (the band's bit_len length lemma USHR_{128*nfull}_8BL_LEMMA),
   x5_lemma (X5_ZERO_LEMMA{nfull+1}), disc (keystream Q-regs discarded per step in
   windows 6..254 — the band KEEPS Q0..Qk for its blocks), disc2 (the 256..265
   window's discard list, kept verbatim per band), inoff (16*nfull, the in_p
   tail-block offset in the word_sub rewrite), and nks (how many keystream regs to
   abbreviate ks0..ks{nks-1} at s269; 0 = none).  The band's branch cascade
   (steps 270.., per-band resolver rungs) is appended by the caller — the rung
   structure (fall/boundary/taken placement) genuinely differs per byte-length.
   The le1 band (1..16 bytes, NO full blocks) never enters the more_than_k path,
   so its front in aesv8_gcm_8x_dec_256_1block.ml stays separate by design.
   See STEP C of _docs/dec-band-homogenization-convergence-plan.md. *)
let keys15 = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;

let DEC_FRONT_TAC ushr_lemma x5_lemma disc disc2 inoff nks =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (1--5) THEN
  MP_TAC(SPEC `bl1:num` ushr_lemma) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 disc) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (31--84) THEN mk_discard2 (disc@[30]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (85--173) THEN mk_discard2 (disc@[30]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (174--177) THEN GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 (disc@[30]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (178--184) THEN mk_discard2 (disc@[30]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (185--254) THEN mk_discard2 (disc@[30]) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  MP_TAC(SPEC `bl1:num` x5_lemma) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [255] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (256--265) THEN mk_discard2 disc2 THEN
  MP_TAC(SPEC `bl1:num` ushr_lemma) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE (parse_term (Printf.sprintf
      "word_sub (word_add in_p (word (%d + bl1):int64)) in_p = word (%d + bl1)" inoff inoff))]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (266--269) THEN
  EVERY(map (fun i -> ABBREV_TAC (parse_term (Printf.sprintf
      "ks%d:int128 = read Q%d s269" i i))) (0--(nks-1))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt0:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15))));;

(* targeted lane closer for the GMULT2 W-surface (fold qqNl/qqNh lane subwords,
   then a flat 64-bit WORD_RULE). *)
let LANE_CLOSE_TAC : tactic = fun (asl,w) ->
  let is_lane_def (_,th) =
    let c = concl th in is_eq c &&
    (try let r = rhs c in is_var r &&
       (let n = fst(dest_var r) in String.length n>=3 && String.sub n 0 2="qq" &&
        (let last = n.[String.length n-1] in last='l' || last='h'))
     with _ -> false) &&
    (try let l = lhs c in is_comb l && fst(dest_const(rator(rator l)))="word_subword" with _ -> false) in
  let lane_ths = map snd (filter is_lane_def asl) in
  (REWRITE_TAC lane_ths THEN CONV_TAC WORD_RULE) (asl,w);;

(* collapse the symbolic mask on the block-1 ciphertext: find word_and <symbolic
   mask> cph1 in the assumptions, prove = word_and cph1 MK (INSERT2_JOIN +
   MASK_LEMMA), rewrite everywhere. *)
let MASK_COLLAPSE_CPH1_SYM_TAC : tactic = fun (asl,w) ->
  let masked =
    tryfind (fun (_,th) ->
      let c = concl th in
      hd (find_terms (fun u -> try fst(dest_const(rator(rator u)))="word_and" && rand u=`cph1:int128`
                               && not(is_var(rand(rator u))) with _->false) c))
      asl in
  let mk = `word_and cph1 (word (2 EXP (8 * bl1) - 1)):int128` in
  (SUBGOAL_THEN (mk_eq(masked, mk))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)
   THENL [REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE;
          ALL_TAC]) (asl,w);;

(* the GMULT2 fast bridge, parameterised over the (masked) block-1 ciphertext atom
   cph1term.  Mirrors DEC_2BLK_GMULT2_BRIDGE_TAC from the 2-block proof. *)
let dec2_gmult2_bridge_tac cph1term =
  let a0t = `word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`
  and a1t = mk_comb(`word_bytereverse:int128->int128`, cph1term) in
  let gmult2_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [a0t; `byteswap128 h2:int128`; a1t; `byteswap128 h:int128`] GMULT2_FULL_CORRECT_BA) in
  let r1def = `word_xor (word_xor (word_shl (word_zx (wal:64 word):128 word) 63) (word_shl (word_zx wal:128 word) 62)) (word_shl (word_zx wal:128 word) 57)` in
  let udef = `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l))))` in
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th)=`byteswap128 h2` with _->false)
    then GEN_REWRITE_TAC RAND_CONV
           [REWRITE_RULE[GSYM gmult2_dec]
             (GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th]
               (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
                       `word_bytereverse cph0:int128`; mk_comb(`word_bytereverse:int128->int128`,cph1term)]
                 GHASH_POLYVAL_ACC_2))]
    else NO_TAC) THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
  REWRITE_TAC[PMUL_W_64_128] THEN REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  EVERY (map (fun a ->
    let av = mk_var(a,`:int128`) in
    ABBREV_TAC (mk_eq(mk_var(a^"l",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(0,64)`))) THEN
    ABBREV_TAC (mk_eq(mk_var(a^"h",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(64,64)`))))
    ["qq0";"qq1";"qq4";"qq5";"qq6";"qq10"]) THEN
  ABBREV_TAC `wal:64 word = word_xor qq1l qq6l` THEN
  REWRITE_TAC[DEC2_WXSYM] THEN
  FIRST_ASSUM(fun th -> if (try rhs(concl th)=`wal:64 word` && lhs(concl th)=`word_xor qq1l qq6l:64 word` with _->false) then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_TAC (mk_eq(`r1:128 word`, r1def)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (0,64):64 word) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (64,64):64 word) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (0,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (0,64):64 word)) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (64,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (64,64):64 word)) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`u:64 word`, udef)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor qq10l qq4l) (word_xor wal (word_xor qq0l qq5l))) (word_xor (word_xor qq1h qq6h) (word_subword (r1:128 word) (0,64):64 word)) = u`
   (fun th -> REWRITE_TAC[th]) THENL [MAP_EVERY EXPAND_TAC ["u";"wal"] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l)))) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `us57:128 word = word_shl (word_zx (u:64 word):128 word) 57` THEN
  ABBREV_TAC `us62:128 word = word_shl (word_zx (u:64 word):128 word) 62` THEN
  ABBREV_TAC `us63:128 word = word_shl (word_zx (u:64 word):128 word) 63` THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_CLOSE_TAC;;

(* ========================================================================= *)
(* The 17-31 byte band decrypt theorem (masked-blend out_p postcond).         *)
(* bit_len = 128 + 8*bl1: one FULL block 0 + one MASKED partial block 1.       *)
(* ========================================================================= *)

let AESV8_GCM_8X_DEC_256_LE2BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4612) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4612) (out_p:int64, 32) /\
    nonoverlapping (word pc, 4612) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4612) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (xi_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 32) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 240) /\
    nonoverlapping (out_p, 32) (htbl_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (128 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 (word_add out_p (word 16))) s = outprev /\
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
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 0x11e4) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor (word_and (word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
            (word (2 EXP (8 * bl1) - 1)))
            (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0;
               word_bytereverse (word_and cph1 (word (2 EXP (8 * bl1) - 1)))]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  (* shared front generator (states 1..269 + pt0-capture), then the band's cascade:
     symbolic tail cascade (x5 = word(16+bl1)): #112..#32 fall through, #16 TAKEN
     -> more_than_1 (pc+4340).  Same step indices as enc le2block. *)
  DEC_FRONT_TAC USHR_128_8BL_LEMMA X5_ZERO_LEMMA2 [2;3;4;5;6;7] [2;3;4;5;6;30] 16 0 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (270--270) THEN dec_bl2_resolve 270 112 3808 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (271--282) THEN dec_bl2_resolve 282 96 3856 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (283--290) THEN dec_bl2_resolve 290 80 3888 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (291--297) THEN dec_bl2_resolve 297 64 3916 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (298--303) THEN dec_bl2_resolve 303 48 3940 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (304--309) THEN
  bl2_resolve_pc_bdy 309 32 3964 THEN dec_bl2_resolve_stale THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (310--313) THEN
  bl2_resolve_pc16_taken 313 4340 THEN dec_bl2_resolve_stale THEN
  (* more_than_1 block-0: st1 v12 stores pt0 to out_p; capture readback. *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (314--320) THEN
  SUBGOAL_THEN `read (memory :> bytes128 out_p) (s320:armstate) = pt0`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt0" THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s320" THEN
  (* block-1 eor3 321..328 -> Q12 = block-1 plaintext; abbrev pt1. *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (321--328) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC
    `pt1:int128 = word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  DISCARD_OLDSTATE_TAC "s328" THEN
  (* into less_than_1: X1 = (128+8*bl1) AND 0x7f, bridge to (8*bl1) AND 0x7f. *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (329--335) THEN
  DISCARD_OLDSTATE_TAC "s335" THEN mk_discard2 [1;2;3;4;5;6;7] THEN
  MP_TAC(SPEC `bl1:num` X1_MOD128_BRIDGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  (* less_than_1 mask region 336..350: collapse Q9 to word_and cph1 MK, and
     re-assert Q12 = the masked-blend so the block-1 store readback is captured. *)
  ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (336--350) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_and cph1 (word (2 EXP (8 * bl1) - 1)):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  REWRITE_TAC[INSERT2_JOIN] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor (word_and (pt1:int128) (word (2 EXP (8 * bl1) - 1)))
       (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "pt1" THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN
    REWRITE_TAC[BLEND_OR_XOR] THEN REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_BLAST;
    DISCH_TAC] THEN
  (* block-1 GHASH multiply over the masked block + store pt1-masked to out_p+16
     + single Prop3 reduction; capture the masked store readback before discards. *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (351--363) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s363:armstate) =
     word_xor (word_and (pt1:int128) (word (2 EXP (8 * bl1) - 1)))
       (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s363` with _ -> false) &&
       (try is_comb(rand(concl th)) &&
            fst(dest_const(rator(rator(rand(concl th))))) = "word_xor" with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s363" THEN DISCH_TAC THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (364--369) THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s363` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s369" THEN DISCH_TAC THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC [370] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s363` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s370" THEN DISCH_TAC THEN
  (* collapse the symbolic mask inside Q19's GHASH block, then abstract the masked
     block-1 ciphertext to an atom cphm so the bridge is identical to the 2BLOCK
     whole-block bridge with cph1:=cphm. *)
  MASK_COLLAPSE_CPH1_SYM_TAC THEN
  ABBREV_TAC `cphm:int128 = word_and cph1 (word (2 EXP (8 * bl1) - 1))` THEN
  (* === GMULT2 fast bridge over the masked block-1 = cphm === *)
  SUBGOAL_THEN
    `read Q19 (s370:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cphm]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s370`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s370` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   dec2_gmult2_bridge_tac `cphm:int128`;
   ALL_TAC] THEN
  (* ext+rev64 371-372 -> word_bytereverse gval; store xi_p 373; exit pc+0x11e4. *)
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cphm]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (371--372) THEN
  SUBGOAL_THEN `read Q19 (s372:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s372`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s372` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [373] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC));;

(* ========================================================================= *)
(* byte_list_at corollary (the generic single-buffer form): out_p is one       *)
(* byte_list_at clause over aes_ctr_full_tail_bytes with nfull=1, tail=bl1     *)
(* (one full block 0 ++ first bl1 bytes of the masked block 1).  Cheap         *)
(* postcond-weakening via BYTE_LIST_AT_NBLOCK_CTR (nfull/tail generic).        *)
(* ========================================================================= *)

let AESV8_GCM_8X_DEC_256_LE2BLOCK_BYTELIST = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4612) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4612) (out_p:int64, 32) /\
    nonoverlapping (word pc, 4612) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4612) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (xi_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 32) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 240) /\
    nonoverlapping (out_p, 32) (htbl_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (128 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 (word_add out_p (word 16))) s = outprev /\
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
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 0x11e4) /\
          byte_list_at
            (aes_ctr_full_tail_bytes ctr0 [cph0;cph1]
               [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14] 1 bl1)
            out_p (word (16 + bl1)) s /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0;
               word_bytereverse (word_and cph1 (word (2 EXP (8 * bl1) - 1)))]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC
   `\s. read PC s = word (pc + 0x11e4) /\
        read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
        read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor (word_and (word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
            (word (2 EXP (8 * bl1) - 1)))
            (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
        read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0;
               word_bytereverse (word_and cph1 (word (2 EXP (8 * bl1) - 1)))])` THEN
  CONJ_TAC THENL
   [BETA_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BYTE_LIST_AT_NBLOCK_CTR THEN
    EXISTS_TAC `outprev:int128` THEN
    REWRITE_TAC[AES_CTR_2_EL] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `val (word (16 + bl1):int64) = 16 + bl1` SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ARITH_TAC;
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `16 * 0 = 0`; WORD_ADD_0] THEN
      X_GEN_TAC `kk:num` THEN
      REWRITE_TAC[ARITH_RULE `kk < 1 <=> kk = 0`] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `16 * 0 = 0`; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[AES_CTR_2_EL];
      REWRITE_TAC[MULT_CLAUSES] THEN ASM_REWRITE_TAC[AES_CTR_2_EL]];
    MATCH_MP_TAC AESV8_GCM_8X_DEC_256_LE2BLOCK THEN ASM_REWRITE_TAC[]]);;
