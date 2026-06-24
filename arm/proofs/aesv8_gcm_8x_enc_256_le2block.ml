(* ============================================================================
   AESV8_GCM_8X_ENC_256, the 17-31 byte band: bit_len = 128 + 8*bl1, 1<=bl1<=16.
   One FULL block 0 (more_than_1, GHASH vs H^2) + one MASKED partial block 1
   (less_than_1, symbolic mask MK = word(2 EXP (8*bl1)-1)).

   First binary consumer of BYTE_LIST_AT_NBLOCK_CTR at nfull=1.

   Requires arm/proofs/aesv8_gcm_8x_enc_256_2block.ml already loaded (brings in
   the EXEC rule, the 1block LE1BLOCK symbolic-mask machinery MASK_LEMMA /
   BLEND_OR_XOR / bl_resolve_pc / INSERT2_JOIN / USHR_8BL_LEMMA / X5_ZERO_LEMMA,
   GHASH_POLYVAL_ACC_2, MERGE_2BLK_TAC / FINISH_2BLK_TAC / ABBREV_INNER_PMULS_TAC,
   the 2BLOCK bridge helpers, BYTE_LIST_AT_NBLOCK_CTR + aes_ctr_full_tail_bytes).

   STATUS (2026-06-22): DONE.  loadt-clean, binds AESV8_GCM_8X_ENC_256_LE2BLOCK
   (strong masked-blend out_p postcond) and AESV8_GCM_8X_ENC_256_LE2BLOCK_BYTELIST
   (byte_list_at over aes_ctr_full_tail_bytes nfull=1 tail=bl1), no cheats, 3
   standard axioms.  Front 1-259 = 2BLOCK verbatim modulo USHR_128_8BL_LEMMA (X9)
   and X5_ZERO_LEMMA2 (s260 tail branch).  Tail cascade resolved by the symbolic
   bl2_resolve_pc / _bdy / _16_taken resolvers (x5 = word(16+bl1); thresholds
   112..32 fall through, #16 TAKEN -> more_than_1).  Block-0 GHASH vs H^2 + block-1
   GHASH vs H = 2BLOCK verbatim, EXCEPT less_than_1's mask is the LE1BLOCK symbolic
   MK = word(2 EXP (8*bl1)-1) (X1 = (128+8*bl1) AND 0x7f bridged to (8*bl1) AND 0x7f
   by X1_MOD128_BRIDGE so MASK_LEMMA applies with bl:=bl1).  Bridge = the 2BLOCK
   GHASH_POLYVAL_ACC_2 route with block-1 element = word_bytereverse(word_and ct1 MK).
   ============================================================================ *)

needs "arm/proofs/aesv8_gcm_8x_enc_256_2block.ml";;

(* ---- new symbolic-bit_len helper lemmas (scaffold-proved) ---- *)

(* X1 = bit_len = 128 + 8*bl1 for the 2-block band.  The routine masks with X1 AND 0x7f;
   128 = 0 mod 128, so (128+8*bl1) AND 127 = (8*bl1) AND 127, letting MASK_LEMMA (stated over
   word(8*bl)) apply with bl:=bl1.  (Was referenced here but never defined; proved 2026-06-24.) *)
let X1_MOD128_BRIDGE = prove
 (`!bl1. bl1 <= 16
    ==> word_and (word (128 + 8 * bl1):int64) (word 127) =
        word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (128 + 8 * bl1):int64) = 128 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `128 + 8 * bl1 = 8 * bl1 + 1 * 128`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let USHR_128_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (128 + 8 * bl1):int64) 3 = word (16 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (128 + 8 * bl1):int64) = 128 + 8 * bl1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

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

(* ---- looser ival lemmas for the symbolic 2-block tail cascade (16+bl1 <= 32) ---- *)
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

(* Cascade resolvers (x5 = word(16+bl1)).  bl2_resolve_pc: cmp #k fall-through
   (16+bl1 < k).  bl2_resolve_pc_bdy: cmp #k fall-through with the boundary
   16+bl1 = k allowed (k=32).  bl2_resolve_pc16_taken: cmp #16 b.gt TAKEN. *)
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

(* ========================================================================= *)
(* The 17-31 byte band theorem (strong-ensures, masked-blend out_p postcond). *)
(* Direct C_ARGUMENTS entry at pc+0x18 (NO wrapper); exit pc+0x11d8.           *)
(* bit_len = 128 + 8*bl1: one FULL block 0 + one MASKED partial block 1.        *)
(* ========================================================================= *)

let AESV8_GCM_8X_ENC_256_LE2BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    plaintext0 plaintext1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4600) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4600) (out_p:int64, 32) /\
    nonoverlapping (word pc, 4600) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (ivec_p:int64, 16) /\
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
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (128 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = plaintext0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = plaintext1 /\
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
     (\s. read PC s = word (pc + 0x11d8) /\
          read (memory :> bytes128 out_p) s =
          word_xor plaintext0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor (word_and (word_xor plaintext1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
            (word (2 EXP (8 * bl1) - 1)))
            (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse (word_xor plaintext0 (aes256_encrypt ctr0
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]));
               word_bytereverse (word_and (word_xor plaintext1 (aes256_encrypt (gcm_ctr_inc ctr0)
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
                 (word (2 EXP (8 * bl1) - 1)))]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ctr1:int128 = gcm_ctr_inc ctr0` THEN
  FIRST_X_ASSUM(fun th ->
    if (try rhs(concl th) = `ctr1:int128` with _ -> false)
    then ASSUME_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  (* prologue 0x18..0x28 (5 instrs): X9=word(16+bl1), X16, X11, Prop3 const. *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (1--5) THEN
  MP_TAC(SPEC `bl1:num` USHR_128_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  (* CTR setup (6..30): step 1-at-a-time, fold, keep Q0,Q1,Q30. *)
  EVERY (map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (i--i) THEN
              GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [2;3;4;5;6;7]) (6--30)) THEN
  (* AES bulk: keep Q0,Q1, drop Q2-Q7,Q30. *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (31--89) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (90--178) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (179--189) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (190--259) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  (* X5 = ((16+bl1-1) & ~0x7f) + in_p = in_p; collapse so flags resolve. *)
  MP_TAC(SPEC `bl1:num` X5_ZERO_LEMMA2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_REFL; VAL_WORD_0; INT_SUB_REFL; IVAL_WORD_0; LE_REFL]) THEN
  (* cmp x0,x5 / b.ge tail: in_p - in_p = 0 -> branch to .tail (pc+3768). *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [260] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  (* ===== TAIL entry: sub x5,x4,x0 -> x5 = word(16+bl1); fold X4's ushr. ===== *)
  MP_TAC(SPEC `bl1:num` USHR_128_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (261--265) THEN mk_discard2 [2;3;4;5;6;30] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word (16+bl1))) in_p = word (16+bl1):int64`]) THEN
  (* ===== cascade 266-313: x5 = word(16+bl1); thresholds 112..32 fall through,
     #16 IS taken -> more_than_1 (pc+4340).  Symbolic resolvers (LE32 ival). ===== *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (266--270) THEN bl2_resolve_pc 270 112 3808 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (271--282) THEN bl2_resolve_pc 282 96 3856 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (283--290) THEN bl2_resolve_pc 290 80 3888 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (291--297) THEN bl2_resolve_pc 297 64 3916 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (298--303) THEN bl2_resolve_pc 303 48 3940 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (304--309) THEN bl2_resolve_pc_bdy 309 32 3964 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (310--313) THEN bl2_resolve_pc16_taken 313 4340 THEN
  (* ===== more_than_1 (block 0 full GHASH vs H^2): abbreviate ct0, fold, abbreviate ct1 ===== *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor plaintext0 (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]; DISCH_TAC] THEN
  ABBREV_TAC
    `ct0:int128 = word_xor plaintext0 (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (314--323) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor plaintext1 (aes256_encrypt (ctr1:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try lhs(concl th) = `ctr1:int128` with _ -> false)
      then GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th] else NO_TAC) THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]; DISCH_TAC] THEN
  ABBREV_TAC
    `ct1:int128 = word_xor plaintext1 (aes256_encrypt (ctr1:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (324--331) THEN
  DISCARD_OLDSTATE_TAC "s331" THEN
  (* X1 = (128+8*bl1) AND 0x7f = (8*bl1) AND 0x7f -> the LE1BLOCK mask pattern. *)
  MP_TAC(SPEC `bl1:num` X1_MOD128_BRIDGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  (* ===== less_than_1 (block 1 masked, MK = word(2 EXP (8*bl1)-1)).  Mirror LE1BLOCK:
     mask region -> collapse Q9 to word_and ct1 MK before rev64; masked-blend out_p store. *)
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_ENC_256_EXEC (332--345) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `word_and (ct1:int128) (word (2 EXP (8 * bl1) - 1)):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  REWRITE_TAC[INSERT2_JOIN] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE; DISCH_TAC] THEN
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_ENC_256_EXEC (346--347) THEN
  DISCARD_OLDSTATE_TAC "s347" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (348--351) THEN
  (* out_p block-1 store (st1 v9,[x2], x2=out_p+16): masked-blend spec form. *)
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s351:armstate) =
     word_xor (word_and (ct1:int128) (word (2 EXP (8 * bl1) - 1)))
       (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1))))`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(fun th ->
     if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s351` with _ -> false)
     then MP_TAC th else NO_TAC) THEN
   REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN
   DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BLEND_OR_XOR] THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s351` with _ -> false) &&
       (try is_comb(rand(concl th)) &&
            fst(dest_const(rator(rator(rand(concl th))))) = "word_xor" with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s351" THEN DISCH_TAC THEN
  (* GHASH multiply over the masked block-1 + single Prop3 reduction (folds both blocks). *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (352--367) THEN
  DISCARD_OLDSTATE_TAC "s367" THEN
  (* ===== GHASH bridge: read Q19 s367 = ghash_polyval_acc (byteswap128 h)(brev xi)
     [brev ct0; brev (word_and ct1 MK)] (block0 vs H^2, block1 masked vs H). ===== *)
  SUBGOAL_THEN
    `read Q19 (s367:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse ct0;
        word_bytereverse (word_and (ct1:int128) (word (2 EXP (8 * bl1) - 1)))]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s367`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s367` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
   FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `byteswap128 h2` with _ -> false)
     then GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th] else NO_TAC) THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [polyval_reduce_prop3] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
     [REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
   REWRITE_TAC[byteswap128] THEN
   REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_LIMBS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   REWRITE_TAC[WORD_XOR_0; SUBWORD0_LEMMAS] THEN REWRITE_TAC[WORD_XOR_0] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   FINISH_2BLK_TAC;
   ALL_TAC] THEN
  (* ===== ext+rev64 (368-369): Q19 -> word_bytereverse gval; store (370). ===== *)
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse ct0;
       word_bytereverse (word_and (ct1:int128) (word (2 EXP (8 * bl1) - 1)))]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (368--369) THEN
  SUBGOAL_THEN `read Q19 (s369:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s369`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s369` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [370] THEN
  (* ===== close: out_p block-1 (carried spec form) + xi_p (gval over brev ct0/ct1 masked)
     close by ASM after folding ctr1 = gcm_ctr_inc ctr0; MAYCHANGE frame by MONOTONE;
     out_p block-0 (= ct0, store predates abbrev) by the ct0 spec-form expansion. ===== *)
  ENSURES_FINAL_STATE_TAC THEN
  FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `ctr1:int128` with _ -> false)
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(FIRST_X_ASSUM(fun th ->
        if (try rhs(concl th) = `ct0:int128` with _ -> false)
        then GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [SYM th] else NO_TAC) THEN
      ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]));;

(* ========================================================================= *)
(* byte_list_at corollary (the XTS-style single-buffer form): out_p is one     *)
(* byte_list_at clause over aes_ctr_full_tail_bytes with nfull=1, tail=bl1     *)
(* (one full block 0 ++ first bl1 bytes of the masked block 1).  First binary  *)
(* consumer of BYTE_LIST_AT_NBLOCK_CTR at nfull=1.  Cheap postcond-weakening   *)
(* (ENSURES_POSTCONDITION_THM), no re-simulation.                              *)
(* ========================================================================= *)

let AESV8_GCM_8X_ENC_256_LE2BLOCK_BYTELIST = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    plaintext0 plaintext1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 outprev bl1.
    1 <= bl1 /\ bl1 <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4600) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4600) (out_p:int64, 32) /\
    nonoverlapping (word pc, 4600) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (ivec_p:int64, 16) /\
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
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (128 + 8 * bl1); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = plaintext0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = plaintext1 /\
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
     (\s. read PC s = word (pc + 0x11d8) /\
          byte_list_at
            (aes_ctr_full_tail_bytes ctr0 [plaintext0;plaintext1]
               [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14] 1 bl1)
            out_p (word (16 + bl1)) s /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse (word_xor plaintext0 (aes256_encrypt ctr0
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]));
               word_bytereverse (word_and (word_xor plaintext1 (aes256_encrypt (gcm_ctr_inc ctr0)
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
                 (word (2 EXP (8 * bl1) - 1)))]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC
   `\s. read PC s = word (pc + 0x11d8) /\
        read (memory :> bytes128 out_p) s =
          word_xor plaintext0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
        read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor (word_and (word_xor plaintext1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
            (word (2 EXP (8 * bl1) - 1)))
            (word_and outprev (word_not (word (2 EXP (8 * bl1) - 1)))) /\
        read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse (word_xor plaintext0 (aes256_encrypt ctr0
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]));
               word_bytereverse (word_and (word_xor plaintext1 (aes256_encrypt (gcm_ctr_inc ctr0)
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
                 (word (2 EXP (8 * bl1) - 1)))])` THEN
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
    MATCH_MP_TAC AESV8_GCM_8X_ENC_256_LE2BLOCK THEN ASM_REWRITE_TAC[]]);;
