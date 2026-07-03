(* ========================================================================= *)
(* AESV8_GCM_8X_DEC_256, the 1-16 byte band (decrypt): bit_len = 8*bl,        *)
(* 1 <= bl <= 16, nfull = 0 (a single, possibly partial, masked block).       *)
(*                                                                            *)
(* First band of the decrypt chain  core -> le1block -> le2block -> .. ->     *)
(* le8block.  Unlike le2..le8 this band never enters the more_than_k tail     *)
(* path (no full blocks), so it has its own front (not DEC_FRONT_TAC) and     *)
(* closes with the 1-term GHASH bridge GMULT_FULL_CORRECT_BA.  The bl=16      *)
(* endpoint (all-ones mask) is the whole-1-block (16-byte) case, so the       *)
(* formerly separate whole-1-block theorem was removed as redundant.          *)
(*                                                                            *)
(* Machine code, EXEC rule and all shared machinery come from core.  This is  *)
(* the band section split out of the former aesv8_gcm_8x_dec_256_1block.ml    *)
(* (STEP D part 1 of _docs/dec-band-homogenization-convergence-plan.md).      *)
(*                                                                            *)
(* NOTE: besides the band theorem, this file defines the shared MASKED-TAIL   *)
(* lemmas (INSERT2_JOIN, MASK_LEMMA, BLEND_OR_XOR) used by EVERY band's        *)
(* less_than_1 masked block; le2..le8 reach them through this file in the     *)
(* linear needs chain.                                                        *)
(* No CHEAT_TAC, no new axioms.                                               *)
(* ========================================================================= *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_core.ml";;

(* Precondition note: the Prop3 GHASH reduction constant 0xC200000000000000 is written to
   [SP+64] by the function prologue (MOVZ X5,0xC200<<48; STP X5 XZR,[SP+64] at 0x24/0x28)
   BEFORE the pc+0x2c entry, so it is carried as the precondition
   `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 13979173243358019584`.
   The tail reloads it (LDR D16,[SP+64], ~step 341) for the polyval reduction; it is the w
   constant in GMULT_FULL_CORRECT_BA.
   NOTE: HOL term quotations do NOT accept (* *) comments — keep all such notes outside the
   backticks (a stray in-term comment makes the whole `prove` fail to parse). *)
(* BODY theorem: enters at pc+0x2c, AFTER the prologue's arg-setup (lsr/mov/mov/movz/stp/add
   at 0x18..0x2c), so it states the post-setup registers (X9=byte_len, X16=ivec_p, X11=key_p)
   and the Prop3 constant already stored at [SP+64].  The C_ARGUMENTS entry point pc+0x18 is
   handled by AESV8_GCM_8X_DEC_256_1BLOCK below, which steps the 5 setup instructions and
   composes with this body via ENSURES_TRANS.  The prologue reorder (saves grouped
   first, then setup) is what lets pc+0x18 still hold the C arguments in X0..X6 — see the
   .S header and the methodology doc for the divergence from the aws-lc original. *)
(* ------------------------------------------------------------------------- *)
(* Full correctness from the C arguments (XTS-style single theorem).          *)
(*                                                                            *)
(* Enter at the function's natural arg-passing point pc+0x18 (after the        *)
(* prologue's callee-saved STPs, before the arg-setup), so the AArch64 C       *)
(* arguments are still in X0..X6 and are stated with                          *)
(* C_ARGUMENTS [in_p; bit_len(=128); out_p; xi_p; ivec_p; key_p; htbl_p].      *)
(* This is what the prologue REORDER enables (see the .S header / doc).        *)
(*                                                                            *)
(* The proof is structured in two segments composed by ENSURES_TRANS (NOT     *)
(* ENSURES_SEQUENCE_TAC: its MAYCHANGE_IDEMPOT_TAC throws on the 4-memory-     *)
(* region stack frame), with ENSURES_FRAME_SUBSUMED relaxing the              *)
(* (C_setup ,, C_body) frame to the stated frame first:                       *)
(*  - Front (pc+0x18 -> pc+0x2c): the 5 setup instructions (0x18 lsr;          *)
(*    0x1c/0x20 mov; 0x24 movz; 0x28 stp) derive X9=byte_len, X16=ivec_p,      *)
(*    X11=key_p and write the Prop3 constant to [SP+64].  Two non-obvious      *)
(*    requirements for ARM_VSTEPS_TAC (1--5) to carry the input bytes128 reads *)
(*    ACROSS the `stp x5,xzr,[sp,64]` 16-byte store: (a) each input buffer is  *)
(*    stated disjoint from the FULL 80-byte stack frame (stackpointer,80) (the *)
(*    narrow (sp+64,8) the body stepping uses is too small for the 16B store); *)
(*    (b) do NOT rewrite the `nonoverlapping` hyps into nonoverlapping_modulo  *)
(*    form before stepping -- the read-over-write solver matches on            *)
(*    `nonoverlapping`, and the modulo form silently drops every memory read.  *)
(*  - Back (pc+0x2c -> pc+0x11e4): the full 1-block run inline (AES rounds,    *)
(*    branch cascade to the less_than_1 path, GHASH multiply/reduce, bridge    *)
(*    via GMULT_FULL_CORRECT_BA, store to out_p/xi_p).  The (sp+64,8)          *)
(*    sub-region disjointness the body stepping needs is derived from the      *)
(*    (sp,80) facts up front by NONOVERLAPPING_TAC.                            *)
(*                                                                            *)
(* Methodology / lessons: _docs/aesv8-gcm-8x-dec-256-1block-methodology-       *)
(* 20260611.md.                                                               *)
(* ------------------------------------------------------------------------- *)
(* ===========================================================================
   The whole-1-block theorem AESV8_GCM_8X_DEC_256_1BLOCK (bit_len = 128) has been
   REMOVED: the whole-1-block (16-byte) case is the bl=16 endpoint of
   AESV8_GCM_8X_DEC_256_LE1BLOCK below (band 1..16, all-ones mask = full block),
   which is proved independently (its own symbolic-bl simulation, NOT via the
   whole-block theorem).  The dedicated whole-block theorem was referenced nowhere.
   The length/flag helper lemmas and LE1BLOCK that follow are retained.
   =========================================================================== *)

(* ========================================================================= *)
(* Byte-aligned <=1-block decryption: bit_len = 8*bl, 1 <= bl <= 16.          *)
(*                                                                            *)
(* Generalizes the full-block 1-block body (bit_len = 128) to a partial       *)
(* last block of any whole number of bytes, in ONE symbolic-bl run (no        *)
(* case-split on the simulation). The masking path (mask = word(2^(8*bl)-1))  *)
(* is dead from the aws-LC caller, which only passes whole blocks, but the    *)
(* theorem is proven for completeness / any subsequent use.                   *)
(*                                                                            *)
(* Postconditions for the partial block:                                      *)
(*   out_p := word_xor (word_and plaintext MK) (word_and outprev (~MK))       *)
(*   xi_p  := GHASH over (word_and ciphertext MK),  MK = word(2^(8*bl)-1)      *)
(* (At bl=16, MK is all-ones and these collapse to the full-block forms.)     *)
(*                                                                            *)
(* Entry/exit PCs and the MAYCHANGE frame are identical to the full-block     *)
(* BODY; the extra `outprev` precondition is read by the `bif` blend.         *)
(*                                                                            *)
(* Proof methodology and the genuine lessons (one symbolic-bl run; the mask-   *)
(* collapse WORD_BLAST trap and the MASK_LEMMA/INSERT2_JOIN/BLEND_OR_XOR fix;  *)
(* the tail = full-block tail with cph -> word_and cph MK) are written up in   *)
(* _docs/aesv8-gcm-8x-dec-256-1block-methodology-20260611.md section 11.       *)
(* ========================================================================= *)
(* ---- length/flag helper lemmas ---- *)
let X5_ZERO_LEMMA = prove
 (`!bl. 1 <= bl /\ bl <= 16
        ==> word_and (word_sub (word bl) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word bl:int64) (word 1) = word (bl - 1)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[WORD_SUB] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(word 18446744073709551488:int64) = word_not (word (2 EXP 7 - 1))`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (bl - 1):int64) = bl - 1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(bl - 1) DIV 2 EXP 7 = 0`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ARITH_TAC);;

let USHR_8BL_LEMMA = prove
 (`!bl. bl <= 16 ==> word_ushr (word (8 * bl):int64) 3 = word bl`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (8 * bl):int64) = 8 * bl`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let IVAL_WORD_BL = prove
 (`!bl. bl <= 16 ==> ival (word bl:int64) = &bl`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival] THEN
  SUBGOAL_THEN `val (word bl:int64) = bl` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  ASM_SIMP_TAC[ARITH_RULE `bl <= 16 ==> bl < 2 EXP (64 - 1)`]);;

let IVAL_WSUB_BL = prove
 (`!bl k. bl <= 16 /\ k <= 112
          ==> ival (word_sub (word bl) (word k):int64) = &bl - &k`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let INSERT2_JOIN = prove
 (`!(j:int128) (a:int64) (b:int64).
      word_insert ((word_insert j (0,64) a):int128) (64,64) b = (word_join b a:int128)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[DIMINDEX_128] THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_WORD_INSERT; BIT_WORD_JOIN] THEN
  REWRITE_TAC[DIMINDEX_128; DIMINDEX_64] THEN
  REWRITE_TAC[SUB_0; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* ---- bounded enumeration 1<=bl<=16 -> bl=1 \/ ... \/ bl=16.  Proved by STRUCTURAL LE
   unfolding (REWRITE[LE] after rewriting each numeral to SUC form), NOT by ARITH_TAC:
   ASM_ARITH_TAC / ARITH_TAC on this 16-way disjunctive conclusion takes ~92s (the linear-
   arith DNF blows up), whereas the LE rewrite is ~0.07s. ---- *)
let BL16_DISJ = prove
 (`!bl. 1 <= bl /\ bl <= 16
        ==> bl = 1 \/ bl = 2 \/ bl = 3 \/ bl = 4 \/ bl = 5 \/ bl = 6 \/ bl = 7 \/ bl = 8 \/
            bl = 9 \/ bl = 10 \/ bl = 11 \/ bl = 12 \/ bl = 13 \/ bl = 14 \/ bl = 15 \/ bl = 16`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE`16=SUC 15`;ARITH_RULE`15=SUC 14`;ARITH_RULE`14=SUC 13`;ARITH_RULE`13=SUC 12`;
    ARITH_RULE`12=SUC 11`;ARITH_RULE`11=SUC 10`;ARITH_RULE`10=SUC 9`;ARITH_RULE`9=SUC 8`;
    ARITH_RULE`8=SUC 7`;ARITH_RULE`7=SUC 6`;ARITH_RULE`6=SUC 5`;ARITH_RULE`5=SUC 4`;
    ARITH_RULE`4=SUC 3`;ARITH_RULE`3=SUC 2`;ARITH_RULE`2=SUC 1`] THEN
  REWRITE_TAC[LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISJ1_TAC THEN ASM_REWRITE_TAC[GSYM LE_ANTISYM]);;

(* ---- the asm's lsr/csel partial-block mask at s328 = word(2^(8*bl)-1)
   (per-bl reduction, NOT WORD_BLAST; see methodology doc section 11b for why;
   the one slow one-time lemma). ---- *)
let MASK_LEMMA = prove
 (`!bl. 1 <= bl /\ bl <= 16 ==>
    word_join
     (if ~(ival (word_sub (word_and (word_sub (word 0:int64)
              (word_sub (word_and (word (8 * bl):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0:int64)
              (word_sub (word_and (word (8 * bl):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0:int64)
              (word_sub (word_and (word (8 * bl):int64) (word 127)) (word 128))) (word 127)) (word 64))))
      then word_jushr (word 18446744073709551615:int64)
             (word_and (word_sub (word 0:int64)
                (word_sub (word_and (word (8 * bl):int64) (word 127)) (word 128))) (word 127))
      else word 0)
     (if ~(ival (word_sub (word_and (word_sub (word 0:int64)
              (word_sub (word_and (word (8 * bl):int64) (word 127)) (word 128))) (word 127)) (word 64)) < &0 <=>
           ~(ival (word_and (word_sub (word 0:int64)
              (word_sub (word_and (word (8 * bl):int64) (word 127)) (word 128))) (word 127)) - &64 =
             ival (word_sub (word_and (word_sub (word 0:int64)
              (word_sub (word_and (word (8 * bl):int64) (word 127)) (word 128))) (word 127)) (word 64))))
      then (word 18446744073709551615:int64)
      else word_jushr (word 18446744073709551615:int64)
             (word_and (word_sub (word 0:int64)
                (word_sub (word_and (word (8 * bl):int64) (word 127)) (word 128))) (word 127))):int128 =
    word (2 EXP (8 * bl) - 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BL16_DISJ o CONJ (ASSUME `1 <= bl`)) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV THENC
    WORD_REDUCE_CONV THENC ONCE_DEPTH_CONV INT_REDUCE_CONV THENC
    REWRITE_CONV[] THENC WORD_REDUCE_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV));;

(* word_or -> word_xor for complementary masks (the `bif` blend of plaintext/outprev) *)
let BLEND_OR_XOR = prove
 (`!x y m:int128. word_or (word_and x m) (word_and y (word_not m)) =
                  word_xor (word_and x m) (word_and y (word_not m))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ---- branch-PC resolver: for a b.gt-cascade branch at state sN comparing word bl
   against K (K<=112, bl<=16 so bl<K), the branch falls through to word(pc+fall). ---- *)
let bl_resolve_pc sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    MP_TAC(SPECL [`bl:num`; mk_small_numeral k] IVAL_WSUB_BL) THEN
    ASM_SIMP_TAC[IVAL_WORD_BL] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf "&bl - &%d:int < &0" k)) ASSUME_TAC THENL
     [MP_TAC(ASSUME `bl <= 16`) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE (parse_term (Printf.sprintf
       "bl <= 16 ==> ~(bl + 2 EXP 64 - %d = 0)" k))] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]; ALL_TAC]);;

(* the K=16 last branch needs bl=16 handled too (word_sub(word 16)(word 16)=0) *)
let bl_resolve_pc16 sN fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    MP_TAC(SPECL [`bl:num`; `16`] IVAL_WSUB_BL) THEN
    ASM_SIMP_TAC[IVAL_WORD_BL; ARITH_RULE `16 <= 112`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `bl = 16` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[];
      SUBGOAL_THEN `&bl - &16:int < &0` ASSUME_TAC THENL
       [MP_TAC(ASSUME `bl <= 16`) THEN MP_TAC(ASSUME `~(bl = 16)`) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]]; ALL_TAC]);;

(* ---- the byte-aligned theorem, C_ARGUMENTS entry at pc+0x18 (XTS-style) ----
   AESV8_GCM_8X_DEC_256_LE1BLOCK: enters at pc+0x18 with the C arguments in X0..X6
   (bit_len = word(8*bl)); the prologue reorder (saves-first) makes this hold.  The
   5-instruction arg-setup (pc+0x18 -> pc+0x2c) is composed with the byte-aligned body
   inline via ENSURES_FRAME_SUBSUMED + ENSURES_TRANS (see the full-block AESV8_GCM_8X_DEC_256_1BLOCK
   for the identical front recipe; X9 = lsr(word(8*bl),3) = word bl by USHR_8BL_LEMMA). *)
let AESV8_GCM_8X_DEC_256_LE1BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk outprev bl.
    1 <= bl /\ bl <= 16 /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4612) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4612) (out_p:int64, 16) /\
    nonoverlapping (word pc, 4612) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4612) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (xi_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 240) /\
    nonoverlapping (out_p, 16) (htbl_p, 192) /\
    nonoverlapping (out_p, 16) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (8 * bl); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read X9 s = word bl /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = cph /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 out_p) s = outprev /\
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
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk)
     (\s. read PC s = word (pc + 0x11e4) /\
          read (memory :> bytes128 out_p) s =
          word_xor (word_and (word_xor cph (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
            (word (2 EXP (8 * bl) - 1)))
            (word_and outprev (word_not (word (2 EXP (8 * bl) - 1)))) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse (word_and cph (word (2 EXP (8 * bl) - 1)))]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 16); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(stackpointer:int64, 80)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `(MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, 16); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16); memory :> bytes(stackpointer:int64, 80)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]) ,,
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, 16); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16);
                memory :> bytes(word_add stackpointer (word 64):int64, 8)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN
  EXISTS_TAC
   `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
        read PC s = word (pc + 0x2c) /\ read SP s = stackpointer /\
        read X0 s = in_p /\ read X1 s = word (8 * bl) /\
        read X9 s = word bl /\ read X2 s = out_p /\
        read X3 s = xi_p /\ read X16 s = ivec_p /\
        read X11 s = key_p /\ read X6 s = htbl_p /\
        read Q30 s = ctr0 /\
        read (memory :> bytes128 in_p) s = cph /\
        read (memory :> bytes128 xi_p) s = xi /\
        read (memory :> bytes128 ivec_p) s = ctr0 /\
        read (memory :> bytes128 out_p) s = outprev /\
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
        read (memory :> bytes64 (word_add stackpointer (word 64))) s =
          word 13979173243358019584` THEN
  CONJ_TAC THENL
  [(* Front: 5 setup instructions 0x18..0x28 -> pc+0x2c.  X9 = lsr(word(8*bl),3) = word bl
       (USHR_8BL_LEMMA).  Keep nonoverlapping NATIVE so the [sp,64] store carries the reads. *)
   REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
   ENSURES_INIT_TAC "s0" THEN
   RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
   ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (1--5) THEN
   ASM_SIMP_TAC[USHR_8BL_LEMMA] THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[USHR_8BL_LEMMA] THEN
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MONOTONE_MAYCHANGE_TAC;
   (* Back (pc+0x2c -> exit): the (sp+64,8) sub-region disjointness from the (sp,80) facts;
      then the byte-aligned 1-block body inline. *)
   SUBGOAL_THEN
    `nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 64):int64,8) /\
     nonoverlapping (xi_p:int64,16) (word_add stackpointer (word 64):int64,8) /\
     nonoverlapping (out_p:int64,16) (word_add stackpointer (word 64):int64,8)`
    STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  (* === AES rounds + counter setup (length-agnostic), steps 1-254 === *)
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (1--8) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (9--11) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (12--13) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (14--15) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (16--17) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (18--19) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (20--21) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (22--23) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (24--25) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (26--84) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (85--173) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (174--177) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (178--184) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (185--254) THEN DISCARD_COUNTER_REGS_TAC THEN
  (* X5 = ((bl-1) & ~0x7f) + in_p = in_p; collapse so flags resolve. *)
  MP_TAC(SPEC `bl:num` X5_ZERO_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_REFL; VAL_WORD_0; INT_SUB_REFL; IVAL_WORD_0; LE_REFL]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (255--265) THEN DISCARD_COUNTER_REGS_TAC THEN
  (* X4 = in_p + ushr(8*bl,3) = in_p + word bl ; X5 = (in_p+word bl)-in_p = word bl. *)
  MP_TAC(SPEC `bl:num` USHR_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word bl)) in_p = word bl:int64`]) THEN
  SUBGOAL_THEN `val (word bl:int64) = bl` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* === branch cascade 266-311: all 7 b.gt fall through (bl<=16), reach less_than_1 pc+4408 === *)
  bl_resolve_pc 265 112 3808 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (266--277) THEN bl_resolve_pc 277 96 3856 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (278--285) THEN bl_resolve_pc 285 80 3888 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (286--292) THEN bl_resolve_pc 292 64 3916 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (293--298) THEN bl_resolve_pc 298 48 3940 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (299--304) THEN bl_resolve_pc 304 32 3964 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (305--308) THEN bl_resolve_pc16 308 3980 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (309--311) THEN
  (* === less_than_1 block: mask region 312-328 === *)
  ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (312--328) THEN
  DISCARD_OLDSTATE_TAC "s328" THEN
  (* collapse the symbolic mask to word(2^(8*bl)-1) on Q9 (INSERT2_JOIN + MASK_LEMMA). *)
  FIRST_X_ASSUM(MP_TAC o SPEC `word_and cph (word (2 EXP (8 * bl) - 1)):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  REWRITE_TAC[INSERT2_JOIN] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE;
    DISCH_TAC] THEN
  (* === GHASH multiply over the masked block; Q12 = masked output blend === *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_EXEC (329--340) THEN
  SUBGOAL_THEN
    `read Q12 (s340:armstate) =
     word_xor (word_and (word_xor cph (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))
       (word (2 EXP (8 * bl) - 1)))
       (word_and outprev (word_not (word (2 EXP (8 * bl) - 1))))`
    ASSUME_TAC THENL
  [(* Q12 = word_or (and PT_tower MASK) (and outprev (~MASK)): expand both AES towers,
      INSERT2_JOIN + MASK_LEMMA collapse the mask, BLEND_OR_XOR turns word_or->word_xor,
      WORD_RULE closes the XOR-assoc (aes-tower as atom). See methodology doc section 11b. *)
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ASM_REWRITE_TAC[INSERT2_JOIN] THEN ASM_SIMP_TAC[MASK_LEMMA] THEN
   REWRITE_TAC[BLEND_OR_XOR] THEN REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read Q12 s340` with _ -> false) then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s340" THEN DISCH_TAC THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (341--344) THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s344` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s344" THEN DISCH_TAC THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (345--350) THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC [351] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s344` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s351" THEN DISCH_TAC THEN
  (* === GHASH bridge over the MASKED block (cph -> word_and cph MK) === *)
  SUBGOAL_THEN
    `read Q19 (s351:armstate) =
     polyval_dot (word_xor (word_bytereverse xi)
       (word_bytereverse (word_and cph (word (2 EXP (8 * bl) - 1)))))
       (byteswap128 h)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s351`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s351` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   GEN_REWRITE_TAC RAND_CONV
     [GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
        (ISPECL [`word_xor (word_bytereverse xi)
                   (word_bytereverse (word_and cph (word (2 EXP (8 * bl) - 1)))) : int128`;
          `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))] THEN
   REWRITE_TAC[byteswap128] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_PMUL_ATOMS_TAC THEN
   REWRITE_TAC[WORD_XOR_0; SUBWORD0_LEMMAS] THEN REWRITE_TAC[WORD_XOR_0] THEN
   REWRITE_TAC[PMUL_W_64_128] THEN
   REWRITE_TAC[JOINMID] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   ABBREV_TAC `xll:64 word = word_subword (qq0:int128) (0,64)` THEN
   ABBREV_TAC `xlh:64 word = word_subword (qq0:int128) (64,64)` THEN
   ABBREV_TAC `xhl:64 word = word_subword (qq1:int128) (0,64)` THEN
   ABBREV_TAC `xhh:64 word = word_subword (qq1:int128) (64,64)` THEN
   ABBREV_TAC `xml:64 word = word_subword (qq2:int128) (0,64)` THEN
   ABBREV_TAC `xmh:64 word = word_subword (qq2:int128) (64,64)` THEN
   ABBREV_TAC
    `r1:(128)word = word_xor (word_xor (word_shl (word_zx (xhl:(64)word):(128)word) 63)
                                       (word_shl (word_zx xhl:(128)word) 62))
                             (word_shl (word_zx xhl:(128)word) 57)` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (0,64):(64)word)
                        (word_subword (word_shl (word_zx xhl:(128)word) 62) (0,64):(64)word))
              (word_subword (word_shl (word_zx xhl:(128)word) 57) (0,64):(64)word) =
     word_subword (r1:(128)word) (0,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (64,64):(64)word)
                        (word_subword (word_shl (word_zx xhl:(128)word) 62) (64,64):(64)word))
              (word_subword (word_shl (word_zx xhl:(128)word) 57) (64,64):(64)word) =
     word_subword (r1:(128)word) (64,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   ABBREV_TAC `u:(64)word = word_xor (word_xor (word_subword (r1:128 word) (0,64)) (xhh:64 word)) (word_xor (word_xor (xll:64 word) (xhl:64 word)) (xml:64 word))` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (xhh:64 word) (word_xor (word_xor (xml:64 word) (xhl:64 word)) (xll:64 word))) (word_subword (r1:128 word) (0,64)) = u`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   ABBREV_TAC
    `r2:(128)word = word_xor (word_xor (word_shl (word_zx (u:(64)word):(128)word) 63)
                                       (word_shl (word_zx u:(128)word) 62))
                             (word_shl (word_zx u:(128)word) 57)` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63) (0,64):(64)word)
                        (word_subword (word_shl (word_zx u:(128)word) 62) (0,64):(64)word))
              (word_subword (word_shl (word_zx u:(128)word) 57) (0,64):(64)word) =
     word_subword (r2:(128)word) (0,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63) (64,64):(64)word)
                        (word_subword (word_shl (word_zx u:(128)word) 62) (64,64):(64)word))
              (word_subword (word_shl (word_zx u:(128)word) 57) (64,64):(64)word) =
     word_subword (r2:(128)word) (64,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse (word_and cph (word (2 EXP (8 * bl) - 1))))) (byteswap128 h)` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (352--353) THEN
  SUBGOAL_THEN `read Q19 (s353:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s353`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s353` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [354] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(EXPAND_TAC "gval" THEN AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT]) THEN
  TRY(CONV_TAC WORD_BLAST) THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[])]);;
