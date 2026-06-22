# LE2BLOCK (17-31 byte band) scaffold — validated close, pending binary sim

**Date:** 2026-06-21. Goal: `AESV8_GCM_8X_ENC_256_LE2BLOCK_BYTELIST` — bit_len = 128 + 8*bl1,
1<=bl1<=16 (one FULL block 0 + one MASKED partial block 1), out_p postcond as the single
`byte_list_at (aes_ctr_full_tail_bytes ctr0 [pt0;pt1] keys 1 bl1) out_p (word (16+bl1))` clause.

## Control-flow finding (confirmed from the .S dispatch + the two existing proofs)
- 17-31 bytes: tail dispatch `cmp x5,#16; b.gt` is TAKEN (x5 = 16+bl1 > 16) -> `more_than_1`
  (full block 0, GHASH vs H^2) -> falls through to `less_than_1` (block 1).
- This is the SAME path the whole-block 2BLOCK takes (x5=32). The ONLY divergence is in
  `less_than_1`: mask is all-ones (whole) vs `word(2 EXP (8*bl1)-1)` (partial).
- So: front + block-0 (steps ~1-325) = whole-block 2BLOCK VERBATIM modulo the symbolic
  bit_len cascade (use LE1BLOCK's bl_resolve_pc / USHR_8BL_LEMMA / X5 machinery, retargeted
  to the 2-block tail PCs). less_than_1 tail = LE1BLOCK symbolic-mask stepping
  (MASK_LEMMA, BLEND_OR_XOR, Q9 mask collapse before rev64). Bridge = GHASH_POLYVAL_ACC_2
  with block-1 element = word_bytereverse (word_and ct1 MK).

## NOT ENSURES_SEQUENCE_TAC (re-confirmed)
The le-1block theorem cannot be plugged in as the `less_than_1` segment: at that PC the
accumulators already hold block 0's H^2 contribution (vs just folded xi in the standalone
1-block), so the intermediate state doesn't match; plus ENSURES_SEQUENCE_TAC is frame-
incompatible with our 4-region stack frame. Reuse = shared tactics/lemmas, not nested theorems.

## VALIDATED (cheap, mock-checked 2026-06-21): the byte_list_at close
Given the strong-ensures theorem `...LE2BLOCK` (EL 0 full block-0 read + masked-blend block-1
read + xi_p), the byte_list_at corollary closes via ENSURES_POSTCONDITION_THM +
BYTE_LIST_AT_NBLOCK_CTR (nfull=1). The 6 bridge antecedents discharge as:
  1<=bl1; bl1<=16; val(word(16+bl1))=16*1+bl1 (VAL_WORD_EQ, bl1<2^64);
  1<LENGTH[pt0;pt1] (=2); (!k<1. read = EL k ...) [k=0, WORD_ADD_0, 16*0];
  masked read [16*1 -> 16].
This is the same cheap postcond-weakening pattern as 2BLOCK_BYTELIST / LE1BLOCK_BYTELIST.

## DONE (2026-06-22): the strong-ensures binary simulation + byte_list corollary
`AESV8_GCM_8X_ENC_256_LE2BLOCK` (masked-blend postcond) AND
`AESV8_GCM_8X_ENC_256_LE2BLOCK_BYTELIST` (byte_list_at, nfull=1) PROVED end-to-end.
Final proof: `arm/proofs/aesv8_gcm_8x_enc_256_le2block.ml` (loadt-clean, no cheats,
3 standard axioms; ~8.4 min with the 2block dep cached).  Key pieces realised:
- Front 1-259 = 2BLOCK verbatim; X9 via USHR_128_8BL_LEMMA, s260 tail branch via X5_ZERO_LEMMA2.
- Tail cascade: x5 = word(16+bl1) symbolic.  New resolvers (LE32 ival lemmas):
  bl2_resolve_pc (fall-through #112..#48), bl2_resolve_pc_bdy (#32, boundary 16+bl1=32
  allowed), bl2_resolve_pc16_taken (#16 b.gt TAKEN -> more_than_1 pc+4340).
- Block-0 GHASH vs H^2 + block-1 GHASH vs H: 2BLOCK verbatim, EXCEPT less_than_1 mask.
- less_than_1 mask: X1 = (128+8*bl1) AND 0x7f, bridged to (8*bl1) AND 0x7f by the new
  X1_MOD128_BRIDGE so LE1BLOCK's MASK_LEMMA applies with bl:=bl1; Q9 collapses to
  word_and ct1 MK (MK = word(2 EXP (8*bl1)-1)); masked-blend out_p store via BLEND_OR_XOR.
- Bridge: 2BLOCK GHASH_POLYVAL_ACC_2 route, block-1 element = word_bytereverse(word_and ct1 MK).
- byte_list close: VALIDATED ENSURES_POSTCONDITION_THM + BYTE_LIST_AT_NBLOCK_CTR nfull=1
  (k<1 -> k=0 read EL 0; masked read EL 1; val(word(16+bl1))=16*1+bl1; 1<LENGTH[pt0;pt1]).
- Step-index note: the symbolic cascade single-steps each b.gt, so LE2BLOCK reaches
  more_than_1 at s313 (2BLOCK: s315), a -2 offset; downstream PCs identical (same code).

## PROGRESS 2026-06-22 — front replayed + helper lemmas proved

Confirmed (live, on the loaded 2block dep): the whole-block 2BLOCK front replays VERBATIM for
the symbolic 17-31 band through step s259 (prologue 1-5, CTR setup 6-30, AES bulk 31-178,
GHASH fold 179-259) — these are length-agnostic. The ONLY front changes are the symbolic
bit_len resolutions, for which two helper lemmas are now PROVED and should be pasted into the
LE2BLOCK proof (or aes_ctr_spec.ml):

```
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
```

WHERE THEY GO in the front (replacing 2BLOCK's concrete-32 handling):
- After the prologue (s5), X9 = `word_ushr (word(128+8*bl1)) 3`; rewrite with USHR_128_8BL_LEMMA
  to `word (16+bl1)` (analog of 2BLOCK using `word 32`).
- At the s260 branch `cmp x0,x5; b.ge`: x5 = `((byte_len-1)&~127)+in_p`. Rewrite x5's
  `word_and (word_sub (word(16+bl1)) (word 1)) (word ...80)` to `word 0` via X5_ZERO_LEMMA2 +
  USHR_128_8BL_LEMMA, then WORD_ADD_0 -> x5=in_p, so in_p-in_p=0 -> tail (INT_SUB_REFL like 2block).

## CASCADE divergence (the one real difference from 2BLOCK, still TODO in the script)
2BLOCK has x5=32 (concrete); LE2BLOCK has x5 = word(16+bl1), symbolic. The tail cascade
`cmp x5,#112/.../16; b.gt` must resolve: for 17<=byte_len<=31, all b.gt for thresholds 112..32
are NOT taken, and `cmp x5,#16; b.gt` IS taken -> more_than_1 (block 0 full). Need a
`bl_resolve`-style resolver for x5=16+bl1 at the 2block tail PCs (LE1BLOCK's bl_resolve_pc is
for x5=bl with ALL falling through; here the #16 compare is TAKEN). Build a small variant:
val(word(16+bl1)) = 16+bl1 (VAL_WORD_EQ), and 16+bl1 > 16 (since bl1>=1), 16+bl1 <= 31 < 32.

## REMAINING (script it, loadt-iterate; do NOT live-step — 370 steps, b() reverts everything)
1. Front 1-259 verbatim from 2BLOCK + the two helper lemmas above for X9/X5.
2. Cascade 260-~315: resolve to more_than_1 (block 0 full, x5=16+bl1>16) then less_than_1.
3. block-0 more_than_1 GHASH vs H^2: verbatim from 2BLOCK.
4. less_than_1 block-1: MIRROR LE1BLOCK symbolic mask (Q9 collapse to word_and ct1 MK before
   rev64, MASK_LEMMA, BLEND_OR_XOR), GHASH vs H. mask MK = word(2 EXP (8*bl1)-1).
5. bridge: GHASH_POLYVAL_ACC_2 with block-1 element = word_bytereverse (word_and ct1 MK)
   (2BLOCK bridge, but block1 masked). then ext+rev64+store, ENSURES_FINAL_STATE.
6. byte_list_at corollary: VALIDATED close (ENSURES_POSTCONDITION_THM + BYTE_LIST_AT_NBLOCK_CTR
   nfull=1) — see scaffold above.
