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

## REMAINING (expensive): the strong-ensures binary simulation
`AESV8_GCM_8X_ENC_256_LE2BLOCK` (masked-blend postcond). ~22 ARM_STEPS sections, symbolic
bit_len, ~17 min/loadt, multi-cycle. Front+block0 paste from 2block; tail mirrors LE1BLOCK.
This is the only piece left and is a dedicated stepping effort.
