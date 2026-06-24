# Plan: dec ≤2-block generic `byte_list_at` (with proven masked partial tail)

**Goal (user, 2026-06-24):** Not a per-block postcondition. A single dec proof using the
**generic `byte_list_at`** spec that covers ≤2 blocks **including a partial (1..16-byte)
final block**, with the masked tail **proven** (the aws-lc caller passes whole blocks, but
we match Mila and prove the masked-tail path anyway).

Two deliverables, in order:
1. Keep the whole-2-block proof we just finished (`AESV8_GCM_8X_DEC_256_2BLOCK` +
   `_BYTELIST`, GMULT2 fast bridge) — done, committed.
2. Add `AESV8_GCM_8X_DEC_256_LE2BLOCK` (bit_len = 128 + 8·bl1, 1≤bl1≤16: one FULL block 0 +
   one MASKED partial block 1) and its generic `byte_list_at` form
   `AESV8_GCM_8X_DEC_256_LE2BLOCK_BYTELIST`.

## This is a MIRROR PORT, not greenfield
The enc side already did exactly this: `arm/proofs/aesv8_gcm_8x_enc_256_le2block.ml`
proves `AESV8_GCM_8X_ENC_256_LE2BLOCK` (+ `_BYTELIST`) — one full + one masked block at
nfull=1 — and is the "first binary consumer of `BYTE_LIST_AT_NBLOCK_CTR` at nfull=1".
The dec port reuses ALL of the following, which already exist and are proven:

### Spec layer (generic, already proven — our analog of Mila's aes256_gcm_encrypt/OUT_BRIDGE_GEN)
- `arm/proofs/utils/aes_ctr_spec.ml`:
  - `aes_ctr_full_tail_bytes ctr0 pts keys nfull tail` (L354): APPEND of nfull full blocks
    (`int128_list_to_bytes (SUB_LIST(0,nfull)(aes_ctr ...))`) + `SUB_LIST(0,tail)` of the
    masked block `word_and (EL nfull (aes_ctr ...)) (word (2 EXP (8*tail) - 1))`. This IS the
    generic byte-list spec (= Mila's `aes256_gcm_encrypt` shape: nfull full + tail masked).
  - `BYTE_LIST_AT_NBLOCK_CTR` (L406): the generic OUTPUT BRIDGE (= Mila's `OUT_BRIDGE_GEN`):
    from {nfull whole-block readbacks + one masked-tail readback
    `word_xor (word_and blk mask)(word_and outprev (word_not mask))`} concludes
    `byte_list_at (aes_ctr_full_tail_bytes ...) out_p len s`. Already proven, generic in nfull/tail.

### Tail-masking machinery (already proven for dec)
- `arm/proofs/aesv8_gcm_8x_dec_256_1block.ml`:
  - `MASK_LEMMA` (L2306): symbolic mask collapse `word_and ... = word (2 EXP (8*bl) - 1)`.
  - `BLEND_OR_XOR` (L2339): `word_or (word_and x m)(word_and y (word_not m)) = word_xor ...`.
  - `INSERT2_JOIN`, `X1_MOD128_BRIDGE` (enc has the analog) — mask-region resolvers.
  - `AESV8_GCM_8X_DEC_256_LE1BLOCK` (L2385): the dec masked ≤1-block proof (1≤bl≤16) with the
    `word_or(word_and cph mask)(word_and outprev (word_not mask))` store + `byte_list_at` form.
    This is the dec analog of enc LE1BLOCK and proves the single masked block path end-to-end.

### GHASH bridge (just finished — reuse directly)
- `AESV8_GCM_8X_DEC_256_2BLOCK`'s `DEC_2BLK_GMULT2_BRIDGE_TAC` + `GMULT2_FULL_CORRECT_BA`
  (in `aesv8_gcm_8x_dec_256_2block.ml`). For LE2BLOCK the block-1 GHASH element is the MASKED
  ciphertext `word_bytereverse (word_and cph1 MK)` instead of `word_bytereverse cph1`; the
  bridge is otherwise identical (GHASH_POLYVAL_ACC_2 route, block0 vs H^2, block1 vs H).

## What the dec LE2BLOCK proof must do (mirror of enc le2block.ml, dec dataflow)
File: NEW `arm/proofs/aesv8_gcm_8x_dec_256_le2block.ml`, `needs` the dec 2block file (for the
EXEC rule + GMULT2 bridge helpers) + the dec 1block file (MASK_LEMMA / LE1BLOCK machinery).

1. **Statement** `AESV8_GCM_8X_DEC_256_LE2BLOCK`: precondition `1 <= bl1 /\ bl1 <= 16`,
   `C_ARGUMENTS [...; word (128 + 8*bl1); ...]` (X1 = bit_len). Postcondition:
   - out_p block 0 (full) = `word_xor cph0 (aes256_encrypt ctr0 keys)` (the plaintext);
   - out_p block 1 (masked) = `word_xor (word_and pt1 MK)(word_and outprev (word_not MK))`
     where `pt1 = word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0) keys)`, `MK = word(2 EXP (8*bl1)-1)`;
   - xi_p = `word_bytereverse (ghash_polyval_acc (byteswap128 h)(brev xi)
       [brev cph0; brev (word_and cph1 MK)])`.
   (Compare enc le2block.ml L132-206; swap pt<->cph per dec mirror: dec GHASHes the loaded
    INPUT ciphertext, so the block-1 GHASH element is `brev (word_and cph1 MK)`.)

2. **Front (1..~313)**: identical structure to the whole-2-block dec proof up to the tail
   branch, BUT the tail branch now goes through the masked path. Reuse the dec 2block front
   tactics; the cmp/b.ge tail uses the symbolic `16+bl1` cascade (enc's
   X5_ZERO_LEMMA2 / X1_MOD128_BRIDGE analogs — port the dec versions or lift from enc le2block).

3. **Block 0 (full)**: more_than_1 path, same as whole-2-block (store pt0, GHASH cph0 vs H^2).

4. **Block 1 (masked)**: less_than_1 path. The mask region collapses Q9 to
   `word_and cph1 MK` BEFORE the rev64 (MASK_LEMMA + INSERT2_JOIN), and the out_p+16 store is
   the masked blend `word_or(word_and pt1 MK)(word_and outprev (word_not MK))`. This is the
   dec LE1BLOCK masked-store machinery applied to block 1. Block-1 GHASH element =
   `word_bytereverse (word_and cph1 MK)`.

5. **Bridge at s370-analog**: `DEC_2BLK_GMULT2_BRIDGE_TAC` with block-1 = masked
   `word_and cph1 MK` (the GMULT2 lemma is operand-generic, so it applies with a1 = brev of the
   masked block; only the concrete cph1 term changes to `word_and cph1 MK`).

6. **`_BYTELIST` corollary** `AESV8_GCM_8X_DEC_256_LE2BLOCK_BYTELIST`: postcondition
   `byte_list_at (aes_ctr_full_tail_bytes ctr0 [cph0;cph1] keys 1 bl1) out_p len s` (nfull=1,
   tail=bl1), proved by ENSURES_POSTCONDITION_THM + `BYTE_LIST_AT_NBLOCK_CTR` (the generic
   bridge), exactly the enc le2block.ml L401 pattern.

## Then: collapse to ONE ≤2-block theorem (the "single generic" deliverable)
After both whole-2-block and LE2BLOCK exist, add a dispatch theorem
`AESV8_GCM_8X_DEC_256_LE2BLOCK_CORRECT` (mirror of Mila's `AES256_GCM_ENCRYPT_CORRECT` cascade)
with hypothesis `1 <= val len /\ val len <= 32` (bytes) and a single postcondition
`byte_list_at (aes_ctr_full_tail_bytes ctr0 [cph0;cph1] keys nfull tail) out_p len s`,
proved by `ASM_CASES_TAC` on `val len <= 16` dispatching to LE1BLOCK_BYTELIST (nfull=0,tail=len)
vs the 17..32 band (nfull=1, tail=len-16) = LE2BLOCK_BYTELIST. (Need the whole-2-block case
val len = 32 to also reduce to the generic form: nfull=2,tail=... OR nfull=1,tail=16 — pick the
encoding `aes_ctr_full_tail_bytes` uses so 32 bytes = the all-full case; check whether the
spec wants tail in 1..16 with nfull counting only strictly-full blocks. Mila uses
val len = 16*nfull + tail with 1<=tail<=16, so 32 bytes => nfull=1, tail=16. Confirm our
LE2BLOCK at bl1=16 equals the whole-2-block proof's output, so the single theorem's tail=16
case is the whole-block proof, and tail<16 is LE2BLOCK. That means the whole-2-block proof
becomes the bl1=16 instance — verify the masked store at bl1=16 (MK=all-ones) reduces to the
plain block store, i.e. LE2BLOCK at bl1=16 SUBSUMES the whole-block proof.)

### DECISION (CONFIRMED 2026-06-24): option (a) — match Mila exactly
LE2BLOCK covers `1 <= bl1 <= 16` INCLUDING bl1=16 (mask = all-ones, the masked store reduces
to the plain block store). The single ≤2-block theorem dispatches `len <= 16 -> LE1BLOCK`,
`16 < len <= 32 -> LE2BLOCK`. The just-finished whole-2-block proof
(`AESV8_GCM_8X_DEC_256_2BLOCK`) is the bl1=16 instance of LE2BLOCK; it is kept as an internal
convenience / building block but is NOT a separate arm of the public dispatch. Verify LE2BLOCK
at bl1=16 (MK = all-ones, `word_and x allones = x`, `word_and y (word_not allones) = 0`,
`word_or x 0 = x`) reduces to the whole-block output — that is the subsumption check.

--- (original options, for the record) ---
Mila encodes `val len = 16*nfull + tail, 1<=tail<=16`, so a full 32-byte input is
`nfull=1, tail=16` — i.e. her LE2BLOCK (masked, with mask=all-ones) already covers the
whole-block case, and there is no separate "whole 2-block" theorem in her dispatch. If we
follow that, our just-finished whole-2-block proof becomes redundant for the public API
(it's the bl1=16 instance of LE2BLOCK). Options:
  (a) Make LE2BLOCK cover 1<=bl1<=16 (incl. 16 = all-ones mask) and have the single ≤2-block
      theorem dispatch len<=16 -> LE1BLOCK, 16<len<=32 -> LE2BLOCK. Whole-2-block proof kept
      only as an internal/whole-block convenience (or retired).
  (b) Keep whole-2-block separate and only add LE2BLOCK for strictly-partial 17..31 bytes.
Recommend (a) to match Mila exactly and avoid a redundant public theorem; confirm with user.

## Acceptance
- `AESV8_GCM_8X_DEC_256_LE2BLOCK` + `_BYTELIST` proved, loadt clean, axioms()=3, no cheats.
- Single ≤2-block dispatch theorem with generic `byte_list_at` (+ proven masked tail).
- Reuses GMULT2 bridge, BYTE_LIST_AT_NBLOCK_CTR, MASK_LEMMA, dec LE1BLOCK machinery — no new
  infrastructure beyond the per-step dec dataflow port from enc le2block.ml.

## Key references
- `arm/proofs/aesv8_gcm_8x_enc_256_le2block.ml` — THE mirror to port (enc 17-31 byte band).
- `arm/proofs/aesv8_gcm_8x_dec_256_1block.ml` L2306-2680 — dec LE1BLOCK + MASK_LEMMA/BLEND_OR_XOR.
- `arm/proofs/aesv8_gcm_8x_dec_256_2block.ml` — whole-2-block + DEC_2BLK_GMULT2_BRIDGE_TAC.
- `arm/proofs/utils/aes_ctr_spec.ml` L354-440 — aes_ctr_full_tail_bytes + BYTE_LIST_AT_NBLOCK_CTR.
- Mila `manastasova:aes256_gcm_tail` @178285cb: aes256_gcm.ml AES256_GCM_ENCRYPT_CORRECT (L8813)
  = the single dispatch theorem; OUT_BRIDGE_GEN (L6877); _CONCRETE/_ABS layering.
- memory: [[project_enc_le2block_17_31_done]], [[project_dec_byte_aligned_le1block]],
  [[project_dec_2block_done]].
