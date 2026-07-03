# AES-GCM decrypt LE5BLOCK (nfull=4, 65–80 bytes) — plan

**Goal:** `AESV8_GCM_8X_DEC_256_LE5BLOCK_BODY` (literal per-block triple, ARM-sim target)
+ `AESV8_GCM_8X_DEC_256_LE5BLOCK` (readable byte_list_at in/out) in
`arm/proofs/aesv8_gcm_8x_dec_256_le5block.ml`. bit_len = 512 + 8*bl1, 1<=bl1<=16.
FOUR full ciphertext blocks 0..3 (GHASH vs H^5,H^4,H^3,H^2) + one MASKED partial block 4
(less_than_1, vs H). nfull=4. Mirror of le4block with one extra full middle block +
5-term GHASH bridge. bl1=16 endpoint = whole-5-block (80 byte) case.

## Binary control flow (objdump aesv8_gcm_8x_dec_256.o)
Cascade ladder (x5 = byte length = 64+bl1 for this band):
- 0xec0 cmp x5,#0x70(112) b.gt 0xf98   — fall (64+bl1 <= 80 < 112+1... always fall for bl1<=16→ x5<=80)
- 0xf04 cmp #0x60(96)  b.gt 0xfc8      — fall
- 0xf1c cmp #0x50(80)  b.gt 0x1000     — BOUNDARY: taken only if x5>80 i.e. never (bl1<=16 → x5<=80); at bl1=16 x5=80 NOT >80 → fall. (bl5_resolve_pc_bdy at #80)
- 0xf30 cmp #0x40(64)  b.gt 0x103c     — TAKEN (x5=64+bl1 > 64 for bl1>=1) → more_than_4 = 0x103c = pc+4156
- (#48/#32/#16 not reached)

`more_than_N` entry PCs: more_than_4=0x103c, more_than_3=0x1074, more_than_2=0x10b8,
more_than_1=0x10f4, less_than_1=0x1138. Each more_than_k does one GHASH round
(rev64 v8,v9=cph; eor v8,v16; pmull/pmull2/mid vs the k-th H-power lane; accumulate
v17/v18/v19; ldr next cph; eor3 v12 = plaintext; st1 v12 store). less_than_1 (0x1138)
does the masked tail round + reduction + rev64 + st1 xi_p.

H-power htable lanes used in more_than_4 (0x103c..): v20/v21 = htbl+96 (H^4 + its key),
then v24/v25=htbl+160, v22/v23=htbl+128, ... (walk backwards H^5..H). For le5 the
FIRST full block (block 0) multiplies by H^5. Need htable slots up to htbl+? for H^5.
Verify exact htable offsets & the h5/h5k reads in the front (mirror le4's htbl_p reads:
le4 read h..h4 at htbl+0..80; le5 needs h5 at htbl+96 and h5k at htbl+112). CONFIRM by
objdump of the CTR/htable-load bulk and by the pmull lane regs in more_than_4.

## Prerequisites to build
1. **GHASH_POLYVAL_ACC_5** (common/ghash_nblock_karatsuba.ml) — 5-block Horner unroll,
   derived from GHASH_POLYVAL_ACC_BATCHED for list [p;q;r;s;t] exactly like ACC_4:
   ```
   ghash_polyval_acc h a [p;q;r;s;t] =
     polyval_reduce_prop3 (word_xor (word_pmul (word_xor a p) H^5)
       (word_xor (word_pmul q H^4) (word_xor (word_pmul r H^3)
        (word_xor (word_pmul s H^2) (word_pmul t H)))))
   ```
   proof = MP GHASH_POLYVAL_ACC_BATCHED [q;r;s;t] a p; REWRITE h_power/ghash_wide/num_CONV.
2. **GMULT5_FULL_CORRECT_BA** via `build_GMULTn_fast 5` (shared builder, ~0.3s).
3. **spec_to_byteform_5** — the H-power byteswap relations (h2..h5 = polyval_dot chain),
   analogue of le4's spec_to_byteform_4, feeding GHASH_POLYVAL_ACC_5.
4. **AES_CTR_5_EL** + **GCM_CTR_INC4_LANES** — 5th counter lane (ctr+4).
5. **GCM_DEC_GHASH_BLOCKS_5 / GCM_DEC_PT_BYTES_5** — already built in aes_gcm_dec_spec.ml.
6. Input bridge: **BYTE_LIST_AT_5BLOCKS** (exists in aes_xts_common.ml, 80 bytes).
   Output bridge: **BYTE_LIST_AT_NBLOCK_CTR** + AES_CTR_5_EL (nfull=4).

## Proof structure (mirror le4, +1 full block)
- **PART 1 cascade helpers**: bound 64+bl1<=80, x5=word(64+bl1). USHR_512_8BL_LEMMA,
  X5_ZERO_LEMMA5, X1_MOD128_BRIDGE5 (512 = 8*bl1 + 4*128 → MOD_MULT_ADD). resolvers
  bl5_resolve_pc (fall #112/#96), bl5_resolve_pc_bdy (#80 boundary, taken never / at
  bl1=16 fall), bl5_resolve_pc64_taken (#64 → more_than_4 pc+4156).
- **FRONT** (mirror le4 front): prologue+CTR/AES bulk; keep Q3 fix? For 5 blocks the
  opaque-keystream shift lands v4=ctr+4 for the masked block. KEYSTREAM: keep the blocks
  that survive the shift-register movs for the 4 full + 1 masked = need v0..v4 as ctr+0..4.
  ABBREV 5 keystreams. Cascade with plain ARM_STEPS to more_than_4 entry.
- **STORES**: 4 full plaintext stores pt0..pt3.
- **MASKED TAIL**: pt4 capture, mask-collapse Q9→cphm BEFORE rev64, masked-blend store
  out_p+64, to bridge state.
- **5-TERM BRIDGE** (BRIDGE_CLOSE_TAC_5): mirror BRIDGE_CLOSE_TAC_4 with THREE explicit
  FOLD_MID_TAC middles (cph1·H^4→qq?, cph2·H^3, cph3·H^2); masked mid auto-folds.
- **POST-BRIDGE**: rev64 + st1 xi_p; ENSURES_FINAL_STATE; MONOTONE_MAYCHANGE. Exit PC =
  le4 exit + (one extra GHASH-round span). DISCOVER empirically.

## Step→PC discovery
The exact ARM step indices for the 5-block path must be found by stepping (le4's front
is ~303 steps to more_than_3; le5 to more_than_4 is one cascade rung EARLIER in the b.gt
ladder but ONE MORE full-block GHASH round in the body). Use the le4 tactics as template;
adjust step ranges + the bridge state s(N). Bridge off-by-one discipline: take AFTER the
shared `eor v19,v19,v18`.

## Acceptance
hyps=0, axioms()=3, no cheats, cold-load-clean (load 1block first, then le5block).
Add `needs "arm/proofs/aesv8_gcm_8x_dec_256_le4block.ml"` at top (reuses le4's infra).
