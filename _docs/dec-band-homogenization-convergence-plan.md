# AES-256-GCM decrypt band homogenization & Mila-convergence plan

Status: **STEPS A–C + le8 optimization EXECUTED** (2026-07-03, same day as plan).
- STEP A (b3b9499e): FOLD_MID_HPOW machinery promoted to le3block; le4–le7's
  fragile whole-term-keyed folds replaced by uniform `FOLD_MID_HPOW "Hk"`.
- le8 Q18-only stores (1f9bb255): `ARM_STEPS_FOLD_KEEPQ18_TAC` over 271–374;
  le8 loadt 853s -> 687s (~20%).
- STEP B (b51229e4): all five bridge closers = one-line instantiations of
  `DEC_BRIDGE_CLOSE_TAC nblk sN gmult_ba spec_bf extra_fix` (in le3block);
  `dec_bridge_specl` verified concl-equal to the hand SPECL at N=8.
- STEP C (7e24ce48 + 055c8ac8): `DEC_FRONT_TAC ushr x5 disc disc2 inoff nks`
  hosted in le2block; ALL more_than_k bands le2..le8 use it (le1 has no full
  blocks / never enters more_than_k, so keeps its own front by design).
  Cascade rungs stay per-band (structurally length-dependent).
Every commit chain-verified: hyps=0, axioms()=3, no cheats, no slowdown.
STEP D (3-layer dispatch + Mila D2/D4 spec convergence) remains OPEN — it
requires coordinating file layout/spec vocabulary with Mila's branch.

Original plan follows.  All seven decrypt bands `le2block`..`le8block`
(17–128 B, nfull=1..7) are PROVED + loadt-clean (axioms()=3, hyps=0, no cheats).
This doc records how to homogenize them into ONE recognizable pattern that is *not
slower*, and how that pattern aligns with Mila's live encrypt branch
`mila/aes256_gcm_tail` (tip `14154e49`, 2026-06-30, "Clean and unify closers").

Do NOT churn the proven files without budget: each band re-verifies in ~250–850s
(le8 is the slowest). Re-verify every band you touch and confirm axioms()=3.

---

## 1. Current structure (what we have)

Two-layer per band (file `arm/proofs/aesv8_gcm_8x_dec_256_leNblock.ml`):
- **LAYER 1 `..._LENBLOCK_BODY`** — literal per-block ensures triple, proved by
  `full_leN_tac_front THEN full_leN_tac_stores THEN full_leN_tac_tail THEN full_leN_tac_bridge`.
- **LAYER 2 `..._LENBLOCK`** — readable `byte_list_at` wrapper over the recursive
  whole-buffer spec (`gcm_dec_pt_bytes`/`gcm_dec_final_xi`), proved sim-free from BODY
  via `BYTE_LIST_AT_NBLOCKS` (input) + `BYTE_LIST_AT_NBLOCK_CTR` + `AES_CTR_N_EL` (output).

Shared infra (already homogenized — defined ONCE, reused via `needs`):
- `arm/proofs/utils/aes_gcm_dec_spec.ml` — recursive spec + `GCM_DEC_*_1..8` unfolds.
- `common/gmult_nblock_lemmas.ml` — `build_GMULTn_fast` (GMULTn bridge lemma, ~0.3s).
- `common/ghash_nblock_karatsuba.ml` — Mila's GHASH N-block karatsuba layer.
- `aesv8_gcm_8x_dec_256_le3block.ml` defines the shared bridge machinery reused by
  le4..le8: `WA_UNIFY_TAC`, `WV_UNIFY_TAC`, `ABBREV_WAWV_TAC`, `QQ0SPLIT`, `JOIN_EQ_SPLIT`,
  `SJ_COLLAPSE`/`SJ_COLLAPSE2`, `bubble_fix`, `LANE_FINISH_TAC`, `ABBREV_INNER_PMULS_TAC`,
  `MERGE_2BLK_TAC`, `PMUL_CONG_128`, `RF8_SUBWORD`, `JOINMID`, etc.

What is NOT homogenized (each band redefines its own, with hardcoded step numbers):
- `full_leN_tac_front / _stores / _tail / _bridge`
- `bridge_hash2..6` + `FOLD_MID_TACN` (le4..le7) vs `pmul_mult_hpow`+`FOLD_MID_HPOW` (le8)
- `BRIDGE_CLOSE_TAC_N`, `keys15`, per-band cascade resolvers.

### Per-band step-number table (measured 2026-07-03)

| band | nfull | bytes  | front end | stores window            | tail steps                      | bridge SUBGOAL | post-bridge |
|------|-------|--------|-----------|--------------------------|---------------------------------|----------------|-------------|
| le2  | 1     | 17-31  | s269/270  | 271–297 (cascade rungs)  | …–369                           | **s370**       | 371–372     |
| le3  | 2     | 33-47  | s269/270  | 271–…–373                | 374–380                         | **s381**       | 382–383     |
| le4  | 3     | 49-64  | s269/270  | 291–…–385                | 386–…                           | **s392**        | 393–394    |
| le5  | 4     | 65-80  | s269/270  | 291–…–393                | 394–…                           | **s400**       | 401–402     |
| le6  | 5     | 81-96  | s269/270  | 291–360                  | 361–401                         | **s408**       | 409–410     |
| le7  | 6     | 97-112 | s269/270  | 291–376                  | 377–417 (masked store s417)     | **s422**       | 423–424     |
| le8  | 7     | 113-128| s270      | 271–374 (KEEPGH)+375–392 | 393–414 (KEEPGH; midacc)        | **s414**       | 415–416     |

Note the bridge state advances ~+8 per extra full block (s370,381,392,400,408,422) —
**except le8 = s414**, because le8's bridge is taken PRE the final `ext v19,#8` half-swap
(pc+4568), not post-eor+8. This off-by-one (`ext` at pc+4568, not the eor) was the
multi-session le8 blocker. Every band's bridge = `read Q19 s<K> = ghash_polyval_acc
(byteswap128 h)(word_bytereverse xi)[brev cph0;…;brev cph(nfull-1); brev cphm]`.

---

## 2. Mila's recognizable pattern (mila/aes256_gcm_tail — the convergence target)

She proves ENCRYPT (`AES256_GCM_ENCRYPT_CORRECT`, val len ≤ 128) in a 3-layer XTS style:
- **dispatch** — nested `ASM_CASES_TAC` on `val len` at 16,32,…,112 → `..._LT_{0..8}BLOCK_ABS`.
- **abstract band `..._ABS`** — conclusion in spec vocab; uniform 8-block-sized precond.
- **concrete band `..._CONCRETE`** — ARM_STEPS sim; GHASH closed by the karatsuba layer.

Recent "Clean and unify closers" work: one file per size
`arm/proofs/utils/gcm_{one..eight}_block_closers.ml`, each with the SAME recognizable
skeleton:
- `ghash_Nblock_karatsuba` (new_definition), `GHASH_NBLOCK_AS_NBLOCK`,
  `GHASH_NBLOCK_KARATSUBA_EQ_POLYVAL_ACC`,
- **parameterized shared tactic generators**: `GCM_NBLOCK_CT{k}_STEP_TAC = GCM_NBLOCK_CT_STEP_TAC N k`
  (the per-N specialization is a one-liner instantiation, not a hand-inlined tactic),
- `NBLOCK_USHR`, `NBLOCK_MASK_REG`, etc.
Her hard bridge `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` is proven ONCE and instantiated per N.

Key divergences (decrypt-vs-encrypt aside): D2 `aes256_block_enc` vs our XTS `aes256_encrypt`;
D4 `word_reversefields 8` vs `word_bytereverse` (equal via `WORD_BYTEREVERSE_REVERSEFIELDS`);
D5 htable key packaging; prologue reorder (ours enters pc+0x18, hers pc). See
`_docs/gcm-spec-divergence-from-mila-handback.md`.

---

## 3. Homogenization steps (safe, incremental, not slower)

Do these in order; re-verify (cold-load or `loadt` with chain preloaded) after each,
confirm axioms()=3 / hyps=0. Each is independently committable.

### STEP A — promote the multiplier-keyed FOLD_MID to shared (correctness + uniformity)
The le8 `FOLD_MID_HPOW` keys on the pmul's MULTIPLIER (2nd arg = h-power), which is
robust; le4..le7's `bridge_hashN` keys on `find_term hN` over the WHOLE pmul, which is
fragile (the whole-8 karatsuba INPUT carries lower h-powers — this is exactly why le8
needed the rewrite). Move `pmul_mult_hpow` + `is_pmul128_tm` + `FOLD_MID_HPOW` +
`LE8_K13_FIX` + `QQ39_FIX_TAC` into `le3block.ml` (next to WA_UNIFY_TAC). Then each band's
`BRIDGE_CLOSE_TAC_N` folds mids with `FOLD_MID_HPOW "H6"`…`"H2"` uniformly. Re-verify le4..le8.
Expected: same speed (the fold work is identical), cleaner + one recognizable mechanism.
NOTE: only le8 needs `QQ39_FIX_TAC` (the k13 ins-carry is unique to the whole-8 main loop);
smaller bands can call it as a no-op-if-absent (guard `try … with _ -> ALL_TAC`).

### STEP B — unify the bridge close into ONE parameterized tactic
Extract `BRIDGE_CLOSE_TAC_N` into a single `DEC_BRIDGE_CLOSE_TAC nfull sN` in le3block that:
  builds the (2*nfull+2)-arg GMULT{nfull+1} SPECL from `build_GMULTn_fast` output,
  spec_eq via `spec_to_byteform_{nfull+1}`, prefix rewrites, ABBREV_INNER_PMULS, MERGE_2BLK,
  FOLD_MID_HPOW over the present h-powers, WA_UNIFY, (le8: QQ39_FIX), WV_UNIFY, ABBREV_WAWV,
  QQ0SPLIT/JOIN_EQ_SPLIT/LANE_FINISH. Per-band call = `DEC_BRIDGE_CLOSE_TAC 7 414`.
This mirrors Mila's `GCM_NBLOCK_CT_STEP_TAC N k` recognizable-generator style.

### STEP C — unify the front (nfull-independent) into a shared generator
The front (states 1–270) is IDENTICAL across bands except the length lemma
(`USHR_*_8BL_LEMMA`, `X5_ZERO_LEMMA{N}`) and the cascade resolver. Extract
`DEC_FRONT_TAC nfull` taking the band's length/cascade lemmas. The stores/tail differ by
step windows (table §1) so keep per-band but drive from a `(nfull -> windows)` table.

### STEP D (optional, larger) — adopt Mila's 3-layer dispatch for decrypt
Add a top `AES256_GCM_DECRYPT_*` dispatch (ASM_CASES on val len) routing to the le2..le8
bands + le1block, matching her encrypt `AES256_GCM_ENCRYPT_CORRECT`. This is the natural
place to also converge D2/D4 (use her `aes256_block_enc` / `word_reversefields 8`) so the
decrypt spec reads identically to hers. Coordinate file placement (shared `common/`/`utils/`).

---

## 4. le8-specific optimization (the "not slower" concern)

le8 is the slowest band (~851s loadt) because `full_le8_tac_stores` uses
`ARM_STEPS_FOLD_KEEPGH_TAC` over 271–392, keeping ALL of Q16/Q17/Q18/Q19 live across
~120 states (hyp pile → 546). But the midacc-capture only needs **Q18** live to s374.
OPTIMIZATION: a `KEEP_Q18_ONLY` stepper (discard Q16/Q17/Q19 per-step, keep only Q18)
for 271–374 should cut the stores time materially with no correctness change (verified
need: only `read Q18 s374` is abbreviated as `midacc`; Q16/17/19 at s392 are re-derived
by the tail's own reads). Test: after the Q18-only stores, confirm `read Q18 s374` is
present + closed (size ~19612) and the rest of the proof is unchanged. Re-verify le8.
This is the single highest-value "not slower" change and keeps le8 in line with the
per-step-discard philosophy of [[project_dec_band_stepping_optimization]].

---

## 5. Sequencing recommendation

1. STEP A (promote FOLD_MID_HPOW) — smallest, highest correctness value, re-verify le4..le8.
2. le8 Q18-only stores optimization (§4) — re-verify le8, confirm faster.
3. STEP B (unified DEC_BRIDGE_CLOSE_TAC) — re-verify all bands.
4. STEP C (DEC_FRONT_TAC) — re-verify all bands.
5. STEP D (dispatch + Mila spec convergence) — the big one; coordinate with Mila's file layout.

After STEP D the decrypt side mirrors `mila/aes256_gcm_tail`'s encrypt structure closely
enough that a reviewer sees ONE recognizable pattern for both directions and all sizes.
