# Comparison: AES-256-GCM GHASH Proof Approaches

## Proof Index

| # | Name | File | Lines | Assembly | Branch / Commit |
|---|------|------|-------|----------|-----------------|
| 1 | **1blk-dedicated** | `arm/proofs/aesv8_gcm_1block_enc_256.ml` | 380 | 72 instr, linear, no branching/mask/counters — purpose-built standalone | [`mila/one_block_very_messy_v1`](https://github.com/manastasova/s2n-bignum-dev/blob/one_block_very_messy_v1/arm/proofs/aesv8_gcm_1block_enc_256.ml) @ `8bc5c9e1` |
| 2 | **1blk-bridge** | `arm/proofs/one_block_aes256_gcm_preloop_tail.ml` | 780 | 111 instr, linear, mask+BIF but no branch cascade — extracted tail of 8x | Same branch |
| 3 | **1blk-bridge-4.7** | `arm/proofs/one_block_aes256_gcm_preloop_tail_claude_4.7.ml` | 770 | Same as #2 | Same branch |
| 4 | **1blk-direct** | `arm/proofs/one_block_aes256_gcm_preloop_tail_direct.ml` | 752 | Same as #2 | Same branch |
| 5 | **1blk-fullpath** | `arm/proofs/aesv8_gcm_8x_enc_256_1block.ml` | 154 | 352 steps through production `aesv8_gcm_8x_enc_256` — branch cascade, counters, mask, interleaved | [`nebeid/aesv8-gcm-1block-proof`](https://github.com/nebeid/s2n-bignum/tree/aesv8-gcm-1block-proof) @ [`51d3193b`](https://github.com/nebeid/s2n-bignum/commit/51d3193b) |
| 6 | **2blk-direct** | `arm/proofs/two_blocks_aes256_gcm_preloop_tail_direct.ml` | 756 | 160 instr, interleaved AES for 2 counters + batched 2-block GHASH — extracted tail | `mila/one_block_very_messy_v1` |
| 7 | **3blk-bridge** | `arm/proofs/three_blocks_aes256_gcm_preloop_tail_claude_4.7.ml` | 397 | ~220 instr, interleaved AES for 3 counters + batched 3-block GHASH — extracted tail | Same branch |

---

## 1 — 1blk-dedicated: Dedicated 1-block function (380 lines)

**Assembly**: `aesv8_gcm_1block_enc_256.S` — 72 instructions, completely linear. Loads counter from `[x4]`, does 14 AES rounds (ldp+aese+aesmc pairs), final eor3 with plaintext and last round key, stores ciphertext, increments counter, then straight into GHASH (rev64, ext, 3 pmulls, Prop3 reduction with 2 pmulls, rev64, store xi). No branches, no mask computation, no counter register management. Purpose-built for verification — not the production code.

**Spec**: `gcm_gmult_spec` — an instruction-level mirror of the assembly register data flow. The postcondition IS the assembly shape.

**Simulation**: Per-step simplification (`GCM_ENC_SIMPLIFY_TAC` after every step). `ARM_VERBOSE_STEP_TAC` for final 9 steps to preserve Q19.

**Closure**: Pure rewriting — `WORD_INSERT_AS_JOIN`, `KAR_SUBWORD_LEMMA`, `ASM_REWRITE_TAC[]`. No WORD_BLAST for GHASH. NIST equivalence proved separately.

**Tradeoff**: Simplest proof (assembly is purpose-built, spec mirrors it exactly). Requires a separate assembly function and separate NIST equivalence proof.

---

## 2 — 1blk-bridge: Preloop tail with intermediate spec (780 lines)

**Assembly**: `one_block_aes256_gcm_preloop_tail.S` — 111 instructions. Extracted from the tail of the production `aesv8_gcm_8x_enc_256` function. Linear (no branch cascade) but includes the mask computation (MVN/LSL/DUP/BIF) that the production code uses for partial blocks. AES rounds use ldp pairs. GHASH uses the same eor3-based Prop3 reduction as the production code. Includes stack frame setup/teardown (stp/ldp of callee-saved registers).

**Spec**: `ghash_polyval_acc` (mathematical). Introduces `ghash_1block_karatsuba` as intermediate assembly-shaped spec.

**Bridge**: `GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT` (~30 lines). Assembly-shaped spec = `word_reversefields 8 (polyval_dot input h)` under hk precondition.

**Simulation**: Per-step simplification. Intermediate `RULE_ASSUM_TAC` rewrites at steps 93 and 111.

**Closure** (~50 lines): Rewrites with bridge lemma, expands intermediate spec, structural lemmas (`WORD_INSERT_AS_JOIN`, `KAR_SUBWORD_LEMMA`, `HALFSWAP_XOR`, etc.), then `ABBREV_ALL_PMUL_TAC` + `CONV_TAC WORD_BLAST`.

**~20 structural lemmas** required.

---

## 3 — 1blk-bridge-4.7: Claude 4.7 version (770 lines)

Identical to #2 (1blk-bridge) except documents the **step 105 REV64 pathology** (~3.5 min blowup when Q19 holds a large expression). Accepts the slow step rather than break the closure. Removes dead-code lemmas from #2.

---

## 4 — 1blk-direct: Direct version (752 lines)

No intermediate spec. Bridges directly to `polyval_dot` using compositional lemmas: `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS`, `BARRETT_REDUCTION_EQ_PROP3_REDUCTION`, `PMUL_KARATSUBA`.

**Closure** (~150 lines): Manual decomposition — abbreviates pmulls, proves pmul duplicates (`pm2=pm0`, `pm3=pm1`, `pm5=pm4`), abbreviates Barrett reduction patterns `r1`/`r2`, proves intermediate equalities `t=u`, final `CONV_TAC WORD_BLAST`.

Most manual approach. Each piece is small and fast. 150 lines vs 4 in #5 (1blk-fullpath).

---

## 5 — 1blk-fullpath: Full 8x function path (154 lines, 75s)

**Assembly**: The actual production `aesv8_gcm_8x_enc_256` function (4600 bytes total). The 1-block path traverses 352 instructions starting at the function's internal entry point (pc+0x2c): counter setup with REV32+ADD pairs for 8 counters (steps 1-25), 14 AES rounds interleaved with counter increments (26-265), a 6-way B.GT branch cascade comparing remaining length against thresholds 112/96/80/64/48/32/16 (266-310), mask computation via MVN/LSL/DUP/AND/BIF (311-332), ciphertext store (334), and GHASH with eor3-based Prop3 reduction (333-352). This is the unmodified production binary — no extraction or simplification.

**Spec**: `ghash_polyval_acc`/`polyval_dot` directly. No intermediate spec.

**Simulation**: No per-step simplification. `ARM_STEPS_TAC`/`ARM_STEPS_RESOLVE_TAC` for bulk stepping. VSTEPS only for 8 steps around ciphertext store.

**Closure** (4 lines):
```ocaml
REWRITE_TAC[ghash_polyval_acc; polyval_dot; polyval_reduce_prop3; PMUL_KARATSUBA] THEN
CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
ABBREV_ALL_PMUL_TAC THEN
CONV_TAC WORD_BLAST
```

Expands RHS into assembly structural form, abbreviates `word_pmul` terms, WORD_BLAST resolves the 128-bit structural equality.

---

## 6 — 2blk-direct: 2-Block proof (756 lines, COMPLETE)

**Assembly**: `two_blocks_aes256_gcm_preloop_tail.S` — 160 instructions. Extracted tail handling exactly 2 blocks. AES rounds for two counter values (v0 and v1) are interleaved for pipeline efficiency. After both ciphertexts are produced, the batched 2-block GHASH section computes two Karatsuba triples simultaneously — one using h (from Htable[0]) and one using h² (from Htable[2]) — accumulates both 256-bit products via XOR, then performs a single Prop3 reduction. The B.GT dispatch (cmp x5, #16) selects between 1-block and 2-block paths within this function.

**Key insight — batched GHASH**: Assembly computes both Karatsuba triples simultaneously (using h and h²), XORs 256-bit products, ONE reduction. Matches `GHASH_POLYVAL_ACC_2`:
```
ghash_polyval_acc h a [b; c] =
  polyval_reduce_prop3 (word_xor (word_pmul (word_xor a b) (h²)) (word_pmul c h))
```

**Htable**: h, karatsuba_mid(h), h², karatsuba_mid(h²).

**Closure** (~100 lines): `GHASH_POLYVAL_ACC_2` + two Karatsuba triples (6 pmulls) + `ABBREV_ALL_PMUL_TAC` + `CONV_TAC WORD_BLAST`.

---

## 7 — 3blk-bridge: 3-Block proof (397 lines, INCOMPLETE)

**Assembly**: `three_blocks_aes256_gcm_preloop_tail.S` — ~220 instructions. Extracted tail handling exactly 3 blocks. AES for three counter values (v0, v1, v2) interleaved. Batched 3-block GHASH computes three Karatsuba triples using h, h², h³ from the htable, accumulates all three 256-bit products, single Prop3 reduction.

Uses `GHASH_POLYVAL_ACC_3` + `GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC`. Three Karatsuba triples (9 pmulls), summed, one reduction.

**Status**: Bridge lemma PROVEN. Simulation scaffold provided. Closure uses **CHEAT_TAC**.

---

## Summary Table

| Aspect | 1-dedicated | 2-bridge | 3-bridge-4.7 | 4-direct | 5-fullpath | 6-2blk |
|--------|----|----|----|----|----|----|
| Closure lines | ~10 | ~50 | ~50 | ~150 | 4 | ~100 |
| Structural lemmas | 3 | ~20 | ~15 | ~20 | 0 | ~20 |
| Per-step simplify | Yes | Yes | Yes | Yes | No | Yes |
| WORD_BLAST for GHASH | No | Final | Final | Final | Main | Final |
| Intermediate spec | gcm_gmult_spec | ghash_1block_karatsuba | Same | None | None | ghash_2block_karatsuba |
| Bridge lemma | Separate | Yes | Yes | Compositional | Implicit | Yes |
| VSTEPS | No | No | No | No | Yes (8) | No |
| Proof time | Fast | ~4min (REV64) | Same | Similar | 75s | Unknown |
| Assembly | 72 instr | 111 instr | Same | Same | 352 instr | 160 instr |

---

## Clarification: Per-Step Simplification vs Bridge Lemma

Independent techniques solving different problems:

| Technique | Problem it solves | What it does |
|-----------|------------------|--------------|
| Per-step simplification | Expressions grow too large during simulation | Collapses REV64 byte-trees, eliminates double half-swaps, normalizes subwords after each instruction |
| Bridge lemma | Proving final expression equals mathematical spec | Algebraic theorem: "N Karatsuba triples with these inputs = polyval_dot/ghash_polyval_acc" |

In #2/#3/#6: both used together. In #5: neither (WORD_BLAST handles both). In #4: bridge is compositional (multiple small lemmas instead of one).

---

## Performance: Per-Step Simplification vs Alternatives

| Approach | Per-step cost | Total for 20 GHASH steps | Notes |
|----------|--------------|--------------------------|-------|
| ARM_STEPS_RESOLVE_TAC | ~60ms/step | ~1.2s | Fastest, but huge expressions |
| VSTEPS | ~200-500ms/step | ~5-10s | Grows with hypothesis count |
| Per-step simplification | ~50-100ms usually | ~5s + 3.5min on REV64 | Fast usually, catastrophic on REV64 |

The 3.5-minute REV64 pathology is an engineering problem (solvable by abbreviating Q19 before that step), not a fundamental limitation.

---

## Scalability: Multi-Block and Loop Proofs

### The assembly batches GHASH

The tail/cascade at offsets 0x1080-0x11D4 accumulates N Karatsuba triples (one per block, using h, h², ..., h^N) into Q17/Q18/Q19, then does ONE Prop3 reduction. The loop body does the same for 8 blocks per iteration.

This means **per-block assertion (the hybrid approach) won't work** — there are no per-block GHASH boundaries in the assembly. The GHASH for all N blocks is one fused computation.

### What scales

1blk-bridge's architecture (per-step simplification + bridge lemma + `GHASH_POLYVAL_ACC_N`) scales linearly:
- Each N needs `GHASH_POLYVAL_ACC_N` (provable by induction)
- Bridge lemma is structural (same pattern for each N)
- Closure grows linearly (3N pmulls to abbreviate)

1blk-fullpath's WORD_BLAST approach does not scale beyond 1 block.

### Recommended architecture for 2+ blocks

1. `GHASH_POLYVAL_ACC_N` to unroll Horner iteration into batched form
2. Per-step simplification during fused GHASH section
3. Bridge lemma connecting assembly-shaped batched computation to spec
4. `ABBREV_ALL_PMUL_TAC` + `WORD_BLAST` (or manual reduction rounds) for closure

---

## Q&A

### Q: Is the batched GHASH from the loop body or the exit paths?

The batched GHASH is in the **exit paths** (tail/cascade). The cascade processes blocks N, N-1, ..., 2 by accumulating Karatsuba products into Q17/Q18/Q19, then the final section processes block 1 and does the single Prop3 reduction.

1blk-fullpath's 1-block proof skips the earlier accumulation (Q17=Q18=Q19=0 at entry) and only executes the final section. For 2 blocks, one earlier accumulation section also executes.

The loop body also batches — 8 blocks per iteration — same accumulate-then-reduce-once pattern with h, h², ..., h⁸.

### Q: Will we need a bridge lemma for all 8 blocks? How long?

Yes. Need `GHASH_POLYVAL_ACC_8` (8-block Horner unrolling into batched form).

**Bridge lemma**: ~30-50 lines. Same structure as 2-block, more Karatsuba triples. Mechanical proof.

**Closure**: 8 Karatsuba triples = 24 half-size pmulls + 2 reduction pmulls = 26 `word_pmul` terms. Estimated:
- With parameterized `GHASH_CLOSE_N_TAC`: 1 line
- Manual: ~300-400 lines
- If WORD_BLAST can't handle 26 pmulls: manual reduction-round approach (~150 lines, deterministic)

Risk: #6 (2blk-direct) (6 pmulls) works with WORD_BLAST. #7 (3blk-bridge) (9 pmulls) uses CHEAT_TAC — may already be at the limit. If WORD_BLAST fails at 8 blocks, fallback is `REDUCTION_ROUND_TAC` (deterministic, same cost regardless of block count).

---

## Experiment: Does ABBREV_ALL_PMUL_TAC + WORD_BLAST scale beyond 1 block?

### Hypothesis

The comparison doc's scalability concern may be overstated. After `ABBREV_ALL_PMUL_TAC`, WORD_BLAST sees only XOR/join/subword over opaque variables — the depth is fixed (one Prop3 reduction) and adding blocks only adds XOR leaves (linear, not exponential). WORD_BLAST might work for all N up to 8.

### What to test

For each N-block closure, measure:
1. Time for `REWRITE_TAC[...PMUL_KARATSUBA] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV)` — spec expansion
2. Time for `ABBREV_ALL_PMUL_TAC` — how many pmulls, how long to abbreviate
3. Time for `CONV_TAC WORD_BLAST` — the actual bit-blasting
4. Total memory usage

### Concrete steps

1. **2-block test** (cheapest to try): Extract the 2-block tail path, simulate to the GHASH postcondition goal, then run:
   ```ocaml
   REWRITE_TAC[ghash_polyval_acc; GHASH_POLYVAL_ACC_2;
               polyval_dot; polyval_reduce_prop3; PMUL_KARATSUBA] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   ABBREV_ALL_PMUL_TAC THEN
   time (CONV_TAC WORD_BLAST)
   ```
   Measure: does WORD_BLAST finish? In how many seconds?

2. **If 2-block works (<30s)**: Try 3-block with `GHASH_POLYVAL_ACC_3`.

3. **If 3-block works (<60s)**: The approach likely scales to 8. Try 8-block.

### Success criteria

| Result | Conclusion |
|--------|-----------|
| WORD_BLAST finishes in <30s for N blocks | Simple approach works — no bridge lemma needed for N blocks |
| WORD_BLAST finishes but takes >60s | Works but marginal — bridge lemma is an optimization worth considering for CI |
| WORD_BLAST hangs or OOMs | Simple approach doesn't scale to N — bridge lemma + per-step simplification required |
| Spec expansion (`let_CONV`) itself hangs | Need to restructure: expand incrementally or use intermediate assertions |

### What to retract if it works

If WORD_BLAST handles 2+ blocks after abbreviation:
- The "hits a wall at 2+ blocks" claim is wrong
- The "hybrid approach won't work" claim needs revision (it won't work for per-block assertion, but the batched closure with WORD_BLAST does work)
- The recommendation to invest in bridge lemma infrastructure becomes "optional optimization" rather than "required"

### What remains true regardless

- The assembly batches GHASH (no per-block boundaries) — this is a fact about the code
- `GHASH_POLYVAL_ACC_N` is needed to unfold the spec into the batched form — this is required regardless of closure technique
- Per-step simplification keeps simulation fast — still valuable even if WORD_BLAST handles the closure
- Bridge lemma gives deterministic, debuggable closure — still preferable for long-term maintenance
