# Extending the AES-GCM proof to 2 blocks: approaches and whether Mila's parameterised proof scales better

**Date:** 2026-06-03
**Author context:** follow-up to the completed 1-block proof
(`arm/proofs/aesv8_gcm_8x_enc_256_1block.ml`, theorem `AESV8_GCM_8X_ENC_256_1BLOCK`).

This doc answers two questions:
1. How can the current 1-block proof be extended to 2 blocks?
2. Does Mila's parameterised two-block proof (last commit on her
   `one_block_very_messy_v1` branch) scale better for that?

It is grounded in reading both proof developments in full (see §1 sources). Every
structural claim about Mila's files was read from the extracted sources, and the key
HOL facts (`byteswap128`, `GHASH_POLYVAL_ACC_2` shape, the recombine/reduction lemma
statements) were checked.

---

## 0. TL;DR / recommendation

- **The two developments prove different functions.** This proof targets the **real
  shipped binary** `aesv8_gcm_8x_enc_256` (1505 instrs, the aws-lc unroll-by-8 kernel),
  taking its 1-block path through the actual branch cascade. Mila's 2-block proof targets
  a **hand-edited extraction** `two_blocks_aes256_gcm_preloop_tail.S` in which the entire
  8-way `Loop_mod2x_v8`/`prepretail`/`main_loop` machinery is **commented out**; its
  "2-block" GHASH is the single-block `less_than_1` path invoked so the tail handles two
  blocks via the cascade — NOT the binary's genuine 2-block (`Loop_mod2x_v8`) code.
- **Mila's closure infrastructure scales better; her *target* does not match ours.**
  Her GHASH closure is deliberately N-agnostic (one Horner-unroll lemma `GHASH_POLYVAL_ACC_2`
  + block-count-independent recombine/reduction bridge lemmas + a fixed
  abbreviate→sort→halve→blast chain). That is genuinely reusable and is the right model to
  adopt. But it was exercised against straight-line extracted code, so it sidesteps the two
  things that actually make the *real* binary hard at 2+ blocks: the **`trn1/trn2` Karatsuba-mid
  packing** and the **aggregate-then-reduce-once** scheduling of `Loop_mod2x_v8`.
- **Recommended path:** adopt Mila's *spec layer and closure strategy*
  (`GHASH_POLYVAL_ACC_2`/`_N`, `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS`,
  `BARRETT_REDUCTION_EQ_PROP3_REDUCTION`, the abbrev/sort/halve chain), but apply it to the
  **real binary's 2-block path** (`Loop_mod2x_v8`), proving two new local facts: a `trn1/trn2`
  = Karatsuba-mid lemma, and that the assembly's aggregated `(acc⊕b0)·H² ⊕ b1·H` before a
  single reduction equals `GHASH_POLYVAL_ACC_2`'s RHS. This combines our binary-faithfulness
  with her scalable closure. Estimated effort below (§7).

---

## 1. Sources (read in full for this analysis)

From `mila` remote = `https://github.com/manastasova/s2n-bignum-dev`, branch
`one_block_very_messy_v1`, commit `8bc5c9e141f75007034d50fc9db70d30cb3b6b13` (the last
commit; the parameterised 2/3-block work is added there):
- `arm/proofs/two_blocks_aes256_gcm_preloop_tail_direct.ml` (756 lines) — **complete,
  no-cheat** 2-block functional-correctness proof (verified: no CHEAT_TAC/new_axiom/mk_thm).
- `arm/proofs/two_blocks_aes256_gcm_preloop_tail_claude_4.7.ml` (923 lines) — alt variant.
- `arm/proofs/one_block_aes256_gcm_preloop_tail_direct.ml` (752 lines) — the 1-block direct
  proof whose helper lemmas/tactics the 2-block proof reuses verbatim.
- `arm/proofs/two_block_aes256_gcm_preloop_tail_plan.md` (347 lines) — Mila's plan, including
  the explicit `GHASH_CLOSE_N_TAC` parameterisation design.
- `common/ghash_spec.ml` (1276) — `GHASH_POLYVAL_ACC_2`, `polyval_dot`,
  `polyval_reduce_prop3`, `karatsuba_mid`, `ghash_polyval_acc`.
- `arm/proofs/utils/gcm_gmult_v8_nist.ml` (1989) — the NIST↔polyval bridge plus the
  closure bridge lemmas `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS`,
  `BARRETT_REDUCTION_EQ_PROP3_REDUCTION`, `PMUL_KARATSUBA`, `KARATSUBA_LIMBS`, `PMUL_W_64_128`.
- `arm/aes-gcm/two_blocks_aes256_gcm_preloop_tail.S` (1560, mostly commented-out unroll8).

Extracted to `_tmp/mila2blk/` for reading.

---

## 2. The real binary's block-count paths (what we'd actually be extending)

`aesv8_gcm_8x_enc_256` dispatches on `bit_len` (x1) through a cascade
(`.L256_enc_blocks_less_than_N`, N=1..7) plus the 8-block `main_loop`/`prepretail`. The GHASH
math differs by path:

| Path | Blocks | GHASH structure in the binary |
|------|--------|-------------------------------|
| `less_than_1` (our 1-block proof) | 1 | one Karatsuba multiply `(acc⊕ct)·H̄`, then one Prop3 reduction |
| `Loop_mod2x_v8` | 2 | **`trn1/trn2`-packed** Karatsuba-mid for the pair; `(acc⊕b0)·H̄² ⊕ b1·H̄` accumulated into hi/mid/lo, **one** Prop3 reduction |
| `ghash_v8_4x`-style | 4 | 4 independent pmul chains, single reduction |
| `main_loop`/`prepretail` | 8 | 8-way aggregation with `trn1/trn2`, single reduction, AES interleaved |

Key point for scaling: the binary does **aggregate-then-reduce** — for N blocks it XORs N
Karatsuba products into (hi,mid,lo) and reduces **once**. The reduction cost is constant in N;
only the multiply/accumulate grows. This is exactly the shape `GHASH_POLYVAL_ACC_2` (and a
general `GHASH_POLYVAL_ACC_N`) is built to bridge.

---

## 3. What our 1-block proof established (and how it closes GHASH)

- Targets the real binary, 1-block path, 352 simulated steps with the branch cascade.
- GHASH key insight: htable stores H lanes-exchanged, so the algebra key is `byteswap128 h`.
- Closure: assert `read Q19 s348 = polyval_dot (word_xor (brev xi)(brev ct)) (byteswap128 h)`,
  proved by `GMULT_FULL_CORRECT_BA` (one Karatsuba multiply + Prop3 = `polyval_dot`) +
  bespoke `ABBREV_INNER_PMULS_TAC`/`MERGE_PMUL_ATOMS_TAC` + `WORD_BLAST`.
- **`GMULT_FULL_CORRECT_BA` is single-multiply.** It bridges *one* `polyval_dot a b`. It does
  NOT directly express the multi-block aggregate. So our 1-block closure does not, as-is,
  extend to 2 blocks — see §5.

---

## 4. How Mila's 2-block closure works (and why it parameterises)

Her closure (`two_blocks_..._direct.ml` lines 496–587) is, in order:
1. `REWRITE_TAC[GHASH_POLYVAL_ACC_2]` — unroll the **2-element Horner list** into a single
   `polyval_reduce_prop3 (word_xor (word_pmul (a⊕b) (polyval_dot h h)) (word_pmul c h))`.
   This is the only block-count-specific lemma; it generalises to `GHASH_POLYVAL_ACC_N`
   (provable by induction from `GHASH_POLYVAL_ACC_2` + an append lemma + polyval linearity).
2. Fold `xi⊕ct1` and `ct2` (AES-spec rewrites) — N copies, mechanical.
3. `polyval_reduce_prop3` + `PMUL_KARATSUBA` on **both** pmuls → `KARATSUBA_LIMBS` →
   `PMUL_W_64_128`.
4. `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` — **block-count-agnostic** (quantified over abstract
   limbs `xl,xh,xm`). Recombines Karatsuba mid into Prop3 limb form.
5. Substitute the two `karatsuba_mid` htable hypotheses (one for `h`, one for `h²`).
6. `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` — **block-count-agnostic** (quantified over abstract
   `a,b,c,d`). The single final two-phase reduction.
7. `ABBREV_ALL_PMUL_TAC` → `PMUL_ARG_SORT_CONV` → `ABBREV_ALL_PMUL_TAC` →
   `ABBREV_PMUL_HALVES_TAC` → `WORD_BLAST`.

The genuinely scalable part is steps 4, 6, 7: the recombine and reduction bridge lemmas are
stated over abstract 64-bit limbs and are **independent of N** (because the binary reduces once
regardless of N), and the abbrev/sort/halve/blast chain just gets longer (≈3N pmuls, ≈6N
half-names) without changing shape. Mila's plan (§"GHASH_CLOSE_N_TAC") makes this explicit:
the only N-parameterised tactic is `REDUCTION_ROUND_TAC` repeated `n` times, and even that is a
fixed template.

**This closure architecture is strictly more reusable than ours.** Ours bridges one multiply
via `GMULT_FULL_CORRECT_BA`; hers bridges the *reduction* generically and unrolls the Horner
list with one lemma per arity. For N≥2 her design is the right one.

---

## 5. But: the two proofs target different code (the decisive caveat)

Reading `two_blocks_aes256_gcm_preloop_tail.S` shows its 2-block GHASH does **not** use the
binary's `Loop_mod2x_v8`. The entire mod2x/prepretail/main_loop body is commented out
(hundreds of `// pmull ... // trn1 ... // eor3 ...` lines); the function reaches a 2-block
result by the `less_than_1` single-block path under a hand-modified dispatch. Concretely:

- **Mila's 2-block multiply** is expressed as `pmul(a⊕b, H²) ⊕ pmul(c, H)` with the
  Karatsuba-mid taken from **htable hi/lo lanes** (`karatsuba_mid h`, `karatsuba_mid h²`) —
  i.e. precomputed mids loaded from memory, exactly matching `GHASH_POLYVAL_ACC_2`.
- **The real binary's 2-block path (`Loop_mod2x_v8`)** computes the Karatsuba mid *on the fly*
  with `trn1/trn2` packing two blocks' lanes, and schedules the two products' hi/mid/lo
  accumulation interleaved before one reduction. The `trn1/trn2` mid is NOT the htable-loaded
  `karatsuba_mid`; it is `subword(block_i)⊕subword(block_j)` assembled by the transpose
  instructions.

So Mila's closure would transfer, but the **simulation half** (getting `read Q19 = <byte form>`
at the pre-reduction state) differs substantially: the real binary's `trn1/trn2` + interleaved
schedule produces a different symbolic term than the straight-line `less_than_1`-twice code she
simulated. Bridging that needs a `trn1/trn2`-mid lemma and an "aggregate matches
`GHASH_POLYVAL_ACC_2` RHS" step that her proof never had to do.

(Our `htable-byteswap-analysis.md` and `aes-gcm-ghash-aarch64-reference.md` already document
the `trn1/trn2` packing and why the unroll8 uses it — see §4.3 / §7 there.)

---

## 6. Two concrete options for our 2-block extension

### Option A — extend the real-binary proof, borrowing Mila's closure
Stay faithful to `aesv8_gcm_8x_enc_256`; prove its genuine 2-block path
(`Loop_mod2x_v8`, taken when `bit_len = 256`).

Simulation (the new work):
- Reuse the entire AES/ciphertext front from our 1-block proof (it already steps both CTR
  blocks v0,v1 — only v0 was *used* before). Abbreviate `ct0`, `ct1` as we do `Q9` now.
- Step the `Loop_mod2x_v8` body. New facts needed:
  - **`TRN1_TRN2_MID` lemma:** `trn1/trn2` of two lane-exchanged blocks gives the pair's
    Karatsuba-mid operands. Small `WORD_BLAST`/`BITBLAST` over `word_subword`/`word_join`.
  - The htable now also supplies H̄² and its mid (extend the precondition like Mila's:
    `htable[..] = byteswap128 (polyval_dot h h)`, `subword h2k = karatsuba_mid (polyval_dot h h)`).
- At the pre-reduction state, assert
  `read Q19 = polyval_dot (word_xor (brev xi) (brev ct0)) (byteswap128 (polyval_dot h h))
              XOR-aggregated-with  polyval_dot (brev ct1) (byteswap128 h)` (the aggregate form),
  then reduce once.

Closure (borrow from Mila, don't reinvent ours):
- Replace our bespoke `GMULT_FULL_CORRECT_BA` close with the **`GHASH_POLYVAL_ACC_2`** route:
  port `GHASH_POLYVAL_ACC_2`, `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS`,
  `BARRETT_REDUCTION_EQ_PROP3_REDUCTION`, `ABBREV_ALL_PMUL_TAC`, `PMUL_ARG_SORT_CONV`,
  `ABBREV_PMUL_HALVES_TAC` into our preamble (or `needs` her `gcm_gmult_v8_nist.ml` +
  `ghash_spec.ml` if we adopt that spec stack).
- Spec change: postcondition becomes
  `xi_p = word_bytereverse (ghash_polyval_acc (byteswap128 h) (brev xi) [brev ct0; brev ct1])`
  (note `byteswap128 h` still, per our §6 finding; Mila uses raw `h` because her extraction's
  htable/EXT convention nets the other way — reconcile during porting).

Pros: proves the real shipped code; composes toward the eventual full-loop theorem.
Cons: must do the `trn1/trn2` + aggregate-schedule simulation that nobody has done yet.

### Option B — prove a Mila-style extracted 2-block function
Extract a straight-line 2-block `.S` (like hers) and reuse her proof almost verbatim.

Pros: fastest to a *a* 2-block theorem; her closure transfers directly; ~her stated effort.
Cons: proves a *synthetic* function, not the binary; does NOT advance coverage of
`aesv8_gcm_8x_enc_256`; the `Loop_mod2x_v8`/`trn1`/aggregate gap remains unproven and would
have to be done later anyway for the real loop proof.

**Recommendation: Option A.** The whole point of the 1-block proof was binary faithfulness
("applies to the shipped aws-lc binary; composes with the loop proof"); Option B abandons that.
Adopt Mila's *closure* (clearly superior for N≥2) but keep our *target*.

---

## 7. Does Mila's approach "scale better"? — verdict

**For the GHASH algebraic closure: yes, decisively.** Her design is N-parameterised by
construction (one Horner-unroll lemma per arity, block-count-agnostic recombine/reduction
bridges, a fixed abbrev/sort/halve/blast chain). Our `GMULT_FULL_CORRECT_BA` close is
single-multiply and would need re-engineering for each N; hers would not. For 2/3/4-block we
should switch to her closure model regardless of target.

**For the end-to-end proof of the real binary: only partially.** Her parameterisation was
validated on straight-line extracted code that avoids the binary's `trn1/trn2` packing and
aggregate-then-reduce scheduling. Those are the genuinely new simulation obstacles for the real
2-block (`Loop_mod2x_v8`) and 8-block paths, and her proofs do not touch them. So her work
de-risks the *closure* (the part we found hardest at 1 block) but not the *new simulation* that
2-block-of-the-real-binary introduces.

**Net:** the best 2-block plan is a hybrid — our binary-faithful simulation skeleton + a
`trn1/trn2`-mid lemma + Mila's `GHASH_POLYVAL_ACC_2`-based scalable closure. Effort estimate:
~simulation 3–5 days (the `Loop_mod2x_v8` body + trn lemma + aggregate assertion are the risk),
closure ~1–2 days (mostly porting her lemmas and reconciling the `byteswap128 h` vs raw-`h`
convention). Subsequent N (3,4) then drop to ~2–3 days each once `GHASH_POLYVAL_ACC_N` and a
`GHASH_CLOSE_N_TAC`-style meta-tactic exist — which is exactly Mila's plan, just retargeted at
the real binary.

---

## 8. Open items to settle before starting

1. **Confirm the binary's 2-block path is `Loop_mod2x_v8`** (not a `less_than_2` cascade tail)
   by disassembling `aesv8_gcm_8x_enc_256.o` at `bit_len=256` and tracing the branch. (The
   1-block path is `less_than_1`; the 2-block dispatch needs checking — it may take the mod2x
   loop or a dedicated tail.)
2. **Reconcile the GHASH key convention.** Ours nets `byteswap128 h`; Mila's nets raw `h`
   (different EXT placement in her extraction). For the real binary, re-derive numerically as in
   the 1-block proof (`_docs/ghash-1block-bridge-halfswap-findings-20260603.md`).
3. **Decide spec-stack dependency.** Adopting `GHASH_POLYVAL_ACC_2` means depending on
   `common/ghash_spec.ml` + `gcm_gmult_v8_nist.ml`. Check these are on a path to land on the
   nebeid fork / main (Mila's `gcm_gmult_proof` branch is NOT on origin — see the methodology
   doc §0), or port the specific lemmas into our file's preamble to stay self-contained.
4. **`h²` provenance.** The proof only needs `h² = polyval_dot h h` and `htable mid =
   karatsuba_mid h²` as precondition hypotheses (opaque `h²`), exactly as Mila does — no need to
   unfold `polyval_dot`.
