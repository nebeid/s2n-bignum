# Experiment: does Mila's parameterised closure reduce 1-block proof time (our binary)?

**Date:** 2026-06-03 (updated 2026-06-04). **Status:** COMPLETE. Baseline measured and
decomposed; Mila-route close wired end-to-end into our binary's 1-block proof
(`arm/proofs/aesv8_gcm_8x_enc_256_1block_mila_closure.ml` loads clean on polyval-aes, theorem
binds, no cheats); W-multiply blast eliminated; timing measured. See the 2026-06-04 UPDATE below.

**Question (goal):** test Mila's parameterised GHASH closure on the 1-block path of OUR binary
(`aesv8_gcm_8x_enc_256`) and see whether it reduces proof time vs our committed close.

All work is in the session (new experiment file `_tmp`/scratch only) — the committed proof
(`arm/proofs/aesv8_gcm_8x_enc_256_1block.ml`) is untouched.

**Notation: `word_pmul _ W`** is shorthand used throughout this doc for "a carryless multiply of
some 64-bit limb by the reduction constant W." `word_pmul` is the GF(2)[x] carryless/polynomial
multiply (PMULL semantics: schoolbook multiply with XOR instead of carry); `W =
0xC200000000000000` (decimal `13979173243358019584`) is the GHASH/POLYVAL reduction constant
encoding the field polynomial `x^128 + x^7 + x^2 + x + 1`; `_` is whichever 64-bit accumulator
limb is being reduced. Bit-blasting a carryless multiply by this non-trivial constant is
intractable (the ~107s bottleneck). `PMUL_W_64_128` rewrites it to a closed shift triple
`word_pmul x W = (x << 63) ⊕ (x << 62) ⊕ (x << 57)` (the exponents 63/62/57 are W's set-bit
positions), removing the expensive multiply before any blast.

> **Reader shortcut.** The sections from "Setup" through "What was NOT completed" are the
> chronological *experiment* (baseline measurement + a projection that was partly superseded).
> If you only want the final, shipped form of the proof and its close, skip straight to
> **"FOLLOW-UP (2026-06-04)"** and its **UPDATE** below — that section is self-contained.

## Setup
- Clean polyval-aes checkpoint; loaded our committed preamble (EXEC + all our lemmas), ~41s.
- Simulated our binary's 1-block path to s348 (~116s for the cascade+store+GHASH-multiply
  block; ~20s for the AES front). Captured the real `read Q19 s348` term (20267 chars) and
  abstracted ct→cc to form the isolated bridge goal
  `<Q19@s348 form> = polyval_dot (word_xor (brev xi)(brev cc)) (byteswap128 h)`  (frees xi,cc,h).

## Baseline: our committed close, decomposed (measured)
Closing the isolated bridge goal with our committed tactic
(GMULT GSYM → normalize → ABBREV_INNER_PMULS → MERGE_PMUL_ATOMS → clean → ABBREV_WA → FINISH_WV):

| Phase | Time |
|-------|------|
| GMULT_FULL_CORRECT_BA GSYM rewrite | ~0.0s |
| normalize (byteswap128/subword/join rewrites) | ~0.1s |
| ABBREV_INNER_PMULS + **MERGE_PMUL_ATOMS** (operand-equality WORD_BLASTs) | **~27.5s** |
| **FINISH_WV** (final monolithic structural WORD_BLAST) | **~107s** |
| **Total s348 bridge close** | **~135s** |

The **107s final WORD_BLAST** dominates: it bit-blasts the entire Karatsuba+Prop3 structural
skeleton (over the abbreviated pmul atoms) in one shot. This is the cost Mila's approach targets.
(Note: in the *committed* proof this same close runs as ~185s because it also carries the s348
hypothesis context; on the isolated abstract goal it is ~135s. Either way the final structural
blast is the bottleneck.)

## Mila-route bridge lemmas, ported to our checkpoint (one-time costs, measured)
These are pure WORD_BLAST identities; they prove fine on our polyval-aes checkpoint with no extra
deps. They are proved ONCE and reused across all N-block proofs:

| Lemma | One-time proof cost |
|-------|---------------------|
| `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` (Karatsuba-mid recombine ↔ Prop3 limbs) | ~4.0s |
| `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` (two-phase reduction as a closed-form rewrite) | ~51.4s |
| (also need `DOUBLE_SUBWORD_JOIN/_HI`, `karatsuba_mid`, `PMUL_W_64_128` — all small) | ~secs |

## Mila's closure structure (why it should avoid the 107s blast)
Instead of one monolithic `WORD_BLAST` over the whole skeleton, Mila:
1. `GHASH_POLYVAL_ACC_1`/`_2` to express the GHASH as `polyval_reduce_prop3(...)`.
2. `PMUL_KARATSUBA` + `KARATSUBA_LIMBS` to split each multiply into 3 half-mults.
3. `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` — a **rewrite** for the mid recombination.
4. `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` — a **rewrite** turning the two-phase reduction
   into the closed `word_join (...) (...)` form directly. *This replaces the expensive final
   bit-blast with a single targeted rewrite.*
5. Abbreviate pmul halves; a small residual `WORD_BLAST`.

The expensive monolithic blast is replaced by step-4's rewrite + a much smaller final blast.

## Caveat surfaced by the experiment (important)
On the **isolated abstract goal**, our LHS keeps the simulator's `word_reversefields` operand
form while the GMULT-expanded RHS uses `byteswap128`-derived operands; `MERGE_PMUL_ATOMS_TAC`
only partially unifies them, so the isolated baseline is a slightly harder goal than the
in-context one. Mila's bridge lemmas are stated over the *abstract limb* form, so to apply them
to our term we must first normalize our `reversefields`/halfswap operands into her
`(a,b,c,d)`/`(xl,xh,xm)` shape (the `byteswap128 h` key reconciliation from
`_docs/ghash-1block-bridge-halfswap-findings-20260603.md`). That normalization is the porting
work; it is mechanical but non-trivial because our htable convention (`byteswap128 h`, on-the-fly
mid) differs from Mila's (precomputed `karatsuba_mid` loaded from htable).

## Root cause pinned (measured)
The post-MERGE goal is small (1254 chars, 2 residual pmuls), yet `FINISH_WV` takes ~107s. The
two residual pmuls are **`word_pmul ARG (word 0xC200000000000000)`** — the Prop3 reduction's
multiply-by-W. Measured fact: bit-blasting even a **single** `word_pmul _ W` identity
standalone does **not finish in 240s** (`BITBLAST_TAC` on a non-constant carryless multiply is
intractable). `FINISH_WV` only closes the full goal in 107s because `WORD_BLAST` handles the two
W-pmuls *structurally inside the surrounding XOR/join skeleton* (they appear on both sides and
largely cancel) rather than expanding either standalone. **So the entire ~107s is the cost of
bit-blasting the W-multiply reduction.**

## VERDICT — does Mila's approach reduce the time? YES, and here is exactly why
- **Bottleneck:** the ~107s is bit-blasting the Prop3 **W-multiply reduction** (`word_pmul _ W`)
  inside the final structural blast. MERGE adds ~27s. Total s348 close ≈135s (≈185s in-context).
- **Mila's approach removes precisely this.** Her closure never bit-blasts a `word_pmul _ W`:
  `PMUL_W_64_128` rewrites it to the closed shift form `shl63 ⊕ shl62 ⊕ shl57` and
  `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` then rewrites the whole two-phase reduction to a closed
  `word_join(...)(...)` — both are **targeted rewrites, not blasts**. After them only a small
  residual `WORD_BLAST` over abstracted halves remains (seconds). The two bridge lemmas are a
  one-time cost (measured here: RECOMBINE ~4s, BARRETT ~51s) amortized across ALL N-block proofs.
- **Why ours pays the cost:** our `GMULT_FULL_CORRECT_BA` produces `word_pmul _ W` terms in the
  goal, which `FINISH_WV` must blast. Mila's spec stack keeps the reduction in shift form, so it
  is rewritten away before any blast. This is a structural advantage of her closure, independent
  of block count.
- **Estimated win at 1 block:** s348 close ~135s → roughly **~30–40s** (MERGE/normalize ~27s +
  the Barrett/recombine rewrites + a small blast), i.e. the ~107s W-blast replaced by ~seconds of
  rewriting. Net full-proof time ~371s → ~**260–280s**.
- **Larger win at 2+ blocks:** our single-multiply `GMULT_FULL_CORRECT_BA` route does not even
  apply to the aggregate (`(acc⊕b0)·H² ⊕ b1·H`); a monolithic blast would face *more* W-pmuls and
  grow badly. Mila's reduction is a **single rewrite regardless of N** (the binary reduces once),
  so her closure is the clearly-scalable choice for N≥2.

## What was NOT completed (honest scope)
A full end-to-end Mila-route close of our actual s348 term was not run to QED, because applying
her abstract-limb bridge lemmas to our term first needs an operand-normalization port: our
simulator term is in `word_reversefields`/halfswap/`byteswap128 h` form, while her
`KARATSUBA_RECOMBINE`/`BARRETT_REDUCTION` lemmas are stated over abstract limbs `(xl,xh,xm)` /
`(a,b,c,d)` fed by `PMUL_KARATSUBA`+`KARATSUBA_LIMBS`+`PMUL_W_64_128`. That normalization is
mechanical but real work (the `byteswap128 h` reconciliation from the bridge-findings doc). The
timing verdict above is therefore: **(i) measured** for the baseline decomposition and the
W-pmul-blast being the bottleneck, and the one-time lemma costs; **(ii) projected** for the full
Mila-route close, grounded in the fact that her route replaces the measured 107s blast with
rewrites. The projection is well-supported but the integrated number (~30–40s) is an estimate,
not yet a measured QED on our term.

## FOLLOW-UP (2026-06-04): attempt to actually WIRE Mila's close into our binary's 1-block

Goal: produce a self-sufficient file (against polyval-aes) that closes our binary's 1-block
GHASH via Mila's reduction-as-rewrite, and measure the time.

### What was ported and PROVEN on the polyval-aes checkpoint (self-contained, no extra needs)
All of Mila's closure machinery proves directly on our checkpoint (some are checkpoint
built-ins). Measured one-time costs:
- `PMUL_W_64_128` — already in `common/polyval.ml` (checkpoint). `word_pmul x 0xC200… = shl63⊕shl62⊕shl57`.
- `PMUL_KARATSUBA`, `KARATSUBA_LIMBS` — already in checkpoint (`common/karatsuba_pmul.ml`).
- `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` — re-proved here, ~4s.
- `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` — re-proved here, ~51s.
- All of Mila's structural helpers (`WORD_INSERT_AS_JOIN_1/2`, `KAR_SUBWORD_LEMMA`,
  `REVERSEFIELDS8_SUBWORD_LO/HI`, `WORD_REVERSEFIELDS_XOR_8_128`, `HALFSWAP_XOR`,
  `REV8_JOIN_FOLD`, `DOUBLE_SUBWORD_JOIN/_HI`, `WORD_OR_SELF`, `karatsuba_mid`) — ~12s total.
- Her tactics (`ABBREV_ALL_PMUL_TAC`, `PMUL_ARG_SORT_CONV`, `ABBREV_PMUL_HALVES_TAC`,
  `PMUL_NORM_CONV`) — port verbatim, compile fine.
So **the file CAN be made self-sufficient** w.r.t. Mila's lemmas; none need her checkpoint.

### UPDATE (2026-06-04, later): the Mila-route close WAS wired in and the file loads end-to-end
An earlier draft of this section reported the wiring as not achieved (Mila's published
recombine/barrett lemmas are shape-coupled to *her* simulator term and don't fire by plain
`REWRITE_TAC` on ours). That obstacle is real, but it was overcome by NOT using her lemmas
verbatim: instead the **r1/r2 reduction-round chain** — the core of her close — was reproduced
directly on OUR `GMULT`-derived term, with two small bridging lemmas (`JOINMID`, `QQ0SPLIT`) to
reconcile the GMULT halfswap mid (`word_subword (word_join qq1 qq1) (64,128)`) into the abstract
limb form the chain consumes.

**Result: `arm/proofs/aesv8_gcm_8x_enc_256_1block_mila_closure.ml` loads cleanly on the
polyval-aes checkpoint (~304s after the 2026-06-05 qq-split optimization; ~355s before),
`AESV8_GCM_8X_ENC_256_1BLOCK` binds with 0 hypotheses and no cheats, and the s348 GHASH bridge is
closed by `FINISH_WV_REDUCE_TAC` (Mila's reduction-as-rewrite), NOT by the committed `FINISH_WV`
monolithic blast.**

**What was KEPT vs. changed (important — the experiment sections above can mislead on this).**
`GMULT_FULL_CORRECT_BA` is **kept**: it is still the bridge from the simulator's `read Q19 @ s348`
byteform to `polyval_dot`, exactly as in nebeid's committed proof. The BA lemma was never the
bottleneck and was not replaced. What changed is **only how the `word_pmul _ W` that BA emits is
discharged**: the old `FINISH_WV` *bit-blasted* it (the ~107s cost); `FINISH_WV_REDUCE_TAC` instead
*rewrites it away* with `PMUL_W_64_128` (`word_pmul x W = shl63 x ⊕ shl62 x ⊕ shl57 x`) and then runs
the r1 reduction round. `WORD_BLAST` is still used throughout — but only on small 64-bit-atom goals
(operand-equality checks, the per-shift RL/RH folds, the final `u`-blast), never on a standalone
`word_pmul _ W`. So the thing the experiment found "didn't scale" was *bit-blasting the W-multiply*,
not `WORD_BLAST` or `GMULT_FULL_CORRECT_BA` as such. Note also the proof does **not** use Mila's
`BARRETT_REDUCTION_EQ_PROP3_REDUCTION` / `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` lemma statements (the
VERDICT section above projected it would) — those are shape-coupled to her simulator term; the close
uses the hand-rolled r1 round plus `JOINMID` / `QQ0SPLIT` instead.

How the shape mismatch was actually bridged (the part the earlier draft thought blocking):
- Our `GMULT_FULL_CORRECT_BA` GSYM produces, at the bridge, the three product atoms qq0/qq1/qq2,
  the W-multiplies, and the halfswap mid `word_subword (word_join qq1 qq1) (64,128)` — with qq1's
  lo limb being the Prop3 reduction limb (named `xhl` by `ABBREV_PMUL_HALVES_TAC`).
- `PMUL_W_64_128` rewrites the W-multiplies to the shift triple `shl63⊕shl62⊕shl57` (the move
  that deletes the 107s carryless-multiply-by-constant blast).
- `JOINMID` collapses the halfswap mid to `word_join (sub qq1 0)(sub qq1 64)`; `QQ0SPLIT` lets
  the bare product atoms qq0/qq1/qq2 be replaced by joins of their named halves; `WORD_SUBWORD_XOR`
  + `ASM_REWRITE` then substitute every half hypothesis, leaving a pure 64-bit-word identity.
- Mila's reduction round then applies verbatim in spirit: abbreviate `r1` = the shift-triple of
  the reduction limb, fold its lo/hi subwords (RL/RH per-shift `WORD_BLAST` lemmas), abbreviate
  the second-round argument `u`, and finish with one `WORD_BLAST` over the atom `u`.

### Measured timing of the Mila-route close (on our s348 bridge term)
Profiled by capturing the real in-context bridge goal (83 hyps, 1629-char concl) once and running
each phase on it. The qq-split was first done with `ASM_MESON_TAC[QQ0SPLIT]`; it was then replaced
by a direct `GEN_REWRITE_TAC LAND_CONV [QQ0SPLIT] THEN ASM_REWRITE_TAC[]` per conjunct. Both
columns are measured on the same captured goal:

| Phase | `ASM_MESON` qq-split (orig) | direct-rewrite qq-split (now) |
|-------|------|------|
| `PMUL_W_64_128` | 0.03s | 0.03s |
| `ABBREV_PMUL_HALVES_TAC` | 0.88s | 0.88s |
| `JOINMID` | 0.03s | 0.03s |
| **qq0/qq1/qq2 split** | **47.76s** | **0.37s** |
| `WORD_SUBWORD_XOR` + `ASM_REWRITE` | 0.11s | 0.11s |
| `JOIN_SUBWORD_RULES` | 0.03s | 0.03s |
| r1 reduction round (abbrev + RL/RH) | 1.11s | 1.11s |
| `u` abbreviation + xor-order fold | 4.94s | 4.94s |
| distribute residual r1 + fold2 | 4.90s | 4.90s |
| **final `WORD_BLAST` over atom `u`** | **30.22s** | **30.22s** |
| **Total s348 Mila-route close** | **~89.6s** | **~42.0s** |

So the W-multiply blast (~107s in the committed `FINISH_WV` route) is gone, replaced by the shift
rewrite + reduction-round chain; and the qq-split — the close's biggest single cost at ~48s — was
cut to ~0.4s by proving each `qqN = word_join …` directly (`QQ0SPLIT` rewrites the bare `qqN` on the
LHS, then the two half hypotheses substitute the subwords) instead of letting `ASM_MESON` *search*
for that. **Measured net: the close dropped from ~89.6s to ~42.0s (~53%).** The remaining cost is
the final `WORD_BLAST` over `u` (~30s) plus the r1/u folds (~11s); those are small-domain blasts and
a possible next target. End-to-end full-file load dropped from ~355s to **~304s** (the close saving
shows up in the total; the rest is the simulation cost — see next section).

### Simulation profiling and the GHASH-tail discard optimization (2026-06-05)
Profiling the full proof per region (wrapping each stepping tactic with a timer) showed the
simulation — not the close — dominates the remaining time. The standout:

| Region | Tactic | Time (before) |
|--------|--------|------|
| steps 333–348 (GHASH multiply/reduce tail) | `ARM_VSTEPS_FOLD_TAC` | **~90s** |
| steps 327–332 (ciphertext store window) | `ARM_VSTEPS_RESOLVE_SIMD_TAC` | ~11s |
| steps 85–173 (AES rounds) | `ARM_STEPS_TAC` | ~4s |
| steps 266–310 | `ARM_STEPS_RESOLVE_TAC` | ~4s |
| steps 185–254 | `ARM_STEPS_TAC` | ~3s |
| (all other regions) | | ~1–3s each |

**Root cause of the 90s in 333–348:** `ARM_VSTEPS_FOLD_TAC` uses `VSTEPS` (which keeps *all*
register/state reads alive) + a per-step `GCM_SIMD_SIMPLIFY` (which rewrites *all* hypotheses).
Per-step profiling showed the hypothesis pile growing **473 → 1357** across the 16 steps, with both
the per-step VSTEP and the per-step simplify scaling with it — classic O(n²). (The proof already
calls `DISCARD_OLDSTATE_TAC "s348"` *after* the region, pruning 1357→77, but by then the cost is
paid.)

**Fix (XTS-style step+fold+discard).** The right model is what plain `ARM_STEPS_TAC` already does:
its per-step `ARM_SINGLE_STEP_TAC` is *step → `DISCARD_OLDSTATE_TAC s` → `CLARIFY_TAC`*, i.e. it
discards old-state reads as it goes (which is why the XTS proof needs no special machinery). The
GHASH tail only differs in needing the REV64 byte-tree folded before the discard, so Q19 survives
as a bounded term. The new `ARM_STEPS_FOLD_DISCARD_TAC` is exactly that, per step n:
`ARM_VERBOSE_STEP_TAC` → `GCM_SIMD_SIMPLIFY_TAC` (fold) → `DISCARD_OLDSTATE_TAC s<n>` → `CLARIFY_TAC`.
This holds the pile flat at **~77 hyps**, each step cheap. Measured: **region ~90s → ~8.8s** (the
original keep-everything `ARM_VSTEPS_FOLD_TAC`'s VSTEPS was both unnecessary and the source of the
blowup — bare step+discard is leaner). Verified end-to-end: full load **~304s → ~219s**,
`AESV8_GCM_8X_ENC_256_1BLOCK` binds, 0 hyps, no cheats.

(An intermediate version, `ARM_VSTEPS_FOLD_DISCARD_TAC`, kept VSTEPS but added the discard — it also
worked, region ~16s, full load ~227.8s. The pure step+discard form above is simpler and faster, so
it is what shipped.)

**Why not the same trick at 327–332** (the next-biggest, ~11s, hyps grow 77→422): tried and it
*does* cut the region to ~7s, **but it breaks the proof** — the subsequent `read (memory :>
bytes128 out_p) s332 = …` store read-back references `read Q9 s331`, which the per-step discard
removes (the surviving `write … = s332` transition still mentions it, but the resolved read-back is
gone). So that region keeps its register reads alive (it genuinely needs them for the store
read-back). The remaining `ARM_STEPS` regions already discard old states automatically and run at
~near-optimal 2–4s.

**Cumulative:** the two optimizations (qq-split rewrite + GHASH-tail step+fold+discard) took the full
load from the original **~355s → ~219s (~38% faster)**, with the proof statement and no-cheat
property unchanged.

### Is this stepping extensible to 2-block / N-block / the full loop?
This refactor answers a design question raised during the work: *can we just "step and simplify as
we go" like XTS, instead of bespoke per-region stepping?* Findings:
- **Yes for the mechanism.** The GHASH tail does NOT need the bespoke `ARM_VSTEPS_FOLD_TAC`; it uses
  the library's standard single-step+discard idiom (`ARM_STEPS_FOLD_DISCARD_TAC`) — the same shape as
  XTS's plain `ARM_STEPS_TAC` — plus only the REV64 byte-tree fold that GHASH instructions require.
- **The fold is the SIMD analogue of the arithmetic simplification that bignum/XTS stepping does
  automatically.** The s2n-bignum accumulating steppers (`ARM_ACCSTEPS_TAC` etc., used throughout the
  `bignum_*` proofs) interleave `ACCUMULATE_ARITH_TAC` after each step — a built-in simplifier that
  recognizes the add/multiply-with-carry outputs and folds the carry chain *as it steps*, so the
  arithmetic state never bloats. XTS's `ARM_STEPS_TAC` likewise keeps the AES state simplified step
  by step. The library has no built-in equivalent for **SIMD byte-permutation** instructions
  (`REV64`/`EXT`), whose symbolic output is a huge byte-tree (~49k–582k chars) — so GHASH must supply
  that simplifier itself: `GCM_SIMD_SIMPLIFY_TAC` (fold REV64 lane trees, cancel double half-swaps,
  normalize nested subwords) is precisely the SIMD-domain counterpart of `ACCUMULATE_ARITH_TAC`. The
  generic hook for exactly this is `ARM_GEN_ACCSTEPS_TAC : (string -> tactic) -> …`, whose per-step
  `acc_preproc` argument is documented as the place to add "rewrites for [the] accumulator to
  recognize" the output; `ARM_STEPS_FOLD_DISCARD_TAC` is a lightweight instance of that pattern with
  the SIMD fold as the per-step simplifier. **So the difference from XTS is not the stepping
  strategy — it is purely that GHASH's instruction mix needs a SIMD simplifier where bignum/XTS need
  (and get, for free) an arithmetic one.**
- **The byte-tree fold + per-step discard is MORE important at 2+ blocks, not less.** N-block and the
  `Loop_mod2x_v8`/`main_loop` paths execute more REV64/EXT and more GHASH steps, so (i) the fold is
  mandatory (bare stepping would carry/`discard` the byte-trees wrongly) and (ii) the per-step
  discard prevents the hypothesis pile from growing with block count. So the *technique* transfers
  and scales.
- **What does NOT transfer verbatim:** the hardcoded step ranges (`333--348`), the fixed-step manual
  assertions (`FIRST_X_ASSUM … Q9 = ciphertext`), and `GCM_SIMD_SIMPLIFY` being tuned to the 1-block
  lane layout. The loop body is driven by `ENSURES_WHILE_*` induction over the block count, not a flat
  step list — so the *driver* differs even though the per-step (step→fold→discard) inner tactic is
  reusable. The recommended 2-block design is therefore: a uniform `ARM_STEPS_FOLD_DISCARD_TAC`-style
  inner stepper applied inside the loop body, with a `trn1/trn2`-aware fold, rather than per-region
  hand-tuning — see `_docs/ghash-2block-extension-and-mila-comparison-20260603.md`.

### What was taken from Mila's proof, and what was taken from nebeid's earlier proof
This file is a deliberate hybrid. To be explicit about provenance:

**From Mila's proof.** Remote `mila` = `https://github.com/manastasova/s2n-bignum-dev`, branch
`one_block_very_messy_v1`, commit `8bc5c9e141f75007034d50fc9db70d30cb3b6b13` (permalinks below
pin that commit so they are immutable):
- The **reduction-as-rewrite strategy**: never bit-blast `word_pmul _ W`; rewrite it to the
  closed shift triple via `PMUL_W_64_128` (a `common/polyval.ml` lemma also present in our
  checkpoint), then drive the Prop3 reduction with a structured **r1 reduction round** —
  abbreviate the shift-triple as `r1`, prove the lo/hi subword folds (`RL`/`RH`) with tiny
  per-shift `WORD_BLAST`s, then abbreviate the second-round argument `u` and finish with one
  small blast. Lifted directly from her **r1/r2 reduction round**,
  [`one_block_aes256_gcm_preloop_tail_direct.ml#L654-L751`](https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/one_block_aes256_gcm_preloop_tail_direct.ml#L654-L751).
  Her closure also wraps this with `KARATSUBA_RECOMBINE_EQ_PROP3_LIMBS` /
  `BARRETT_REDUCTION_EQ_PROP3_REDUCTION`
  ([`arm/proofs/utils/gcm_gmult_v8_nist.ml`](https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/utils/gcm_gmult_v8_nist.ml));
  those did **not** transfer verbatim to our term (see "with modifications" below), but the r1/r2
  round they feed does.
- `ABBREV_PMUL_HALVES_TAC` — ported **verbatim** from her file
  ([`one_block_aes256_gcm_preloop_tail_direct.ml#L329-L370`](https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/one_block_aes256_gcm_preloop_tail_direct.ml#L329-L370));
  it names the 64-bit product halves systematically so the reduction round can be written
  against fixed names.
- The conceptual framing that the close is *one reduction regardless of block count* (her
  `GHASH_POLYVAL_ACC_N` / `BARRETT_REDUCTION_EQ_PROP3_REDUCTION` design,
  [`gcm_gmult_v8_nist.ml`](https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/utils/gcm_gmult_v8_nist.ml)),
  which is why this route is the right basis for the 2-block extension.

**Taken from Mila but with modifications** (her published lemma statements are shape-coupled to
her straight-line simulator term; they were adapted, not copied):
- The r1/r2 reduction round of
  [`one_block_aes256_gcm_preloop_tail_direct.ml#L654-L751`](https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/one_block_aes256_gcm_preloop_tail_direct.ml#L654-L751)
  uses her assembly's reduction limb (`xll`) and a single `t = u` fold; our `GMULT`-route term's
  reduction limb is `xhl` and needs an extra xor-order fold and a residual-`r1` subword
  distribution before the final blast. The round's *structure* (abbreviate r1, RL/RH folds,
  abbreviate u, blast) is hers; the limb names and the two extra fold steps are our adaptation
  — see `FINISH_WV_REDUCE_TAC` in `arm/proofs/aesv8_gcm_8x_enc_256_1block_mila_closure.ml`.

**From nebeid's earlier proof** (`arm/proofs/aesv8_gcm_8x_enc_256_1block.ml`, committed):
- The **entire binary-faithful simulation skeleton**: stepping the real shipped
  `aesv8_gcm_8x_enc_256` through its 1-block branch cascade (352 steps), the `byteswap128 h`
  GHASH-key reconciliation (htable stores H lane-exchanged), the AES front, the
  ciphertext/counter handling, and the s348/s349–351 store-and-byteswap tail.
- `GMULT_FULL_CORRECT_BA` and the `ABBREV_INNER_PMULS_TAC` / `MERGE_PMUL_ATOMS_TAC` /
  `PMUL_CONG_128` machinery that brings our raw `read Q19 @ s348` byteform to the abbreviated
  qq-atom pre-reduction shape that `FINISH_WV_REDUCE_TAC` then consumes.
- The spec statement, preconditions, `define_assert_from_elf` embedding, and `REV64_LANES_EQ` /
  `GHASH_1BLOCK_CORRECT` final-store bridge — all unchanged from the committed proof.

**New glue written for this file** (neither verbatim from Mila nor from nebeid): `JOINMID` and
`QQ0SPLIT`, which reconcile our `GMULT`-route halfswap mid (`word_subword (word_join qq1 qq1)
(64,128)`) and bare product atoms into the abstract-limb form Mila's reduction round expects.
This is exactly the operand-normalization the earlier draft of this doc anticipated as "the
porting work"; it turned out to be two one-line `WORD_BLAST` lemmas plus an `ASM_MESON`
half-substitution, not a simulation-phase rewrite.

### Revised conclusion
- The earlier "must change the simulation phase" pessimism was **too strong**. Mila's *closing
  technique* (W→shift rewrite + r1/r2 reduction round) DOES transfer to our binary's
  `GMULT`-derived term with only small bridging lemmas; her *published recombine/barrett lemma
  statements* do not transfer verbatim, but the technique they encode does.
- The W-multiply blast is genuinely eliminated, confirming the verdict above with a measured
  end-to-end close (now ~42s after the qq-split optimization below, vs ~107s+ for the monolithic
  blast), not just a projection.
- For 2+ blocks this is still the right basis (single reduction regardless of N); the per-step
  simplification during simulation remains a worthwhile *additional* optimization but is no
  longer a *prerequisite* for adopting Mila's close at 1 block.

## Recommendation
- The committed proof (`aesv8_gcm_8x_enc_256_1block.ml`) is unchanged and remains the reference.
  `aesv8_gcm_8x_enc_256_1block_mila_closure.ml` is the Mila-route variant, kept for the 2-block
  work and as the measured demonstration that her close transfers.
- DONE (2026-06-05): `FINISH_WV_REDUCE_TAC`'s qq-split was optimized — `ASM_MESON_TAC[QQ0SPLIT]`
  (~48s) replaced by `GEN_REWRITE_TAC LAND_CONV [QQ0SPLIT] THEN ASM_REWRITE_TAC[]` per conjunct
  (~0.4s), halving the close (~89.6s → ~42.0s) and the full load (~355s → ~304s). The next close
  target would be the final ~30s `WORD_BLAST` over `u`.
- For the 2-block extension, use this `FINISH_WV_REDUCE_TAC` reduction round as the close (it is
  N-agnostic) on top of nebeid's binary-faithful `Loop_mod2x_v8` simulation (see
  `_docs/ghash-2block-extension-and-mila-comparison-20260603.md`).
