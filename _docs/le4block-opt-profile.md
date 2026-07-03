# LE4BLOCK dec BODY — optimization profiling (2026-07-01)

## Baseline per-phase timing (infra preloaded, interactive `e()`):
- FRONT  `full_le4_tac_front`  : **147s**
- STORES `full_le4_tac_stores` : **272s**
- TAIL   `full_le4_tac_tail`   : **433s**  <- biggest
- BRIDGE `full_le4_tac_bridge` : **50s**
- Body total ≈ 902s.  (File loadt 2333s incl le2/le3 transitively + LAYER 2.)

## TAIL sub-profile (from s350):
- pt3 keystream match (318-326)          : 0.3s
- 351-357 VSTEPS_FOLD + X1_MOD128 + disc  : 40s
- 358-368 RESOLVE_SIMD                    : 91s   (goal 453K chars)
- Q9 collapse                             : 6s    (goal 450K)
- 369-372 RESOLVE_SIMD                    : 75s   (goal 630K!)
- 373 RESOLVE_SIMD                        : 26s   (goal 677K!)
- pt3 capture + DISCARD_OLDSTATE s373     : 12s   (goal 677K -> 55K)  <- discard shrinks 12x
- 374-385 VSTEPS_FOLD                     : 141s  <- biggest single
- 386-392 VSTEPS_FOLD                     : 58s

## ROOT CAUSE
O(n^2): the long VSTEPS_FOLD / RESOLVE_SIMD windows KEEP all intermediate states
(s358..s373 = 16 states; s374..s392 = 19 states) alive simultaneously. Each
GCM_SIMD_SIMPLIFY_TAC does RULE_ASSUM_TAC over the WHOLE pile, so cost per step
grows linearly -> quadratic total. The goal balloons to 677K chars before the
first discard.

## FIX (mirror 1block's ARM_STEPS_FOLD_DISCARD_TAC, doc'd 90s->8.8s for a 16-step
GHASH window): the tail's masked-GHASH windows (358-372) are BRANCHLESS and need
NO intermediate register readback (the only readbacks are Q9@s368 collapse and
Q12@s373 pt3 capture, both at window ends). Use per-step-discard stepping there.
For 374-392 (rev64 + masked-blend store + GHASH-to-eor): the store readback is at
s385 and bridge accumulator Q17/18/19 at s392; break into short windows with
DISCARD_OLDSTATE between, keeping the pile flat.

## Same fix applies to STORES windows 314-327 (14 steps) and 335-350 (16 steps),
which also run VSTEPS_FOLD with no intermediate discard.

## RESULTS (validated interactively + full cold load)
New shared stepper `ARM_STEPS_RESOLVE_SIMD_DISCARD_TAC` added to
arm/proofs/aesv8_gcm_8x_dec_256_1block.ml (branch-resolving per-step-discard form of
ARM_VSTEPS_RESOLVE_SIMD_TAC).  Straight-line windows reuse the existing
ARM_STEPS_FOLD_DISCARD_TAC.

Per-window (le4 tail, measured):
- 358-368  91s  -> 9.3s
- 369-373  101s -> 5.7s
- pt3 cap  12s  -> 0.2s
- 374-385  141s -> 9.2s
- 386-392  58s  -> 9.4s
Phase totals: STORES 272s -> 30s ; TAIL 433s -> ~42s ; body ~902s -> ~295s.
Full cold load of le4block.ml (incl le2/le3 transitively): 2333s -> 1696s.
Theorems intact: BODY + wrapper, axioms=3, hyps=0, no cheats.

## PROPAGATED to all dec bands (each cold-loaded clean, axioms=3, hyps=0, no cheats):
- LE4BLOCK: body ~902s -> ~295s; cold load 2333s -> 1696s. (commit 0ba8d30a)
- LE5BLOCK: cold load 1476s -> 407s (3.6x). 358-376 LEFT as VSTEPS (pt4 capture at
  s377 needs the block-4 keystream materialized earlier; discard would drop it).
  (commit 3d318f60)
- LE2BLOCK + LE3BLOCK: stores + masked-tail windows converted; le3 cold load 634s.
  le2 364-370 and le3 374/381 LEFT as VSTEPS (later window re-references an earlier
  state's store readback / single-step register capture). (commit bbf24edf)

## RULE OF THUMB for which windows are safe to per-step-discard:
Convert a multi-step VSTEPS/RESOLVE_SIMD window to *_DISCARD iff every readback it
feeds lands at the window's END state (Q9 mask collapse, Q12 plaintext capture,
store readback, GHASH accumulator) — the current state is always preserved. LEAVE
it keep-everything iff (a) an intermediate-state fact (e.g. a keystream register
materialized upstream) is consumed mid-window, or (b) a LATER window re-MP_TACs an
earlier window's old-state readback.
</content>
