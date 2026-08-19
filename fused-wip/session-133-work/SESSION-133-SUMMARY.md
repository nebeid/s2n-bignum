# Session 133 Summary

## Verdict
advanced

## What I did
- Confirmed context: k=1,2,3 fused blocks already PROVEN (s122/s126/s132); this session's task was
  WB_FUSED_4BLOCK (k=4) per STATE Continuation + `session-132-work/K4_DISASM_FACTS.md`.
- **PROVED WB_FUSED_4BLOCK hyps=0, no CHEAT, RESTORE_EXIT=0.** Canonical proof:
  `orchestrator/logs/session-133-work/WB_FUSED_4BLOCK_PROVEN.ml` (== wb4_final.ml, md5 6608aa45).
  Run log `wb4final.out` ends `WB_FUSED_4BLOCK RESULT: hyps=0` + `===RESTORE_EXIT=0===`, 0 exceptions.
- Derived the EXACT k=4 step-map by tracing `d5r_dis.txt` with a branch-follower that reproduces the
  PROVEN k=3 milestones exactly (validation): plain (1--30); w0 blk0×H⁴ KEEPGHALL (31--81) pt0@s81;
  w1 (82--124) pt1@s124; w2 (125--167) pt2@s167; w3+reduce (168--214) bridge@s214; brev@s218;
  xi@s221, ivec@s224, blk3@s226, b@s227. (`session-133-work/K4_STEP_MAP.md`.)
- Ran a diagnostic (`wb4_diag.ml`, CHEAT tail → no 13-min replay) that validated the full 4-window
  SIM to s214 and DUMPed the exact bridge qq-atoms → derived the 3 block-0×H⁴ distributions
  qq14=qq9⊕qq1 (hi), qq13=qq8⊕qq0 (lo), qq20=qq15⊕qq16 (mid).
- Ran a stage-2 close (`wb4_close.ml`) that fired `BRIDGE-CLOSED-s214` and validated all data closers,
  then built the final `prove()` with a block-1 (inc¹) closer added (block-1 is NOT auto-closed
  unlike k=3) and MAYCHANGE via a pre-computed `WB4_FRAME_IMP` (k=3's 52-entry frame + `out_p+48`;
  the dumped ACTUAL-FRAME matched the lemma LHS exactly).
- Free base-MCP syntax checks (stub deps → `REACHED-EOF`) before every fused restore; proved
  `WB4_FRAME_SUBSUMED` and `GCM_CTR_INC4_LANES` on the base MCP first.

## What changed in the repo
- NO s2n-bignum commits (Strategy: "land NOTHING until splice ready"). All artifacts are durable
  files under `~/whole-proofs/orchestrator/logs/session-133-work/`:
  WB_FUSED_4BLOCK_PROVEN.ml, wb4_final.ml, wb4_close.ml, wb4_diag.ml, wb4final.out, K4_STEP_MAP.md.
- Working tree unchanged (pre-existing `D _docs/prepretail-probes/build_bench.sh` still there, per
  s132 reviewer note — do NOT sweep into the splice). `git log e3edccb3..HEAD` = 60b4f5a2 (unchanged).

## Decisions made
- Diagnostic-first with a CHEAT tail to read the bridge qq-indices without paying the ~13-min
  prove-replay — cheapest way to nail the one genuinely unknown part of the bridge. (Matches the
  s126 reviewer-endorsed stage-tracer approach.)
- Added an explicit block-1 (inc¹) closer for k=4 (block-1's hi-half does NOT auto-close under
  ASM_REWRITE the way k=3's captured block did); guarded on `gcm_ctr_inc ctr0` AND NOT inc².
- Built `WB4_FRAME_SUBSUMED` by extending the k=3 frame with `out_p+48` and proving it clean at
  file top (SUBSUMED_MAYCHANGE_TAC), then closing the SIM's MAYCHANGE via `MATCH_MP WB4_FRAME_IMP`
  after discarding non-maychange (the s130-proven route that avoids the post-SIM env spin).

## Open issues
- None for k=4 itself (hyps=0, no CHEAT, clean run). The proof is a scaffold file (interactive-style
  `prove()`), NOT yet integrated into `arm/proofs/aesv8_gcm_8x_dec_256_wb.ml` — that happens in the
  splice phase.
- The k=4 close, like k=3, pays a ~13-min prove-replay. When the full spliced file cold-loads with
  all of k=1..4, budget the gate accordingly (ROUTE 2 per-step discard is a replay-shrinking fallback
  if the cold gate runs too long — pure optimization, not a correctness need).

## Questions for human
(none)

## Continuation prompt for next session
SESSION 134 — PHASE A. **ALL FOUR fused blocks are PROVEN: k=1 (s122), k=2 (s126), k=3 (s132),
k=4 (s133, this session).** k=4 canonical proof = `orchestrator/logs/session-133-work/
WB_FUSED_4BLOCK_PROVEN.ml` (hyps=0, no CHEAT, RESTORE_EXIT=0). The fused-region proof obligations
are COMPLETE. The remaining work is the **atomic .S+literal+DISPATCH splice** (STATE Strategy /
s109 §K, `orchestrator/logs/session-109-fused-integration.md`):
  1. Install the fused `.S` via the generator (STATE VALIDATED block: `python3
     _docs/fused-w1-reorder/gen_w1.py <base.S> <out.S> w5r k=1.0 K=0.35 ct=head clump=4 rejoin=1`,
     expected object md5 968b7a2f0e89093da5d1961d978e4f44; or apply `_docs/fused-w1-reorder/d5r.patch`).
  2. Replace the `_mc` literal in `arm/proofs/aesv8_gcm_8x_dec_256_wb.ml` with the fused object's
     literal (regenerate — the s109 `spliced.ml` is STALE per STATE §2).
  3. Wire the four WB_FUSED_{1,2,3,4}BLOCK proofs + the DISPATCH into the export chain so both
     exported theorems cover nblk in {1,2,3,4} through the fused region, {5..8} and >8 unchanged.
  4. Update the 4 drift-gate anchors: the ONE permitted export drift is `word pc,4968` -> new size
     (5960). Never weaken/delete anchors.
Constraints: .S frozen at md5 484fc2d0 UNTIL the deliberate splice; axioms=3/hyps=0/0-CHEAT on every
export; disk 91% — do NOT bake ckpts; keep the 6 Gc.compact() calls; HANDS OFF ~/clean-gate,
~/kat-check, _docs/, arm/Makefile, include/s2n-bignum.h, benchmarks/benchmark.c. At start:
`git status --porcelain` AND `git log e3edccb3..HEAD` (do NOT sweep the pre-existing deleted
`_docs/prepretail-probes/build_bench.sh` into the splice commit). Cold gate to PASS at the end:
PROOF_FILE=arm/proofs/aesv8_gcm_8x_dec_256_wb.ml
TARGET_THEOREM=AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT.
Fused-block proof templates: session-{122,126,132,133}-work/. Each fused block's `prove` pays a
~13-min replay; the full spliced cold gate will be long — budget it (ROUTE 2 per-step-discard is a
replay-shrinking fallback if needed). Also QUEUED (STATE, after a fused commit): the LENGTH +
two-clause disjointness simplification (would make the drift NONE).
