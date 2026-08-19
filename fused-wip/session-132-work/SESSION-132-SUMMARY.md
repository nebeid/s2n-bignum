# Session 132 Summary

## Verdict
advanced

## What I did
- **BREAKTHROUGH — WB_FUSED_3BLOCK (k=3) IS PROVEN, closing a 4-session false-alarm blocker.**
  Ran session-130-work/wb3_v11_lemma.ml (SIM+bridge+all closers, unchanged) under a
  45-min-timeout restore vehicle and it COMPLETED: `PROVE-CALL-DONE cpu_elapsed=777.4
  major_colls_delta=8` → `WB_FUSED_3BLOCK RESULT: hyps=0` → `RESTORE_EXIT=0`. The "MAYCHANGE
  spin" that consumed sessions 128-131 was never a bug — the `prove()` justification-replay
  over the 183-step KEEPGHALL DAG simply takes ~13 min of CPU, and every prior session killed
  it early against restore_fused.sh's 30-min timeout (~7 min of which is DMTCP restore setup).
- Confirmed the tested proof body is byte-identical to wb3_v11_lemma.ml except my 3 timing
  print lines (`diff` exit 0). Preserved the canonical proven artifact as
  session-132-work/WB_FUSED_3BLOCK_PROVEN.ml + full run log wb3term3.out.
- `major_colls_delta=8` in 777s definitively rules out s131's residual GC-thrash framing —
  it is justification-replay (as s131's mechanism said), just FINITE not infinite.
- Corroborating evidence I found: k=2 (WB_FUSED_2BLOCK, s126) had ALREADY completed
  (RESTORE_EXIT=0) with the SAME ARM_STEPS_FOLD_KEEPGHALL_TAC over 2 windows; k=3 = 3 windows,
  so the replay scales with window count — a passing sibling proved the larger was finite too.
- De-risked the arc: verified d5r.o md5 = 968b7a2f… (the STATE-validated fused object baked
  into hol-wb-dec-fused.ckpt), so k=3 is validated against the correct fused machine code.
- Prepared a precise k=4 handoff: session-132-work/K4_DISASM_FACTS.md (fused dispatch map,
  nblk=4 preamble @0x13cc reading htbl+80=h4/+72=fold(h4), bridge assets, spec_to_byteform_wb4
  body, MAYCHANGE-frame extension, the 45-min-vehicle requirement).
- Base-MCP checks (free): confirmed GHASH_POLYVAL_ACC_4 / gcm_ctr_inc are NOT on the base
  polyval-aes image — k=4 dep-checking + validation must run on the fused ckpt.

## What changed in the repo
- NOTHING committed. Tree pristine at 60b4f5a2; .S frozen md5 484fc2d0; HEAD unchanged.
  Per the atomic .S+literal+proof splice discipline, nothing lands until the splice is ready.
- All artifacts live outside the frozen repo: orchestrator/logs/session-132-work/
  {WB_FUSED_3BLOCK_PROVEN.ml, wb3_v11_TERMINATES.ml, wb3term3.out, K4_DISASM_FACTS.md};
  memory wb-dec-fused-3block-s132.md + MEMORY.md index; /tmp/{wb3_term_test.ml,
  restore_fused_long.sh}.
- Advices updated to v104 (added measure-long-sim-prove-to-completion-before-declaring-hung;
  upvoted+corrected maychange-spin-is-prove-justification-replay-not-close 1→2).

## Decisions made
- Ran a termination test BEFORE any restructuring — cheapest path to a possibly-DONE result;
  it paid off (k=3 was already proven). Rationale: no prior session had ever observed the
  replay terminate; the "blocker" was inferred, never measured.
- Did NOT start building k=4 this session: it needs a large new scaffold (4 windows, new
  bridge, spec_to_byteform_wb4) + a ~15-min validation restore, which would risk a
  half-built/dirty handoff with my remaining runway. Handed off a complete k=4 recipe instead.
- Cap enforcement on PROVER_ADVICES.md left to the orchestrator (established s125 precedent;
  reviewer-flagged): the drop candidate is splice-relevant and the bulk is header/Seeded, not
  the Accumulated entries. v104 is not a mult-of-10, so no periodic elimination owed.

## Open issues
- COLD-LOAD BUDGET RISK: if each fused block's `prove` costs ~13-18 min, the eventual spliced
  full-file cold gate could be very long (though s102 GATE_PASS was already cpu=2137s ≈ 36min).
  If it becomes a gate problem, ROUTE 2 (per-step ARM_STEPS_FOLD_DISCARD_TAC à la le4block,
  shrinking the justification tree) can cut the replay — but must handle the cross-window Q18
  mid-accumulator (the reason KEEPGHALL exists). NOT needed for correctness; pure optimization.
- k=3's proof lives only in session-130-work/ + session-132-work/ (scratch), not the repo —
  correct per splice discipline, but it must be spliced into the .ml at splice time.

## Questions for human
(none)

## Continuation prompt for next session
SESSION 133 — PHASE A. **k=3 (WB_FUSED_3BLOCK) IS PROVEN — do NOT reopen it.** The canonical
proof is orchestrator/logs/session-132-work/WB_FUSED_3BLOCK_PROVEN.ml (== session-130-work/
wb3_v11_lemma.ml); it closes hyps=0 no-CHEAT, RESTORE_EXIT=0. The "MAYCHANGE spin" of s128-131
was a FALSE ALARM: the prove-justification-replay is FINITE (~13min CPU) — use the
45-min-timeout vehicle **/tmp/restore_fused_long.sh <check.ml> <TAG> 2700** (NOT restore_fused.sh,
whose 30-min timeout kills the k=3+ replay early). ps-check for a >50%-CPU DMTCP:ocaml-hol
first; kill restores by high-CPU pid ONLY; MCP stays polyval-aes.
NEXT TASK = build WB_FUSED_4BLOCK (k=4). Full recipe in session-132-work/K4_DISASM_FACTS.md:
k=4 enters via the fused dispatch fall-through (x9=0x40) into the preamble @0x13cc (reads
htbl+80=h4, htbl+72=fold(h4)), then the shared tail @0x144c; 4 KEEPGHALL windows (blk0×H⁴…blk3×H
+reduce), bridge ~s214, then tail stores(4)+xi+ivec+MAYCHANGE via a WB4_FRAME_IMP built at file
top (same pattern as WB3_FRAME_IMP). Assets: GMULT4_FULL_CORRECT_BA (in ckpt), spec_to_byteform_wb4
(body in K4_DISASM_FACTS.md, define in-file), GCM_CTR_INC4_LANES (le5block.ml:107 — VERIFY it's in
the fused ckpt, else copy its body), 3 block-0(H⁴) mid distributions (adapt BRIDGE_CLOSE_3_CPH2_TAC
for cph3 unmasked). Template = WB_FUSED_3BLOCK_PROVEN.ml. loadt-check the file on base MCP FIRST
(free syntax check: parse-abort=error, `Unbound value GHASH_POLYVAL_ACC_4`=parse OK). Read exact
window step-numbers + store PCs from /tmp/s108work/d5r_dis.txt (dispatch is 1 branch longer than
k=3; g-stride ~43). THEN the atomic .S+literal+DISPATCH splice (s109 §K), gated by cold gate
PROOF_FILE=arm/proofs/aesv8_gcm_8x_dec_256_wb.ml
TARGET_THEOREM=AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT.
Constraints: .S frozen (md5 484fc2d0); axioms=3/hyps=0/0-CHEAT; land NOTHING until splice ready;
disk 91% — do NOT bake ckpts. At start: git status --porcelain AND git log e3edccb3..HEAD.
