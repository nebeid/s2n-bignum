# Session 126 Summary

## Verdict
advanced

<!-- WB_FUSED_2BLOCK (k=2 of the d5 fused small path) is PROVEN hyps=0, NO CHEAT (RESTORE_EXIT=0).
     The Current Step's core deliverable (the k=2 bridge lane-merge, STEP 1+2 of the continuation
     prompt) is complete, plus the k=2 store tail. Ready for the next step (k=3,4). Nothing committed
     (atomic .S+literal+splice discipline — nothing lands until k=1..4 ready). -->

## What I did
- Git hygiene PASS: HEAD=60b4f5a2 (docs-only ahead of e3edccb3, proof .ml + .S byte-identical),
  .S md5=484fc2d0 (frozen), NO tracked proof-file mods. Clean handoff. Disk 91% — used existing
  hol-wb-dec-fused.ckpt (1.2G), baked no new checkpoints. Recording: session-126.jsonl.
- PROVED WB_FUSED_2BLOCK (k=2) hyps=0, NO CHEAT/new_axiom/mk_thm — validated on the fused ckpt
  (RESTORE_EXIT=0, "WB_FUSED_2BLOCK ... RESULT: hyps=0"). Full proof:
  orchestrator/logs/session-126-work/wb2_v3_qq8fold.ml.
- BRIDGE (the "one remaining task" from s125): a stage-tracing diagnostic (wb2_diag_bridge.ml,
  TRY_REPORT per stage + DUMP QQDEFs) proved the WA_UNIFY blocker was NOT one missing merge but
  THREE block-0×H^2 karatsuba-mid distributions — the fused machine computes them DISTRIBUTED while
  the spec GMULT2 byteform keeps them COMBINED. Fix inserted after MERGE_2BLK_TAC, before WA_UNIFY:
  qq8=qq1⊕qq5 (hi), qq7=qq0⊕qq4 (lo) [EXPAND+CONJUNCT1 WORD_PMUL_XOR+WORD_XOR_ACI], qq12=qq9⊕qq10
  (full-mid, nested-subword operands) [EXPAND+GSYM CONJUNCT1 WORD_PMUL_XOR+PMUL_CONG_128+WORD_BLAST],
  then REWRITE_TAC[WORD_SUBWORD_XOR]. All 8 bridge stages then report OK. QQ8_FOLD_TAC is a no-op
  here (searches for a bare pmul; ABBREV_INNER_PMULS already abbreviated the mid).
- STORE TAIL (found via a CHEAT-and-dump store-diag, wb2_diag_stores.ml): 3 residuals fixed —
  (a) ivec both halves: SUBST gcm_ctr_inc_iter 2 ctr0 = gcm_ctr_inc(gcm_ctr_inc ctr0), GEN_REWRITE
  RAND [GCM_CTR_INC2_LANES], then plain REFL_TAC (NOT WORD_BLAST — that HANGS >6min on the nested
  word_insert tower); (b) block-1 out HI half: address-spelling mismatch (out_p+16)+8 vs out_p+24,
  fixed by a WORD_RULE normalize on both assumptions and goal (same class as the s125 hk+24 fix).
- Updated PROVER_ADVICES to v98 (refined the v97 bridge entry with the complete 3-distribution +
  store solution; upvoted 3 entries used). Wrote memory wb-dec-fused-2block-done-s126 + compacted
  MEMORY.md (19.7KB→~4.5KB).

## What changed in the repo
- NOTHING committed to ~/whole-proofs/s2n-bignum. Tree PRISTINE at 60b4f5a2 (only the pre-existing
  HANDS-OFF _docs/prepretail-probes/build_bench.sh deletion + untracked _docs/orchestrator files).
- Durable artifacts in orchestrator/logs/session-126-work/: wb2_v3_qq8fold.ml (PROVEN k=2, hyps=0),
  wb2_diag_bridge.ml (bridge stage-tracer), wb2_diag_stores.ml (store dumper).
- Memory: wb-dec-fused-2block-done-s126.md (+ MEMORY.md index line, index compacted).

## Decisions made
- Bridge residual is THREE block-0 mid distributions, not one merge (diagnostic-proven). Reason: the
  fused machine distributes block-0's H^2 karatsuba mids (hi/lo/full) that the spec keeps combined.
- ivec store closer: REFL after GCM_CTR_INC2_LANES, NOT WORD_BLAST. Reason: WORD_BLAST on the nested
  gcm_ctr_inc(gcm_ctr_inc) word_insert/bytereverse tower hangs >6min; the machine byte-tower is
  syntactically the lemma's tower, so REFL closes instantly (v42 k=1 precedent).
- No new PROVER_ADVICES entry — refined the existing v97 bridge entry instead (it already scoped this
  scenario; my finding completes its under-specified point (4)).

## Open issues
- k=2 is done but UNCOMMITTED (correct per atomic-splice discipline). Its validity depends on the
  fused ckpt's machine code matching the eventual spliced .S region (exit pc+0x11d0, code 5960 B) —
  re-confirm at splice time (reviewer note carried from s122).
- k=3, k=4 not yet attempted (out of session runway). The route is now fully mapped (see continuation).
- PROVER_ADVICES.md is 264KB (>>36KB cap); bulk is the changelog header + 53 Seeded entries. A scoped
  prover session cannot shave to 36KB without mass Seeded loss — flagged for a dedicated header-trim
  pass (carried from s125).

## Questions for human
(none)

## Continuation prompt for next session
SESSION 127 — PHASE A. WB_FUSED_2BLOCK (k=2) is PROVEN hyps=0 NO-CHEAT — the complete proof is
orchestrator/logs/session-126-work/wb2_v3_qq8fold.ml (validated on hol-wb-dec-fused.ckpt via
/tmp/s108work/restore_fused.sh <check.ml> <TAG>, ~7 min; ONE at a time; ps-check for a 99%-CPU
ocaml-hol first; MCP stays on polyval-aes). Do NOT re-derive k=1 or k=2.

NEXT: extend to k=3 (WB_FUSED_3BLOCK, bridge state s170) and k=4 (s214) as the SAME route-b, per
session-123-fused-k-step-map.md. The generalization pattern is now fully known (see memory
[[wb-dec-fused-2block-done-s126]]):
  * SIM: address-normalize the hk high-half load per H-power (k=2 needed (htbl_p+16)+8=htbl_p+24;
    check the k=3/k=4 stub H^k offsets in the step map — k=3 [x6,#48]/[x6,#64], k=4 [x6,#80]/[x6,#72]);
    inline the accumulator regs Q17/Q18/Q19 self-contained at EACH g-block store boundary, DISCARD,
    KEEPGHALL the next block (capture pt0..pt_{k-2} as SUBGOAL_THEN out-stores before each DISCARD).
  * BRIDGE: use DEC_BRIDGE_CLOSE_TAC k with build_GMULTn_fast k + spec_to_byteform_k (spec_to_byteform_wb3
    already exists in wb.ml:1660 for k=3). For k>=3 the REAL FOLD_MID_HPOW folds run (top_fold=k-1>=2)
    for the MIDDLE blocks, PLUS the same THREE block-0 (highest-H-power) mid distributions
    qq_a=qq_lo⊕qq_lo', qq_b=qq_hi⊕qq_hi', qq_c=qq_mid⊕qq_mid' via WORD_PMUL_XOR that k=2 needed —
    the block-0 distribution is NOT gated by FOLD_MID_HPOW. Use the wb2_diag_bridge.ml stage-tracer
    (TRY_REPORT + DUMP QQDEFs) to read the exact qq atoms per k in ONE run.
  * STORE TAIL: per-block out-store address-norm ((out_p+16i)+8 = out_p+(16i+8)); xi = word_bytereverse
    of the k-block gval; ivec = REFL after GCM_CTR_INC{k}_LANES (SUBST gcm_ctr_inc_iter k then rewrite;
    NOT WORD_BLAST). GCM_CTR_INC2_LANES exists; may need GCM_CTR_INC3/4_LANES (mirror GCM_CTR_INC2_LANES's
    proof: word 1 -> word k substitution + BITBLAST_TAC).
THEN the atomic .S+literal+DISPATCH splice (s109 plan §K, session-109-fused-integration.md), gated by
cold gate PROOF_FILE=arm/proofs/aesv8_gcm_8x_dec_256_wb.ml
TARGET_THEOREM=AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT.

Constraints: .S frozen (md5 484fc2d0); axioms=3/hyps=0/0-CHEAT on every export; land NOTHING until the
splice is ready (atomic .S+literal+proof); partial credit preferred. Disk 91% — do NOT bake
checkpoints. At start: check `git status --porcelain` AND `git log e3edccb3..HEAD`.
