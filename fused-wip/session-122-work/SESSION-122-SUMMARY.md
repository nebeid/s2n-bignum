# Session 122 Summary

## Verdict
advanced

<!-- WB_FUSED_1BLOCK (the d5 fused nblk=1 fast path) is PROVEN hyps=0 END-TO-END, NO CHEAT. This
     closes the entire GHASH-bridge + store-tail obligation that blocked sessions s114-121. The
     nblk=1 leg of the fused small-path arc is DONE. Next: k=2,3,4 (ONE region, per human directive),
     then the atomic .S/literal/DISPATCH splice commit. Tree PRISTINE (nothing landed — multi-session
     atomic-commit discipline; the splice happens only after k=1..4 all close). -->

## What I did
- Hygiene verified: HEAD 60b4f5a2 (docs-only ahead of e3edccb3), proof file + .S byte-identical to
  e3edccb3 (`git diff` empty), .S md5 484fc2d0. Pre-existing HANDS-OFF deletion
  _docs/prepretail-probes/build_bench.sh left untouched. Nothing landed to the tracked proof/.S files.
- Loaded arm/proofs/aesv8_gcm_8x_dec_256_lemmas.ml on the polyval-aes MCP (~117s) for all bridge+store
  helpers; confirmed aes256_encrypt / GHASH_1BLOCK_CORRECT / GCM_CTR_INC_LANES / gcm_ctr_inc_iter defs.
- Ran a STORE97 diagnostic (restore_fused.sh) that dumped all store readbacks at s97 BEFORE
  ENSURES_FINAL — all 3 are bytes128, gval LIVE: xi = word_bytereverse gval; ivec = machine
  lane-shuffle (== gcm_ctr_inc_iter 1 ctr0 unfolded EXACTLY); out = word_xor(word_xor cph AES_TOWER) k14.
- Validated all 3 store-tail closers standalone hyps=0 on the fast MCP, then wired + debugged them
  in-sim across v33–v42 (each restore ~4-5min; probed unclosed goals in-sim to target each fix).
- **PROVED WB_FUSED_1BLOCK hyps=0 end-to-end, NO CHEAT (wb_v42.ml):** sim reaches s97, the GHASH
  bridge closes (s121's BRIDGE_CLOSE_FULL_TAC), and all 6 store half-goals (out/xi/ivec × lo/hi) + PC
  + MAYCHANGE close. Confirmed: "WB_FUSED_1BLOCK v42 RESULT: hyps=0 axioms-clean", RESTORE_EXIT=0,
  no CHEAT/axiom/warning in the load.

## The store-tail solution (three fixes to s121's plan; full detail in PROVER_ADVICES fused entry)
1. OUT: the machine AES input word_join(word_subword ctr0 (8k,8)...) reconstructs ctr0 EXACTLY
   (identity — s121's "byte-reversed ctr0" was imprecise). Standalone JOIN_IS_CTR0 lemma with
   EXPLICIT :16/:32/:64 intermediate word types (WORD_BLAST fails on a reparsed schematic-typed join;
   in-sim types are concrete so it fires), then aes256_encrypt expand + WORD_RULE. NO leading
   AP_TERM_TAC (outer form is word_xor(word_xor cph TOWER) k14, key XOR'd at the END).
2. gval is NOT discarded by ENSURES_FINAL (v37 machine-confirmed gval-in-asl=true). The real trap:
   MULTIPLE `_ = gval` assumptions (read Q19 s84/s85/s86 = gval AND the polyval_dot def = gval); a
   naive EXPAND_TAC/check(rhs=gval) picks a state-read first. FIX: the xi closer's check also requires
   the LHS head to be polyval_dot.
3. Store tail structure: split the 3 bytes128 machine readbacks into bytes64 halves
   (READ_MEMORY_SPLIT_CONV 1) BEFORE ENSURES_FINAL, then ENSURES_FINAL + ASM_REWRITE + REPEAT CONJ_TAC,
   then per-half TRY closers = AP_THM_TAC THEN AP_TERM_TAC (word_subword M k = word_subword S k → M=S)
   then the bytes128 closer: xi (polyval_dot-def SUBST + GHASH_1BLOCK_CORRECT), ivec (num_CONV 1 +
   gcm_ctr_inc_iter + GCM_CTR_INC_LANES — NO WORD_BLAST, it hangs), out (JOIN_IS_CTR0 closer),
   MAYCHANGE (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI + REPEAT CONJ_TAC + MONOTONE_MAYCHANGE_TAC).

## What changed in the repo
- Nothing landed to the tracked proof/.S files (multi-session atomic-commit discipline). Tree PRISTINE
  at HEAD 60b4f5a2, .S md5 484fc2d0.
- Durable artifacts in orchestrator/logs/session-122-work/:
  * wb_v42.ml — the CLEAN full WB_FUSED_1BLOCK proof, hyps=0, no CHEAT (the deliverable).
  * store_closers_validated.ml — JOIN_IS_CTR0 + XI_BYTES128 + the 3 closer recipes.
  * store97-diag.out — the s97 store readback forms.
  * v42_sim_output.txt — the validating run log. wb_v3x/v4x — intermediate debug versions.
- PROVER_ADVICES.md updated to version 94 (refined+upvoted the fused-accumulator entry to score 5;
  upvoted warm-prototype 17, target-raw-band 9, full-sim-skeleton 8). Not committed (orchestrator owns).

## Decisions made
- Store tail = split-readbacks-then-per-half-closers (NOT le1block's no-split), because the fused
  epilogue's tracked stores make ENSURES_FINAL split bytes128 postconds into bytes64 halves. Reason:
  v33 probe showed the half-split is unavoidable here.
- xi closer must select the polyval_dot gval-def specifically (multiple `_=gval` asms exist). Reason:
  root-caused via the v40 gval-defs probe.
- Kept wb_v42.ml as the validated artifact rather than landing it — per the STATE.md atomic-commit
  rule (land nothing until k=1..4 + the .S/literal/DISPATCH splice are all ready).

## Open issues
- k=2,3,4 generalization not started (ONE region instantiated 4×, per the human directive). Each block
  reuses the SAME 3 validated closers; xi accumulates across blocks so the bridge becomes the k-block
  GMULT (build_GMULTn_fast k + DEC_BRIDGE_CLOSE_TAC k, present in the ckpt).
- Nothing committed: the .S/literal splice + DISPATCH re-casing {1,2,3,4}→fused is the final atomic
  commit (s109 plan §K), gated by the cold gate on AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT.
- The v42 closers use TRY(...) wrappers (order-tolerant). For k=2,3,4 with more store goals, consider
  making the dispatch goal-shape-explicit if TRY ordering becomes fragile.

## Questions for human
(none)

## Continuation prompt for next session
SESSION 123 — PHASE A. WB_FUSED_1BLOCK (nblk=1 fast path) is PROVEN hyps=0, NO CHEAT — the complete
proof is orchestrator/logs/session-122-work/wb_v42.ml (validated via /tmp/s108work/restore_fused.sh on
hol-wb-dec-fused.ckpt; polyval-aes MCP + `needs "arm/proofs/aesv8_gcm_8x_dec_256_lemmas.ml"` [~117s]
for the bridge+store helpers). Do NOT re-derive it — the bridge (s121 BRIDGE_CLOSE_FULL_TAC) and the 3
store closers (session-122-work/store_closers_validated.ml) are all validated.
NEXT: generalize to k=2,3,4 as ONE fused region instantiated 4× (STATE.md "PROOF SHAPE: ONE code
region, ONE simulation, instantiated four times"). Steps:
  1. Map the per-k fused step index + entry PCs from the fused objdump (/tmp/s108work/d5r_dis.txt) and
     the le4block GHASH map (orchestrator/logs/session-114-le4block-ghash-map.md). k blocks each finish
     14 AES rounds with GHASH folds INTERLEAVED; the sim length + store count grow.
  2. Reuse the SAME 3 store closers per block: out=JOIN_IS_CTR0+aes+WORD_RULE, ivec=GCM_CTR_INC_LANES
     (each block's ivec = gcm_ctr_inc_iter <blk> ctr0), xi=polyval_dot-def+GHASH_1BLOCK_CORRECT — but
     xi ACCUMULATES: the k-block xi = word_bytereverse(ghash_polyval_acc of k blocks), so the bridge is
     the k-block GMULT (build_GMULTn_fast k + DEC_BRIDGE_CLOSE_TAC k, both present in the fused ckpt;
     see the le4block chain). The store-tail structure (split bytes128 readbacks → per-half AP_THM+
     AP_TERM → closer) carries over per block.
  3. Then the final atomic commit: splice the fused .S region + regenerated define_assert literal +
     DISPATCH re-casing {1,2,3,4}→fused (s109 plan §K, orchestrator/logs/session-109-fused-integration.md),
     gated by the cold gate: PROOF_FILE=arm/proofs/aesv8_gcm_8x_dec_256_wb.ml,
     TARGET_THEOREM=AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT.
Constraints: .S frozen (md5 484fc2d0); axioms=3/hyps=0/0-CHEAT on every export; land NOTHING until the
splice is ready (atomic .S+literal+proof); partial credit preferred. At start: check
`git status --porcelain` AND `git log e3edccb3..HEAD` (hygiene — a clean HEAD with a dirty tree is not a
clean handoff, per STATE.md §3).
