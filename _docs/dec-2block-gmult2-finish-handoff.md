# Handoff: finish the GMULT2 fast-bridge for dec 2-block (W-reduction surface staging)

**Branch:** `aes-gcm-nblock-tail` (commits unpushed). **Date opened:** 2026-06-24.

## TL;DR
`arm/proofs/aesv8_gcm_8x_dec_256_2block.ml` is **already proven, loadt-clean, no cheats, 3 axioms**
— its GHASH bridge uses the slow `MERGE_2BLK×3 + FINISH_2BLK` route (~73s of the loadt). The new
session's job is to **swap that bridge close to the GMULT2 fast route (~35s projected)** WITHOUT
breaking the proof. Two of the three pieces are proven and measured; only the third (W-reduction
surface staging) remains. **If the swap doesn't pan out, the current MERGE route stays — do not
regress a working proof.**

## What is already proven (reusable; rebuild in-session, see "Session setup")
1. **`GMULT2_FULL_CORRECT_BA`** (~1.2s): the scalable 2-block fused multiply+reduce. Abstract over
   `a0 b0 a1 b1:int128`:
   `<byteform: accumulate 2 Karatsuba triples + one W-reduction> = polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1)`.
   Built from `PMUL_KARATSUBA` + `GMULT_REDUCE_PROP3` (both already in the dec 1-block file) via:
   - `PACK2_ID` (1.14s): `tL = word_pmul a0 b0 XOR word_pmul a1 b1` where
     `tL = word_xor(word_xor(word_zx plS)(word_shl(word_zx crossS)64))(word_shl(word_zx phS)128)`,
     `plS/phS/crossS` = XOR-sums of the two blocks' Karatsuba limbs in **a-then-b** pmul order.
     Proof: `GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REWRITE_RULE[LET_DEF;LET_END_DEF] PMUL_KARATSUBA] THEN REWRITE_TAC[WORD_ZX_XOR; WORD_SHL_XOR] THEN CONV_TAC WORD_RULE`.
   - `gmr_tL2 = REWRITE_RULE[REWRITE_RULE[LET_DEF;LET_END_DEF] KARATSUBA_LIMBS] (SPEC tL (REWRITE_RULE[LET_DEF;LET_END_DEF] GMULT_REDUCE_PROP3))`.
   - GMULT2 itself: `REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN GEN_REWRITE_TAC LAND_CONV [gmr_tL2] THEN AP_TERM_TAC THEN REWRITE_TAC[PACK2_ID]`.
   **Use a-then-b pmul order in the statement (matches PMUL_KARATSUBA output) — critical.**
   Full statement + recipe: `_docs/gmult2-fused-reduce-lemma.md` (the `gmult2_goal_ab` term).
2. **MERGE reconciles the operand transpose in 5.2s (MEASURED)** and fully unifies both byteforms'
   block products — see splice below. The rev64/h <-> brev/byteswap128 transpose is NOT a blocker.

## The exact splice (steps 1-2 WORK; step 3 is the remaining task)
At the bridge subgoal in the file (lines ~456-485), the goal is
`read Q19 s370 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) [word_bytereverse cph0; word_bytereverse cph1]`.
Replace the body `REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN ... ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC (x3) THEN FINISH_2BLK_TAC` with:

```
(* gmult2_dec = SPEC the dec spec-operands into GMULT2 (a0=A0,b0=byteswap128 h2,a1=A1,b1=byteswap128 h) *)
let A0 = `word_xor (word_bytereverse xi) (word_bytereverse cph0)` and A1 = `word_bytereverse cph1` in
let gmult2_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
  (SPECL [A0; `byteswap128 h2`; A1; `byteswap128 h`] GMULT2_FULL_CORRECT_BA) in
... THENL [
  (* rewrite read Q19 s370 to LHS as usual, then: *)
  REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
  (GSYM-fold H^2 via the asm `byteswap128 h2 = polyval_dot (byteswap128 h)(byteswap128 h)`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM gmult2_dec] THEN              (* RHS spec -> GMULT byteform *)
  REWRITE_TAC[MID0_EQ; MID1_EQ; WORD_BYTEREVERSE_REVERSEFIELDS;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN              (* 5.2s: unifies block pmuls -> {qq0,qq1,qq4,qq5,qq8,qq10} *)
  <<< STEP 3: close the W-reduction surface identity >>> ;
  ALL_TAC ] THEN ...
```
After `MERGE_2BLK_TAC`, **both sides are GMULT byteforms over the SAME 6 block atoms**; only the
W-reduction *surface* differs (`gq19` s370 has `word_subword(word_join WV WV)(64,128)` ext-form +
a `byteswap128(word_xor(join)(shl(zx ..)))`; the GMULT byteform lays them out directly). `WORD_BLAST`
DIVERGES on this (same wall the dec 1-block hit).

## STEP 3 — the one remaining task (model: dec 1-block FINISH_WV_REDUCE staging)
The 1-block solves the analogous SINGLE-block W-reduction by hand-staging the shift-triples; see
`arm/proofs/aesv8_gcm_8x_dec_256_1block.ml` **lines 2104-2168** (inside `AESV8_GCM_8X_DEC_256_1BLOCK`'s
s351 bridge). The pattern:
  - `ABBREV_TAC` the six 64-bit lanes `xll/xlh/xhl/xhh/xml/xmh = word_subword qqN (lane)`;
  - **round 1:** abbreviate `r1 = word_xor(word_xor(shl(zx xhl)63)(shl(zx xhl)62))(shl(zx xhl)57)`,
    prove `subword(shl(zx xhl)63)⊕(62)⊕(57) lo/hi = subword r1 lo/hi` by `EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST`;
  - abbreviate `u` (the second-round reduction input), prove its fold by `EXPAND_TAC "u" THEN WORD_BLAST`;
  - **round 2:** abbreviate `r2 = shift-triple of u`, prove its lo/hi folds;
  - final `CONV_TAC WORD_BLAST` (now over the abbreviated r1/u/r2 + lanes — small, ~24-30s).
Helpers already in scope (from the 1-block file): `EQ_BY_SUBWORDS_128` (L1365), `TRIPLE_LO`/`TRIPLE_HI`
(L1373/1378), `PMUL_W_64_128`, `JOINMID`, `QQ0SPLIT`, `V0LO`.

**Generalize this to 2 blocks:** after MERGE the accumulator has 6 block atoms (qq0,qq1,qq4,qq5,qq8,qq10)
instead of the 1-block's 3 (qq0,qq1,qq2), but the W-reduction (`wa`,`v0`,`wv`) is over the SAME
256-bit accumulator shape, so there are still exactly TWO W-multiply rounds (r1 from the wa lane,
r2 from the wv lane). The staging is structurally identical; only the lane expressions feeding r1/u
are bigger (sums of 6 atoms not 3).

### Concrete STEP-3 recipe to try (in order)
1. `GEN_REWRITE_TAC I [EQ_BY_SUBWORDS_128]` (split the int128 eq into two 64-bit lane goals).
2. `REWRITE_TAC[byteswap128]` then `REWRITE_TAC[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR]` (push subwords through joins; collapse the ext `word_subword(join WV WV)(64,128)`).
3. `ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN REWRITE_TAC[PMUL_W_64_128; TRIPLE_LO; TRIPLE_HI]` repeatedly
   (CHANGED_TAC loop) to turn `word_pmul _ W` into clean `word_shl`/`word_ushr` of 64-bit lanes.
4. Stage r1/u/r2 EXACTLY as 1-block L2130-2167 but with the 2-block lane sums. The lane sums to use
   come from the post-MERGE assumptions (the qqN defs) — read them off `goal_state` and write the
   `ABBREV_TAC r1 = shift-triple of <the wa-lane sum>` etc.
5. Final `CONV_TAC WORD_BLAST` (or `BITBLAST_TAC`) — should be ~24-30s over the abbreviated atoms.

**Pitfall observed (2026-06-23):** a naive `ABBREV_SHIFT_TRIPLES`/`ABBREV_SHL_ARGS` generic loop does
NOT fully reduce — a `byteswap128(word_shl(word_zx ..))` cross-term on the RHS stays un-normalized,
and `WORD_BLAST` then diverges. The HAND r1/u/r2 staging (naming the exact intermediates) is what
works in the 1-block; do that, don't rely on a generic triple-abbreviator.

## ACCEPTANCE
- `loadt "arm/proofs/aesv8_gcm_8x_dec_256_2block.ml"` clean; both `AESV8_GCM_8X_DEC_256_2BLOCK` and
  `..._BYTELIST` bind; `axioms()` = 3 core; no `CHEAT_TAC`/`new_axiom`.
- Bridge closes via the GMULT2 route (`GMULT2_FULL_CORRECT_BA` + `MERGE_2BLK` + the new STEP-3 staging);
  `FINISH_2BLK_TAC` and ideally the `MERGE`-internal slow paths no longer needed for the reduce.
- Measure the new bridge time; expect ~35s (was ~73s). Record it.
- **Promote** `GMULT2_FULL_CORRECT_BA` + `PACK2_ID` + the STEP-3 W-staging tactic into the file (near
  the other 2-block helpers, ~line 220), so they're reusable for the 4/8-block and enc proofs.
- If STEP-3 resists after a solid attempt: KEEP the working MERGE/FINISH route, commit GMULT2 as a
  file-level lemma anyway (for reuse), and document the residual. Never ship a broken file.

## Session setup (HOL MCP)
- `Sys.chdir "/home/ubuntu/workplace/git-code/s2n-bignum-kiro"` FIRST (for define_assert_from_elf).
- `needs` not loadt. The dec 1-block dep load is ~530s; full file loadt ~615s. Budget for it.
- To iterate on the bridge WITHOUT 600s re-runs: after a full front run to s370 (the `e(...)` driver,
  ~500s), capture `gq19 = rhs(read Q19 s370 hyp)` into a ref and test bridge tactics standalone with
  `prove(mk_imp(conj of asm23/24/25, mk_eq(gq19, spec)), <tac>)`. asm23/24 = the two `word_subword hk`
  preconditions; asm25 = `byteswap128 h2 = polyval_dot (byteswap128 h)(byteswap128 h)`.
- Rebuild GMULT2/PACK2_ID/gmr_tL2 from `_docs/gmult2-fused-reduce-lemma.md` at session start (they
  were proven in a now-ended session; not in any file yet).

## Key references
- `_docs/gmult2-fused-reduce-lemma.md` — GMULT2 full statement, PACK2_ID, the splice, UPDATE 1-4.
- `_docs/dec-2block-eqprop3-progress.md` — the long investigation (why Mila's EQ_PROP3 layer does NOT
  fit dec; the lane-transpose; UPDATE 1-12). Background, not the active recipe.
- `arm/proofs/aesv8_gcm_8x_dec_256_1block.ml` L1365-1382 (helpers), L1412-1468 (GMULT_REDUCE_PROP3 +
  GMULT_FULL_CORRECT_BA), L2104-2168 (the WORKING 1-block r1/u/r2 W-staging — the model for STEP 3).
- `arm/proofs/aesv8_gcm_8x_dec_256_2block.ml` L456-485 (the bridge to modify), L221-228 (FINISH_2BLK).
- Memory: `project_dec_2block_done`, `project_ghash_nblock_layer_promoted` (corrected — Mila layer
  does NOT drop-in for dec), `project_bridge_lemma_scalability` (the (a)+(b) reduce decomposition).
