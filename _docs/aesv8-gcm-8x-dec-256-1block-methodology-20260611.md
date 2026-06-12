# AES-GCM 8x decrypt 256, 1-block: proof methodology and how it differs from encrypt

Status: **PROVED** end-to-end. `AESV8_GCM_8X_DEC_256_1BLOCK` in
`arm/proofs/aesv8_gcm_8x_dec_256_1block.ml` binds via a clean full-file `loadt`
(~239s after optimization; ~554s for the first completed version), with no
`CHEAT_TAC`/`new_axiom`/`mk_thm` and only the 3 core HOL Light axioms in the system.
Exit is `pc+0x11e4` (right after the xi_p store).

Companion docs:
- Encrypt methodology: `_docs/aesv8-gcm-8x-enc-256-1block-methodology-20260603.md`
- Encrypt closure proof (Mila route): `arm/proofs/aesv8_gcm_8x_enc_256_1block_mila_closure.ml`
- Live working notes / recipe: `memory/project_dec_tail_solved.md`

This document assumes familiarity with the encrypt 1-block proof and focuses on
**what is the same**, **what is genuinely different**, and **the traps that cost
the most time** in decrypt.

--------------------------------------------------------------------------------
## 0. TL;DR — the five things that make decrypt different from encrypt

1. **Bridge state is one instruction later.** Enc bridges the GHASH result at
   `s348` (its `result` is complete there). Dec's final reduction `eor v19,v19,v18`
   is at `0x11d4`, executed into `s351`, so the clean `polyval_dot` only appears at
   **`s351`**, not `s350`. Bridging at `s350` (what every earlier handoff assumed)
   can never work: `read Q19 s350` is one XOR short of any `polyval_dot`.

2. **Same GHASH convention, different data block.** Both enc and dec compute
   `polyval_dot (word_xor (brev xi) (brev BLOCK)) (byteswap128 h)` (key is the
   htable-twisted `byteswap128 h`). The only difference is the block:
   enc GHASHes its *computed* ciphertext; dec GHASHes the *loaded* input
   ciphertext `cph`. Net target for dec:
   `read Q19 s351 = polyval_dot (word_xor (brev xi) (brev cph)) (byteswap128 h)`.

3. **Both exit right after their store; neither runs the epilogue.** Enc exits at
   `pc+0x11d8` (after its `st1 {v19}`); dec exits at **`pc+0x11e4`** (after its
   `st1 {v19},[x3]` @0x11e0).  *(Historical: the first completed dec proof exited at
   the real `ret` `pc+0x11f8` and so had to step the callee-saved restores
   `ldp d10,d11,[sp,#16]; ...; ldp d8,d9,[sp],#80`, which forced `aligned 16
   stackpointer`, eight `d8v..d15v` slot preconditions, and `MAYCHANGE [SP]`.  All of
   that was removed by exiting at `pc+0x11e4` — see §3 and §8.)*

4. **The plaintext store read-back must be materialized at the store.** Enc's
   ciphertext store sits in a `VSTEPS_RESOLVE` window where the read-back naturally
   materializes.  Dec's plaintext store (`st1 {v12},[x2]` @0x11b8) is buried inside
   the GHASH `ARM_VSTEPS_FOLD` window, which neither materializes store read-backs nor
   keeps them across `DISCARD_OLDSTATE`.  Materialize it with a plain `ARM_VSTEPS [344]`
   + assert, then carry that single out_p fact to the postcondition via `MP_TAC`/`DISCH`
   across the pre-bridge discard (§4, §8).

5. **The reduction lane-blast needs an extra split, and FINISH_WV diverges.**
   `FINISH_WV_REDUCE_TAC` (which closes enc) stack-overflows on the dec goal shape.
   The dec close inlines its r1/u/r2 staging by hand and adds one `QQ0SPLIT` that
   enc's path didn't need (§5).

--------------------------------------------------------------------------------
## 1. What is shared with encrypt (do NOT reinvent)

- **Front simulation (steps 1–265):** byte-identical to enc (the AES-256 CTR
  keystream tower over `ctr0,k0..k14`). Stepped with `ARM_STEPS_TAC` +
  `DISCARD_COUNTER_REGS_TAC`, with the **step-176 tag fix**: step THROUGH the
  rev64 (`174--177`) + ONE `GCM_SIMD_SIMPLIFY_TAC` so the partial GHASH tag in Q19
  reaches the tail as the stable `word_reversefields`/`word_bytereverse xi` form,
  with **no `ABBREV_TAC`** (an abbrev equation gets consumed and loses the xi link).

- **GHASH algebra:** `GMULT_FULL_CORRECT_BA`, `PMUL_KARATSUBA`,
  `polyval_reduce_prop3`, `polyval_dot`, `byteswap128`, `REV64_LANES_EQ`,
  `GHASH_1BLOCK_CORRECT`, and the helper tactics `ABBREV_INNER_PMULS_TAC`,
  `MERGE_PMUL_ATOMS_TAC`, `PMUL_W_64_128`, `JOINMID`, `QQ0SPLIT`,
  `SUBWORD_XOR_JOIN_DIST`, `JOIN_SUBWORD_RULES`, `WORD_SUBWORD_XOR`. All reused
  verbatim from the enc/Mila infrastructure.

- **The Prop3 reduction constant** `0xC200000000000000` lives at `[SP+64]`, written
  by the prologue and carried as a precondition (`read (memory :> bytes64
  (word_add stackpointer (word 64))) s = word 13979173243358019584`). Same as enc.

- **The reduction is byte-identical to enc.** Hand-traced instruction by
  instruction: dec's `0x11a4..0x11d4` computes the same `v18` and same `v19'` as
  enc's `0x11b0..0x11d0`; both then `ext`+`rev64`+store. The ONLY divergence is the
  block fed in (loaded `cph` vs computed ct), so once you bridge at the right
  state, the close is the enc close.

--------------------------------------------------------------------------------
## 2. The bridge-state pitfall (s350 vs s351)

Every earlier dec handoff tried to bridge `read Q19 s350` and failed, concluding
the dec reduction "doesn't match `GMULT_FULL_CORRECT_BA`". That was a state-offset
error, not an algebra problem.

Decrypt tail (machine code in the work file, NOT the .o objdump which is a
different build):

```
0x11d0  eor   v19,v19,v17     -> s349->s350 boundary
0x11d4  eor   v19,v19,v18     <- read PC s350 = 0x11d4 means THIS is not yet done at s350
0x11d8  ext   v19,v19,v19,#8
0x11dc  rev64 v19,v19         -> final stored value
0x11e0  st1   {v19},[x3]      -> xi_p
```

So `read Q19 s350` is missing the `0x11d4` XOR. Step it (`ARM_VSTEPS_FOLD [351]`)
and `read Q19 s351` is the clean
`polyval_dot (word_xor (brev xi) (brev cph)) (byteswap128 h)`.

**How this was settled decisively:** instantiate `xi,cph,h` to concrete int128
values and `WORD_REDUCE`/`WORD_PMUL_CONV` the byteform and each candidate target.
`read Q19 s350` matched nothing; `read Q19 s351` matched `polyval_dot X (byteswap128 h)`
exactly; and `read Q19 s353` (after ext+rev64) equalled the spec value
`word_bytereverse(ghash_polyval_acc (byteswap128 h)(brev xi)[brev cph])` exactly.
Validating the reducer against the PROVEN `GMULT_FULL_CORRECT_BA` first (result =
polyval_dot for concrete operands) ruled out a harness bug. This concrete pre-check
is the single most valuable habit: it turns a multi-hour diverging-BITBLAST hunt
into a one-second yes/no.

--------------------------------------------------------------------------------
## 3. Exit point: stop after the xi_p store (do NOT step the epilogue)

**Current proof:** exit at `pc+0x11e4`, the instruction right after the xi_p store
`st1 {v19},[x3]` (@0x11e0).  The proof steps `... ARM_VSTEPS [354]` (the store) and
stops — it never executes the callee-saved register-restore epilogue
(`mov x0,x9; ldp d10,d11,[sp,#16]; ldp d12,d13,[sp,#32]; ldp d14,d15,[sp,#48];
ldp d8,d9,[sp],#80; ret`).  This mirrors enc, which exits at `pc+0x11d8` right after
its own store.  With this exit the spec is clean: no stack-frame clauses at all.

### Historical: what stepping the epilogue cost (removed — do NOT reintroduce)

The first completed proof exited at the real `ret` (`pc+0x11f8`) and therefore stepped
the four `ldp` restores.  That forced four spec complications, all since deleted:

1. **`aligned 16 stackpointer` precondition.** `arm_LDP`'s semantics require
   `(Rn = SP ==> aligned 16 base)`; without it the load falls to the
   `ASSIGNS entirety` branch and `ARM_STEPS_TAC` **silently makes no progress**
   (no error — it just doesn't advance).  This was the subtlest blocker.
2. **Eight saved-register stack slots** `d8v..d15v` in the precondition
   (`read (memory :> bytes64 (word_add stackpointer (word 8*i))) s = d_(8+i)v`,
   `i=0..7`), so the `ldp` restores resolve to a definite read.
3. **`MAYCHANGE [SP]`** (the `ldp d8,d9,[sp],#80` deallocates the frame, SP ends at
   `stackpointer+80`; the ABI set excludes SP so `MONOTONE_MAYCHANGE_TAC` fails without it).
4. **Three `nonoverlapping (X,16) (stackpointer,80)`** for `X ∈ {out_p,xi_p,ivec_p}`.

Exiting at `pc+0x11e4` removes all four — the simplest big win (see §8).  If you ever
need the post-`ret` contract, this is the price; otherwise stop after the store.

--------------------------------------------------------------------------------
## 4. Materializing the plaintext output store (out_p)

The plaintext is `v12 = bif v12,v26,v0` (blend of the AES-CTR result with the loaded
ciphertext under the all-ones partial-block mask), stored by `st1 {v12},[x2]` at
`0x11b8` (= step 344), which lies INSIDE the GHASH multiply window. Two facts about
`ARM_VSTEPS_FOLD_TAC`:
- it does NOT create a `read (memory :> bytes128 out_p) sN = ...` read-back hyp, and
- it discards old-state memory reads.

So `ENSURES_FINAL_STATE_TAC` is left with an unprovable `read(mem out_p) = plaintext`
goal. Fix: materialize the read-back at the store, prove it equals the plaintext once,
and carry that single fact to the postcondition (including across the pre-bridge discard).

```
ARM_VSTEPS_FOLD_TAC EXEC (329--343)          (* GHASH multiply, Q19 bounded *)
ARM_VSTEPS_TAC EXEC [344]                     (* the store; materializes out_p read-back *)
SUBGOAL read(mem out_p) s344 = word_xor cph (aes256_encrypt ctr0 [k0..k14])
  by [ASM_REWRITE; REWRITE[aes256_encrypt]; REWRITE EL_15_128_CLAUSES;
      REWRITE[aes256_encrypt_round;aese;aesmc]; CONV_TAC(TOP_DEPTH_CONV let_CONV);
      CONV_TAC WORD_BLAST]
ARM_VSTEPS_TAC EXEC (345--350)                (* finish the GHASH multiply *)
ARM_VSTEPS_FOLD_TAC EXEC [351]                (* the final reduction eor -> Q19 s351 clean *)
FIRST_X_ASSUM(MP_TAC the out_p s344 fact) THEN DISCARD_OLDSTATE_TAC "s351" THEN DISCH_TAC
                                              (* prune the pile, keep out_p as the carried hyp *)
```

The `aes256_encrypt`/`aese`/`aesmc` expansion + `let_CONV` reduces the AES tower to
exactly the assembly's `aese`-tower so `WORD_BLAST` can discharge the all-ones blend
without needing to "understand" AES.  out_p is not written after s344, so the carried
`read(mem out_p) s344 = plaintext` hyp resolves the postcondition directly via
`ASM_REWRITE` at the close.

The `DISCARD_OLDSTATE "s351"` here is the big speed win (§8): the bridge SUBGOAL reads
only the `Q19 s351` hyp, so pruning the ~190-hyp pile to ~80 cuts the bridge from ~150s
to ~65s.  The `MP_TAC`/`DISCH` dance is what makes the discard safe — without it the
discard drops the out_p read-back the postcondition needs.

--------------------------------------------------------------------------------
## 5. The reduction lane-blast (why FINISH_WV_REDUCE_TAC is not enough)

The enc close ends in `FINISH_WV_REDUCE_TAC`. On the dec goal shape it
**stack-overflows**. The dec bridge inlines FINISH_WV's r1/u/r2 staging by hand:

```
GEN_REWRITE LAND_CONV [Q19 s351 hyp]
GEN_REWRITE RAND_CONV [GSYM(LET-reduced ISPECL[X; byteswap128 h] GMULT_FULL_CORRECT_BA)]
REWRITE[byteswap128]; REWRITE[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD]
REWRITE[SUBWORD_XOR_JOIN_DIST]; REWRITE[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES]
ABBREV_INNER_PMULS_TAC; MERGE_PMUL_ATOMS_TAC          (* -> 3 atoms qq0/qq1/qq2, ~28s *)
REWRITE[WORD_XOR_0; SUBWORD0_LEMMAS]; REWRITE[WORD_XOR_0]
REWRITE[PMUL_W_64_128]                                (* word_pmul _ W -> shl 63/62/57 *)
REWRITE[JOINMID]; REWRITE[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR]
GEN_REWRITE ONCE_DEPTH_CONV [QQ0SPLIT]                (* <-- ESSENTIAL, see below *)
REWRITE[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR]
ABBREV xll/xlh/xhl/xhh/xml/xmh = word_subword qq{0,1,2} (0|64,64)
r1 = shl-triple of xhl;  2 SUBGOALs folding subword(r1)(0|64,64)  [EXPAND_TAC"r1"; WORD_BLAST]
u  = word_xor (word_xor (subword r1 0) xhh) (word_xor (word_xor xll xhl) xml)
     + 1 SUBGOAL folding the RHS xor-order of u back to u           [EXPAND_TAC"u"; WORD_BLAST]
r2 = shl-triple of u;    2 SUBGOALs folding subword(r2)(0|64,64)   [EXPAND_TAC"r2"; WORD_BLAST]
CONV_TAC WORD_BLAST                                   (* pure XOR-ACI over 64-bit lanes, ~24s *)
```

**The `QQ0SPLIT` is the dec-specific gotcha.** After `MERGE`, the byteform's outer
`word_xor wv qq0` carries `qq0` as a bare 128-bit atom (the `p_lo` term). The final
`WORD_BLAST` then sees `word_xor r2 qq0` mixing a 128-bit atom with 64-bit lanes and
fails to match. Splitting `qq0` into `word_join (subword qq0 64) (subword qq0 0)`
(then re-collapsing the subwords) eliminates the bare 128-bit atom so the lane
abbreviations cover everything. Enc's `result` doesn't expose a bare `qq0` the same
way, so its path never needed this.

**Always lane-split to 64-bit before the final blast.** A monolithic `WORD_BLAST`
over `word_shl (word_zx _) 63/62/57` (128-bit) diverges (>3600s, hit the MCP timeout
twice). Folding each shift-triple to an abbreviation first makes the final blast a
flat 64-bit XOR identity.

--------------------------------------------------------------------------------
## 6. The ext+rev64 tail and the spec reconciliation

After the bridge: `ABBREV gval = polyval_dot (word_xor(brev xi)(brev cph)) (byteswap128 h)`
so the byte-reorder operates on an atom (otherwise the rev64 explodes Q19 to ~28MB),
then `ARM_VSTEPS_FOLD (352--353)` and
`SUBGOAL read Q19 s353 = word_bytereverse gval` (closed by `WORD_BLAST` on the
collapsed `word_join(reversefields...)...` form). The spec's xi_p postcondition
`word_bytereverse (ghash_polyval_acc (byteswap128 h)(brev xi)[brev cph])` closes via
`EXPAND_TAC "gval" THEN AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT]`
(`GHASH_1BLOCK_CORRECT: polyval_dot (word_xor acc block) h = ghash_polyval_acc h acc [block]`;
`AP_TERM` lifts the shared `word_bytereverse`).

--------------------------------------------------------------------------------
## 7. Infrastructure lessons (cost the most wall-clock)

- **Concrete pre-checks before any BITBLAST.** Instantiate the free vars, reduce,
  compare numerals. A correct reduction blast is seconds; a long hang means a
  wrong/under-specified goal, not a slow-but-correct one.
- **A diverging BITBLAST in the MCP hits the 3600s timeout** and can trigger a
  DMTCP checkpoint-restore that wipes loaded state. Keep every blast bounded; if a
  hang occurs, `hol_interrupt` recovers (the goal rolls back) without losing the
  session.
- **`ARM_VSTEPS_FOLD` discards old-state reads;** protect any memory read-back you
  need downstream by either not folding over it or carrying it via `MP_TAC`/`DISCH`.
- **The work-file machine code, not the `.o` objdump, is authoritative** for step↔PC
  mapping (they were different builds here).

--------------------------------------------------------------------------------
## 8. Performance / optimization history

Full clean-`polyval-aes`-checkpoint `loadt` CPU time:

| State | Time | Change |
|-------|------|--------|
| First completed proof (stepped the epilogue; bridge on the full pile) | ~554s | — |
| Exit after the xi_p store (drop epilogue + stack-frame spec; §3 reverted) | ~529s | -25s, big spec simplification |
| Restore `DISCARD_OLDSTATE` before the bridge (carry out_p via MP_TAC/DISCH) | ~328s | -201s |
| Split the front step group to discard the dead counter Q30 before s10 (commit `c2eea3ce`) | ~284s | -44s |
| Discard the sim pile at s344 before the GHASH reduction (commit `cb55da40`) | ~256s | -28s |
| Discard the sim pile at s340 inside the GHASH multiply (commit `95906676`) | **~239s** | **-17s** |

What moved the needle:
1. **Exit at `pc+0x11e4` (right after the xi_p store), not the `ret`.** Removing the
   callee-saved register-restore epilogue deleted the `aligned 16 stackpointer`
   precondition, the eight `d8v..d15v` saved-slot preconditions, `MAYCHANGE [SP]`,
   and the three stack nonoverlaps — and let the GHASH region drop its fold-split.
   Modest time win, large simplification (mirrors how enc exits right after its store).
2. **Discard the simulation pile before the bridge (~85–150s).**
   The bridge SUBGOAL reads only the `Q19 s351` hyp, but was running on the full
   ~190-hyp pile (~150s). `DISCARD_OLDSTATE "s351"` cuts it to an ~80-hyp pile (~65s).
   The one fact still needed downstream is the out_p plaintext store read-back; carry
   it across the discard with `MP_TAC`/`DISCH` (materialize it at the store via
   `ARM_VSTEPS [344]` + an aese-tower-expansion `WORD_BLAST`).
3. **Split the front step group at s8 to discard the dead counter Q30 (~44s).**
   The committed `ARM_STEPS_TAC (1--11)` bulk group never discarded mid-way, so the
   running counter register Q30 grew into a ~25k-char rev32 byte-tree by s9, and the
   `add v30.4s,v30.4s,v31.4s` at s10 chewed on that whole tree for ~34s (s11 +3.7s) —
   over 10% of total runtime.  Q30 (and the dead blocks 1--7) are not used on the 1-block
   path, so `ARM_STEPS (1--8); DISCARD_COUNTER_REGS; ARM_STEPS (9--11); DISCARD_COUNTER_REGS`
   collapses Q30 to an opaque atom before s9/s10 — steps 1--11 drop from ~44s to ~1.2s.
   *(Corrects the old profiling caveat below: the s10 spike was NOT in a coarse `(12--84)`
   grouping — it was inside the `(1--11)` group itself, which the fine-grained pairs starting
   at step 12 never touched.)*
4. **Discard the sim pile at s344, before the GHASH reduction tail (~28s).**
   `ARM_VSTEPS` cost is O(pile) per step (memory-read resolution), and the pile had grown to
   ~990 hyps by the plaintext store at s344.  Steps 345--351 (the GHASH high/mid eors + the
   EXT/REV64 reorder + the final reduction eor) read only the self-contained Q17/Q18/Q19/Q16/Q8
   register values at s344, so discarding there cuts 345--350 from ~36s to ~12s and step 351
   from ~12s to ~4s.  Carry the out_p plaintext read-back across the discard with `MP_TAC`/`DISCH`
   (it is the only fact the close still needs); a second discard right before the bridge keeps
   the bridge SUBGOAL's `RULE_ASSUM_TAC` scanning only ~80 hyps.
5. **Discard the sim pile at s340, inside the GHASH multiply fold (~17s).**  The multiply fold
   (329--343) was the last O(pile) hot spot (~30--46s), the cost concentrated in its biggest-pile
   tail steps.  The plaintext-blend `bif v12,v26,v0` (@0x11ac = s340) finalizes the plaintext in
   Q12; fold only 329--340, assert `read Q12 s340 = plaintext` (the all-ones-mask blend kills the
   `read Q26 s328` term, so the aese expansion + `WORD_BLAST` closes), then DISCARD the ~755-hyp
   pile carrying that single self-contained Q12 fact.  Folding 341--344 on the pruned pile is then
   ~6s, AND the store at s343 copies the already-clean Q12 atom so the out_p read-back materializes
   in clean plaintext form FOR FREE — removing the separate post-store aese-tower `WORD_BLAST` the
   s344 version needed.  Key to safety: carry the *register* `read Q12 s340` fact (self-contained),
   NOT the store read-back (which references the dropped blend-input registers).

Profiling note (historical — now corrected by item 3): an earlier handoff claimed the s10
~34s counter-init spike came from a coarse `ARM_STEPS_TAC (12--84)` grouping and was avoided
by the fine-grained `(12--13),(14--15),...` pairs.  Re-profiling showed the spike was actually
inside the `(1--11)` group at step s10 (the `add v30.4s` over the accumulated REV32/ADD
byte-tree), which the step-12+ pairs never reached.  Item 3 fixes it directly.

Remaining levers (higher effort, not yet done; see the enc doc §10 for the analogues):
- **GHASH multiply fold (steps 329--343) — SOLVED (commit `95906676`, see item 5 above).**
  Was the largest hot spot (~46s, O(pile) per step).  The earlier "fragile / not cracked"
  note was due to asserting the *store read-back* across the discard (which references the
  dropped blend-input registers).  The fix: assert the *register* fact `read Q12 s340 =
  plaintext` (self-contained — the only old-state term, `word_and (read Q26 s328) (word_not
  allones)`, vanishes for an all-ones full-block mask) BEFORE discarding, carry THAT, and let
  the store at s343 copy the clean Q12 atom (out_p read-back then materializes clean for free).
  A two-discard variant (also at s335) was measured and gives only ~5s more for a second
  6s aese-blast + discard — not worth it; the single s340 discard is the sweet spot.
- **Bridge as a standalone abstract lemma — scalable (a)+(b) form (DONE, commit `05720a30`).**
  **Scalability decision (2026-06-11):** do NOT lift the fused single-block
  `GMULT_FULL_CORRECT_BA` verbatim — it fuses one block's multiply+reduce into a monolithic
  `int128->int128` statement that does not factor for N blocks.  The decrypt/encrypt loop
  accumulates N per-block Karatsuba products into Q17/Q18/Q19 and applies ONE shared Prop3
  reduction per 8-block iteration, so the reusable decomposition is:
  - **(a)** `PMUL_KARATSUBA` (`common/karatsuba_pmul.ml`): the per-block 3-pmull (lo/hi/mid)
    byteform = `word_pmul a b` (256-bit product).  *(already existed)*
  - **(b)** `GMULT_REDUCE_PROP3` (NEW, in the dec file before `GMULT_FULL_CORRECT_BA`): the
    assembly's W-reduction byteform over an ABSTRACT 256-bit accumulator `t` =
    `polyval_reduce_prop3 t`.  Proved by BITBLAST in ~0.9s; helper `V0LO` makes the two
    `word_pmul _ W` atoms syntactically identical first (pmul is opaque to the bit-blaster).
  `GMULT_FULL_CORRECT_BA` is now DERIVED by composing (a)+(b)+`KARATSUBA_LIMBS`+`WORD_PMUL_SYM`
  (REFL close) rather than one monolithic BITBLAST.  Composed with the ALREADY-PROVEN,
  list-generic `GHASH_POLYVAL_ACC_BATCHED` (`common/polyval_ghash.ml` l.318), this is the
  scalable spine for the future 2/4/8-block proofs (the spec-side algebra is already general;
  only (a)/(b) are byteform-specific and both are reused at every block count).
  See `memory/project_bridge_lemma_scalability.md`.

  **Inline-bridge speedup (the ~30s in the dec run): characterized, not landed.**
  After `MERGE_PMUL_ATOMS_TAC` + the 6 lane abbrevs, the bridge's remaining goal is a PURE
  64-bit shift/xor lane identity over `xll/xlh/xhl/xhh/xml/xmh` (no state).  It was extracted
  and proven standalone as `GHASH_WV_LANE_REDUCE` (the r1/u/r2 staging, ~30s), and
  `REWRITE_TAC[GHASH_WV_LANE_REDUCE]` closes the bridge subgoal in one step.  BUT embedding
  that lemma verbatim in the file is unsafe: its ~5.9k-char statement does not round-trip
  through HOL's printer (intermediate word widths are dropped → "inventing type variables" →
  a term NOT alpha-equal to the original).  And within ONE dec load the factoring is
  time-neutral anyway (the 30s staging runs once regardless).  The real win requires
  PROMOTING (b) + a robustly-stated lane lemma to a COMMON checkpoint file so they are
  pre-proven; to state the lane lemma robustly, derive it from (b) via `PMUL_W_64_128`
  (`polyval_reduce_prop3 t` shifted form, HOL-generated in 0.02s) instead of hand-typing it.
  That promotion is a checkpoint change (bigger blast radius) — deferred.
- **`MERGE_PMUL_ATOMS_TAC` tries all atom pairs.** Restrict to the known lo↔lo / hi↔hi /
  mid↔mid pairing to cut redundant WORD_BLASTs inside the bridge.
- **`MERGE_PMUL_ATOMS_TAC` tries all atom pairs.** Restrict to the known lo↔lo / hi↔hi /
  mid↔mid pairing to cut redundant WORD_BLASTs inside the bridge.

--------------------------------------------------------------------------------
## 9. Reproduce / re-verify

```
Sys.chdir "/home/ubuntu/workplace/git-code/s2n-bignum-kiro";;
loadt "arm/proofs/aesv8_gcm_8x_dec_256_1block.ml";;   (* ~239s, binds the theorem; exit pc+0x11e4 *)
axioms();;                                             (* must show only the 3 core axioms *)
```
Backup of the first completed (pre-optimization) file: `_backups/aesv8_gcm_8x_dec_256_1block.ml.bck0017`.
