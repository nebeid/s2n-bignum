# AES-GCM 8x decrypt 256, 1-block: proof methodology and how it differs from encrypt

Status: **PROVED** end-to-end. `AESV8_GCM_8X_DEC_256_1BLOCK` in
`arm/proofs/aesv8_gcm_8x_dec_256_1block.ml` binds via a clean full-file `loadt`
(~550s), with no `CHEAT_TAC`/`new_axiom`/`mk_thm` and only the 3 core HOL Light
axioms in the system.

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

3. **Decrypt runs its full epilogue; encrypt does not.** The enc 1-block spec
   exits at `pc+0x11d8` (right after its `st1 {v19}`), so it never steps the
   callee-saved register restores. The dec spec exits at `pc+0x11f8` (the real
   `ret`), so it MUST step `ldp d10,d11,[sp,#16]; ... ; ldp d8,d9,[sp],#80`.
   This forces three spec changes that enc never needed (see §3).

4. **The plaintext store must be materialized mid-fold.** Enc's ciphertext store
   sits in a `VSTEPS_RESOLVE` window where the read-back naturally materializes.
   Dec's plaintext store (`st1 {v12},[x2]` @0x11b8) is buried inside the GHASH
   `ARM_VSTEPS_FOLD` window, which neither materializes store read-backs nor keeps
   them across its discard. The fold has to be split around that store (§4).

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
## 3. Spec changes decrypt needs that encrypt did not (because dec runs the epilogue)

Enc exits before its register restores; dec exits at the `ret`, so the proof steps
`ldp d10,d11,[sp,#16]; ldp d12,d13,[sp,#32]; ldp d14,d15,[sp,#48]; ldp d8,d9,[sp],#80`.
Consequences:

1. **`aligned 16 stackpointer` precondition.** `arm_LDP`'s semantics require
   `(Rn = SP ==> aligned 16 base)`; without it the load falls to the
   `ASSIGNS entirety` branch and `ARM_STEPS_TAC` **silently makes no progress**
   (no error — it just doesn't advance). This was the subtlest blocker.

2. **Eight saved-register stack slots in the precondition.** Quantify
   `d8v..d15v` and assert `read (memory :> bytes64 (word_add stackpointer (word 8*i))) s = d_(8+i)v`
   for `i=0..7` (slots `sp+0..sp+56`). These are arbitrary callee-saved values; they
   appear nowhere in the postcondition — they exist only so the `ldp` restores
   resolve to a definite read.

3. **`MAYCHANGE [SP]` in the frame, plus three stack nonoverlaps.** The
   `ldp d8,d9,[sp],#80` deallocates the frame, so SP at exit = `stackpointer+80` ≠
   entry SP. The ABI-permitted MAYCHANGE set does NOT include SP, so it must be added
   explicitly or `MONOTONE_MAYCHANGE_TAC` fails with "No match". Also add
   `nonoverlapping (X,16) (stackpointer,80)` for `X ∈ {out_p,xi_p,ivec_p}` so the
   stack-slot loads commute past the data stores.

   (Note: Q8–Q15 lower halves change under the restores; the ABI permits only their
   *tophalf*, but the spec's explicit `MAYCHANGE [Q0;...;Q31]` clause already covers
   the full registers, so no extra change is needed there.)

Encrypt sidesteps all four because it never executes the epilogue.

--------------------------------------------------------------------------------
## 4. Materializing the plaintext output store (out_p)

The plaintext is `v12 = bif v12,v26,v0` (blend of the AES-CTR result with the loaded
ciphertext under the all-ones partial-block mask), stored by `st1 {v12},[x2]` at
`0x11b8` (= step 344), which lies INSIDE the GHASH multiply window. Two facts about
`ARM_VSTEPS_FOLD_TAC`:
- it does NOT create a `read (memory :> bytes128 out_p) sN = ...` read-back hyp, and
- it discards old-state memory reads.

So `ENSURES_FINAL_STATE_TAC` is left with an unprovable `read(mem out_p) = plaintext`
goal. Fix: split the fold around the store.

```
ARM_VSTEPS_FOLD_TAC EXEC (329--343)         (* GHASH multiply, Q19 bounded *)
ARM_VSTEPS_TAC EXEC [344]                    (* the store; materializes out_p read-back *)
SUBGOAL read(mem out_p) s344 = word_xor cph (aes256_encrypt ctr0 [k0..k14])
  by [ASM_REWRITE; REWRITE[aes256_encrypt]; REWRITE EL_15_128_CLAUSES;
      REWRITE[aes256_encrypt_round;aese;aesmc]; CONV_TAC(TOP_DEPTH_CONV let_CONV);
      CONV_TAC WORD_BLAST]
ARM_VSTEPS_TAC EXEC (345--350)               (* PLAIN, no discard, so out_p survives *)
re-assert read(mem out_p) s350 = plaintext   (* per-step mem-frame chains via ASM_REWRITE *)
```

The `aes256_encrypt`/`aese`/`aesmc` expansion + `let_CONV` reduces the AES tower to
exactly the assembly's `aese`-tower so `WORD_BLAST` can discharge the all-ones blend
without needing to "understand" AES. Enc does the analogous assert but in its
ciphertext VSTEPS window, so it never has to split a fold.

Then do NOT `DISCARD_OLDSTATE` before/through the bridge — the bridge only reads the
`read Q19 s351` hyp, and discarding drops the `out_p s350` read-back the
postcondition needs. The larger hypothesis pile just makes the bridge ~150s instead
of ~60s; harmless.

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
## 8. Reproduce / re-verify

```
Sys.chdir "/home/ubuntu/workplace/git-code/s2n-bignum-kiro";;
loadt "arm/proofs/aesv8_gcm_8x_dec_256_1block.ml";;   (* ~550s, binds the theorem *)
axioms();;                                             (* must show only the 3 core axioms *)
```
Backup of the completed file: `_backups/aesv8_gcm_8x_dec_256_1block.ml.bck0017`.
