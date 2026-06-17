# Plan: generalize the AES-GCM counter increment and the N-block goal statement

**Status: PLAN (not started). Author target: whoever picks up the 8-block / general AES-CTR work.**

---

## ⚠ REVISION (2026-06-17) — ADOPT MILA'S SPEC LAYER; DON'T REBUILD IT

After reading Mila's `aes256_gcm_whole` branch in full (see memory
[[reference_mila_aes256_gcm_whole]] and the status writeup), the premise of the
original plan below has shifted. **Mila has already built — and proven — the entire
XTS-style generalized spec layer and the generic bridges this plan set out to construct.**
So most of Tasks 3/4/5/7 are "adopt", not "build". What is genuinely still ours to do is
different (the main loop, our binary, decrypt). Read this section first; treat the
detailed Tasks 0–9 further down as the *fallback "build from scratch" reference*, now
superseded where it overlaps Mila's work.

### What Mila already has (reuse verbatim — `manastasova/s2n-bignum-dev@756df852 arm/proofs/aes256_gcm.ml`)
[permalink](https://github.com/manastasova/s2n-bignum-dev/blob/756df852a0e42ac0229d7d67fb223b843d4afb49/arm/proofs/aes256_gcm.ml)
- **Spec layer (XTS-modeled, byte-list):** `bytes_to_int128` / `int128_to_bytes` /
  `byte_list_at` (verbatim from XTS); `gcm_ctr_iter` (the recursive counter iterator =
  our planned `gcm_ctr_inc_iter`, ALREADY EXISTS); `gcm_keystream`; `gcm_ct_rec` /
  `gcm_ct_bytes_rec` (recursive ciphertext via `prove_general_recursive_function_exists`);
  `gcm_ctm_tail` (masked partial tail); `gcm_ghash_blocks`; `aes256_gcm_encrypt` (top
  ciphertext spec); `gcm_final_xi` (tag spec).
- **Generic bridges (the Task 5 work, done):** `OUT_BRIDGE_GEN` (N−1 full ct stores +
  masked tail ⇔ `byte_list_at (aes256_gcm_encrypt …)`), `BYTE_LIST_AT_BLOCK` /
  `INPUT_BLOCK_BL` / `INPUT_READS_128` (per-block input reads from `byte_list_at`),
  `GHASH_BLOCKS_1..8`.
- **GHASH N-block machinery (the Task 7 work, done):** in
  `arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml` — `kara_acc`/`kara_quad_pmul`/
  `ghash_Nblock_karatsuba`, and the once-proven inductive bridge
  `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` reused for all N; plus the per-block counter-fold
  LANE/CTR lemmas we already cited.
- **Whole-routine theorem:** `AES256_GCM_ENCRYPT_CORRECT` — her binary `aes256_gcm.o`
  correct for every `val len ≤ 128` (0–8 blocks) via length dispatch.

### The crucial caveat — it's a DIFFERENT binary
- Mila proves `aes256_gcm_mc = arm/aes-gcm/aes256_gcm.o`, entry pc+0, the *whole* routine
  with internal length dispatch.
- We prove `aesv8_gcm_8x_enc_256_mc = arm/aes-gcm/aesv8_gcm_8x_enc_256.o`, entry pc+0x18
  (C_ARGUMENTS), the per-call routine.
- Her **theorems** don't transfer to our binary, but her **spec layer + generic bridges +
  counter iterator + GHASH inductive bridge are binary-agnostic** and are exactly what we
  reuse.

### What is actually still open (our real work, in priority order)
1. **Coordinate the shared spec home.** Decide with Mila + upstream where the binary-agnostic
   spec (`byte_list_at`, `aes256_gcm_encrypt`, `gcm_final_xi`, `gcm_ctr_iter`, the generic
   bridges) lives so enc/dec/our-binary/her-binary all `needs` ONE copy (not a fork).
   Likely `common/` or a shared `arm/proofs/utils/` file. This replaces plan Tasks 1/3/4/5.
2. **Wire OUR binary's proofs to her spec.** Re-state `AESV8_GCM_8X_ENC_256_{1,2}BLOCK`
   (and the future N-block) so the postcond is `byte_list_at (aes256_gcm_encrypt …) out_p len`
   + `read xi_p = gcm_final_xi …`, discharged via `OUT_BRIDGE_GEN` / `INPUT_READS_*` /
   the GHASH bridge — replacing our per-block `bytes128`+`gcm_ctr_inc`-literal postconds.
   (This is plan Task 6/6b, but targeting Mila's spec instead of a home-grown `aes_ctr`.)
3. **THE MAIN LOOP / >8 blocks (genuinely new — nobody has done it).** Mila stops at
   `val len ≤ 128` (≤8-block tail dispatch); the bulk `Loop_mod2x_v8` (8-blocks-at-a-time,
   trn1/trn2 interleave) is unproven. This is the largest remaining piece and the main
   point of "reused in the main loop and all tail blocks": the same `gcm_ctr_iter` /
   `gcm_ghash_blocks` / `OUT_BRIDGE_GEN` spec must cover loop iterations too (the loop is
   just `nfull` large), so the spec already fits — the work is the loop *invariant* +
   simulating the interleaved body.
4. **DECRYPT.** Carry the same shared spec to dec (CTR is symmetric: dec keystream is the
   identical `word_xor <cph> (aes256_block_enc (gcm_ctr_iter i ivec) …)`). Only
   `AESV8_GCM_8X_DEC_256_1BLOCK` exists; produce 2-/N-block dec + its main loop.
5. **EVALUATE the GHASH closure (ours vs Mila's) on ONE shared N-block goal, then pick one.**
   Not yet decided — needs a measured head-to-head (see "GHASH closure findings" below).
6. **STACK POSTURE: aim for XTS-style no-stack-clause, but defer the decision to the
   main-loop proof.** Our binary cannot fully skip the stack the way XTS does (see "Stack
   findings" below); the cleanest option is to enter *after* the reduction-constant spill and
   supply that constant as a precond. Decide this once, for the main-loop/whole-binary proof,
   not retrofitted per tail band.

### GHASH closure findings (2026-06-17 evaluation; both approaches read at the pinned commits)
- **Ours** (`aesv8_gcm_8x_enc_256_2block.ml` bridge + `common/polyval_ghash.ml`): per-product
  atom-merge by structural signature (`MERGE_2BLK_TAC`), operand equalities closed by
  `FAST_OPERAND_TAC` (lane-flatten + `WORD_BITWISE`, ~1s) instead of `WORD_BLAST` (~90s). The
  spec side is ALSO list-generic — `GHASH_POLYVAL_ACC_BATCHED` is proven once by induction.
  **Measured: bridge ~73s.** Tactics are tuned to our 256-bit assembly lane shapes.
- **Mila's** (`gcm_aesgcm_nblock_helpers.ml` + `aes256_gcm.ml`): the hard bridge
  `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` is proven ONCE and instantiable for any N, with only
  trivial per-N pieces (`GHASH_BLOCKS_k`, `POLYVAL_DOT_Hk_EQ`). **More scalable BY DESIGN.**
  CAVEAT (verified at `756df852`): that inductive bridge is **not actually wired into her
  concrete per-length bands yet** — each band still hand-closes with `bubble_sort_conv` +
  many `WORD_BLAST` leaves, so its *realized* per-N cost today is comparable hand-work, no
  in-file timings.
- **Verdict:** faster *today* = ours (measured, WORD_BITWISE-optimized); more scalable *by
  design* = Mila's once-proven-bridge pattern (once wired). Neither is a clean win as-shipped.
  **Action (new task):** wire BOTH to one identical N-block bridge goal (e.g. 4-block), time
  them, and adopt the winner — likely a hybrid: Mila's `…_EQ_PROP3` instantiation to avoid
  per-product merging + our `FAST_OPERAND_TAC`/`GHASH_POLYVAL_ACC_BATCHED` for the leaves.
  Promote the chosen lemmas to the shared spec file (item 1).

### Stack findings (2026-06-17; how XTS skips the stack and why GCM can only go partway)
- **XTS skips the stack completely** by (i) entering AFTER the prologue (`pc+28`, past the
  `stp x19,x20,[sp]` / `stp x21,x22,[sp,#16]` callee-saves), (ii) exiting BEFORE the epilogue
  (`pc + LENGTH - 8*4`, before the `ldp` restores + `ret`), so no `[sp]` byte is ever written
  — its MAYCHANGE has NO `bytes(stackpointer,…)` clause (only registers/Qs/flags/ciphertext).
  Sound because it never models the saves/restores; clobbering callee-saved x19–x22 is fine
  in a body lemma since caller-preservation is simply not part of this spec.
- **Our GCM binary has TWO kinds of prologue stack store.** (a) the `d8–d15` callee-saves
  (sp+0..56) — we ALREADY skip these by entering at `pc+0x18`, exactly XTS-style. (b)
  `stp x5,xzr,[sp,#64]` writes the **0xC2000…01 Barrett/Prop3 reduction constant**, which the
  code **reloads 3× as `ldr d16,[x10]` at the MODULO reductions** (`.S` ~lines 682/1101/1503).
  This is an ALGORITHMIC spill→reload, NOT a callee-save — which is why our spec steps it
  inline and carries the `bytes(stackpointer+64,16)` MAYCHANGE clause.
- **So a clean XTS-style total skip is impossible while reaching those reloads.** The viable
  option: enter at **`pc+0x28`** (after the spill), add preconds
  `read (memory :> bytes64 (stackpointer+64)) s = 0xC200…` and `(+72)=word 0`, set
  `X10 = stackpointer+64`, and DROP the `bytes(...,64,16)` clause from MAYCHANGE — then no
  stack *write* occurs (one stack-memory *read* precond remains). Feasible, moderate effort,
  low payoff for a single tail band — **but the right posture for the main-loop/whole-binary
  proof**, where the constant is loaded once and reused across all iterations. Decide it
  there (item 6), not per band.
- **Mila's stance is the OPPOSITE of skipping:** her whole-binary `AES256_GCM_ENCRYPT_CORRECT`
  enters at `pc` (full prologue), `SP=stackptr+80`, and carries the full 80-byte frame
  (`MAYCHANGE [SP]` + `bytes64 stackptr … +72`) — a whole-binary proof must model the real
  push/pop. If we want the XTS no-stack style, that is a deliberate divergence from her shape.

### Revised order of attack
adopt-spec (shared file) → **GHASH-closure bench (pick winner)** → wire enc 1+2 block to it
→ enc main loop (Loop_mod2x_v8, **settle stack posture here**) → decrypt (1,2,…, then its
main loop). Counter-iterator + the N-block spec are already done by Mila; we consume them;
the GHASH *closure tactic* and the *stack posture* are the two things still to decide (above).
Keep everything pointing at ONE shared spec file.

### Open questions to settle before coding
- **Q-stack:** do we want the XTS no-stack-clause posture for our GCM proofs? If yes, the
  target is: enter at `pc+0x28` (after the 0xC2 reduction-constant spill), supply that
  constant + `X10` as preconds, drop the `bytes(stackpointer+64,16)` MAYCHANGE clause. Decide
  for the main-loop/whole-binary proof (not per tail band). Diverges from Mila's full-frame
  shape (see Stack findings).
- **Q-ghash:** which GHASH closure do we standardize on — ours (measured-fast,
  `FAST_OPERAND_TAC`/`GHASH_POLYVAL_ACC_BATCHED`), Mila's (once-proven `…_EQ_PROP3`, scalable
  by design but not yet wired into her bands), or a hybrid? Resolve by the bench in item 5.
- **Q-share:** does Mila intend to upstream `aes256_gcm.ml`'s spec layer to
  `common/`/`arm/proofs/utils/`? If yes, depend on that; if not, lift just the spec+bridges
  into a shared file on our side and `needs` it from both her-style and our-binary proofs
  (coordinate names verbatim so a later merge is a no-op — cf. R5).
- **Q-binary:** are `aes256_gcm.o` and `aesv8_gcm_8x_enc_256.o` the same source compiled
  differently, or different routines? Determines how much of her *concrete* sim/closers we
  can reuse vs. only the spec. (Her concrete bands ARM_STEP her binary; our front/bridge
  already work on ours.)
- **Q-389:** the COPY-DON'T-STUB / `inc32` reconciliation (original Task 2) still applies,
  but note Mila uses `gcm_ctr_inc`+`gcm_ctr_iter`, not `inc32` — the NIST `inc32` bridge is
  still worth having and is still an @UPSTREAM-389 candidate.

---

## Goal

Move the AES-GCM encrypt proofs away from *per-block* spec clauses (one `bytes128`
read and one hand-abbreviated `ct_k` per block, plus a literal counter shuffle in
the precond) toward a **recursive, list-based** statement in the style of AES-XTS:

- ONE postcondition clause `read (memory :> bytes(out_p, 16*N)) s = <CTR spec over the
  whole plaintext buffer>`, instead of N separate `bytes128` clauses;
- the per-block counter modelled by a **defined iterator** of a single increment
  function (not a literal `word_join` shuffle, and not an undefined `gcm_ctr_inc^{k-1}`
  spec phrase), reconciled with the NIST `inc32` from PR #389;
- the per-block counter-fold discharged by **reusable compositional lemmas** (Mila's
  LANE / CTR_WORD_INSERT chain), so the proof cost is linear in the block count.

This subsumes the point-solution `GCM_CTR_INC_LANES` currently in
`arm/proofs/aesv8_gcm_8x_enc_256_2block.ml` (a single monolithic BITBLAST that only
works at a fixed, fully-expanded depth — fine for 2 blocks, does not scale to 8 or
compose into a recursion).

**Order of attack (encrypt first, then decrypt).** Land the machinery on encrypt at 1
then 2 blocks (Task 6 + 6b), then carry the SAME shared spec/utils to the decrypt
proofs (Task 6c), then scale both to 4/8 (Task 8). CTR is symmetric — the decrypt
keystream is the identical `word_xor <data> (aes256_encrypt (gcm_ctr_inc^k ctr0) keys)`
(see `arm/proofs/aesv8_gcm_8x_dec_256_1block.ml`, `word_xor cph (aes256_encrypt ctr0
keys)`), so `aes_ctr`/the iterator/the buffer-read bridge from Tasks 3–5 apply verbatim;
only the spec's "data" argument is the ciphertext (dec) vs plaintext (enc). So decrypt
is a re-use pass, not a re-derivation. NOTE: today only `AESV8_GCM_8X_DEC_256_1BLOCK`
exists (1-block); there is no 2-block dec proof yet, so Task 6c includes producing it.

## Sources to draw from (read these first)

1. **AES-XTS (the structural template for a list-based spec + single-buffer postcond).**
   `arm/proofs/utils/aes_xts_encrypt_spec.ml`:
   - `aes256_xts_encrypt_round P tk key1` — one-block core (`word_xor`/`aes256_encrypt`).
   - `aes256_xts_encrypt_rec i m P iv key1 key2` — recursion over the buffer, defined via
     `prove_general_recursive_function_exists` (WF on `(m+1)-i`) + `new_specification`.
   - `aes256_xts_encrypt P len iv key1 key2` — top spec returning a `byte list`
     (`APPEND rec tail`).
   - byte-list plumbing: `bytes_to_int128`, `int128_to_bytes`, `SUB_LIST`.
   `arm/proofs/aes_xts_encrypt.ml`: the multi-block postcond is ONE
   `read (memory :> bytes(pt_ptr, 0xN0)) s = aes256_xts_encrypt P ...` clause (NOT per-block
   `bytes128`). This is exactly the shape we want for GCM.

2. **PR #389 (NIST SP 800-38D GCM spec — OPEN, not yet merged).**
   Head: `sgmenda:gcm-spec` @ `2f81c762c044ac6dd22a2b9fb5e43c498eb7b767`
   (https://github.com/awslabs/s2n-bignum/pull/389). Adds `common/gcm.ml` (398 lines) plus
   additions to `common/ghash.ml`, `common/misc.ml`, `common/fips197.ml`, `arm/proofs/fips197.ml`.
   Relevant definitions, quoted verbatim from `common/gcm.ml` @ that SHA:
   ```
   let inc32 = new_definition
    `inc32 (cb:128 word) : 128 word =
       let top96:96 word = word_subword cb (32,96) in
       let bot32:32 word = word_subword cb (0,32) in
       word_join top96 (word_add bot32 (word 1 : 32 word)) : 128 word`;;

   let gctr = define
    `gctr (ks:(128 word) list) (icb:128 word) ([] : (128 word) list) = ([] : (128 word) list) /\
     gctr ks icb (CONS x rest) =
       CONS (word_xor x (aes128_cipher icb ks)) (gctr ks (inc32 icb) rest)`;;
   ```
   `gcm_ae` builds `J0 = word_join iv (word 1)`, then `C = gctr ks (inc32 J0) P`.
   - **`inc32` is self-contained** (word primitives only) — copyable verbatim, zero deps.
   - **`gctr` is AES-128-specific** (`aes128_cipher icb ks`, `needs common/fips197.ml`). Our
     proofs are AES-256 (`aes256_encrypt`, `arm/proofs/utils/aes_encrypt_spec.ml`). So `gctr`
     is NOT directly usable: either (i) write the AES-256 analog `gctr256` (same recursion,
     `aes256_encrypt` in place of `aes128_cipher`), or (ii) generalize `gctr` over the cipher
     function — see the UPSTREAM directive in Task 9.
   Our binary-level CTR spec should ultimately be provably equal to `gctr`/`gctr256` so the
   GCM assembly proof composes with the NIST-level spec.

   **COPY-DON'T-STUB POLICY (applies throughout this plan).** Where we need PR389 material,
   COPY the exact definition verbatim from `sgmenda:gcm-spec@2f81c762` into our shared utils
   file, each wrapped in a clearly marked block:
   ```
   (* === BEGIN copied from awslabs/s2n-bignum PR#389 (sgmenda:gcm-spec@2f81c762)  ===
      common/gcm.ml : inc32.  REMOVE this copy and `needs "common/gcm.ml"` once #389 merges. *)
   ...verbatim def...
   (* === END copied from PR#389 === *)
   ```
   This is preferred over hand-written stubs (keeps us byte-identical to upstream, so the
   post-merge cleanup is a delete + `needs`, not a re-derivation). CAVEAT: do NOT wholesale-copy
   `common/gcm.ml` — PR389 also edits `common/ghash.ml`/`misc.ml`/`fips197.ml`, which already
   exist locally with DIFFERENT content; copy only the self-contained defs we need (`inc32`;
   and, if going route (i), the `gctr` recursion shape adapted to `aes256_encrypt`). `inc32` has
   no deps so it copies cleanly; `gctr` drags `aes128_cipher`/`fips197.ml`, so prefer route (i)
   (`gctr256` over the already-present `aes256_encrypt`) rather than importing PR389's AES-128 stack.

   **UPSTREAM-TO-389 DIRECTIVE (mark candidates as you write them).** Anything we add that is
   spec-level and cipher-agnostic — i.e. that *belongs* in the NIST GCM spec rather than in our
   ARM-proof utils — must be tagged in-source with:
   ```
   (* @UPSTREAM-389: <name> -- belongs in common/gcm.ml (NIST spec).  Propose to PR#389 / a
      follow-up.  Reason: <why this is spec-level, not proof-glue>. *)
   ```
   and listed in the "Upstream contributions" section at the bottom of this doc. Concrete
   candidates already identifiable (decide final disposition in Task 0):
   - **`gctr256`** (or a cipher-generalized `gctr`): PR389 only has the AES-128 `gctr`; an
     AES-256 counter-mode spec is genuinely missing upstream and is reusable beyond our proof.
     Strongest upstream candidate. (If PR389 instead generalizes `gctr` over the cipher fn,
     contribute that generalization + the `gctr = gctr_generic aes128_cipher` corollary.)
   - **`AES_CTR_EQ_GCTR`** (Task 4): the equivalence of our recursive CTR spec to `gctr256` —
     spec-level, belongs near the spec.
   - **`INC32_GCM_CTR_INC`** (Task 2): the `inc32` ↔ `gcm_ctr_inc` byteswap bridge — this is
     the link between the NIST counter and the ARM-binary counter; arguably spec-adjacent, but
     since `gcm_ctr_inc` is an ARM-proof artifact it more likely stays in our utils with a
     pointer. Mark `@UPSTREAM-389?` (uncertain) and let the PR389 authors decide.
   Items that are NOT upstream candidates (ARM-proof glue, keep in utils): `gcm_ctr_inc`, the
   LANE/CTR/INSERT fold lemmas, the `GCM_NBLOCK_*` step tactics, the `bytes(ptr,len)`⇔blocks
   bridge — these are about reconciling the *binary's* lane layout with the spec, not the spec.

3. **Mila's N-block helpers (the compositional counter machinery + a model for the tactics).**
   `manastasova/s2n-bignum-dev@756df852 arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml`
   (permalink: https://github.com/manastasova/s2n-bignum-dev/blob/756df852a0e42ac0229d7d67fb223b843d4afb49/arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml):
   - `gcm_ctr_inc` (the ARM rev32+ADD+rev32 increment; we already copied this def).
   - per-block counter-fold lemmas: `LANE0_BYTES_JOIN`, `LANE1_BYTES_JOIN`,
     `LANE2_BYTES_JOIN`, `LANE3_BYTES_JOIN_BE`, `CTR_WORD_INSERT`, `BYTEREVERSE_JOIN_FOLD`,
     `INSERT_IDEM`, `INSERT_SUBWORD` (each a tiny `WORD_BLAST`/`WORD_BITWISE`).
   - `GCM_NBLOCK_CT1_STEP_TAC` / `GCM_NBLOCK_CT_LATER_STEP_TAC n k` / `GCM_NBLOCK_CT_STEP_TAC`
     — close the per-block `ct_k = pt_k ⊕ aes256(ivec_k)` subgoals, peeling `gcm_ctr_inc^{k-1}`
     via the LANE/CTR/INSERT chain.
   - GHASH-side N-block list specs (`kara_acc`, `kara_quad_pmul`, `ghash_Nblock_karatsuba`,
     `GHASH_NBLOCK_KARATSUBA_EQ_PROP3`, the `POLYVAL_DOT_H{4..8}_EQ` power identities) —
     relevant to the GHASH generalization, a parallel track (see Task 7).
   GAPS in Mila's file we must fill: (a) `gcm_ctr_inc^{k-1}` is an *undefined spec phrase*
   handled only tactically — we want a *defined* iterator so it composes in a recursion;
   (b) there is **no recursive ciphertext-list spec** — ciphertext stays per-block; we want
   the XTS-style recursive buffer spec; (c) no `inc32`, so no bridge to the NIST counter.

## Design decisions to settle in Task 0 (do not skip)

- **D1 — element type of the spec list.** XTS uses `byte list` with `bytes_to_int128`/
  `int128_to_bytes`/`SUB_LIST`; PR389's `gctr` consumes a list of blocks. Decide whether
  the GCM CTR spec is over `int128 list` (one element per 16-byte block, cleaner algebra,
  matches `gctr`) or `byte list` (matches XTS plumbing and `bytes(ptr,len)` readback
  directly). RECOMMENDATION: `int128 list` for the core CTR recursion (block = int128),
  with a thin `bytes_to_int128`/`SUB_LIST` adapter only where the memory readback needs it,
  mirroring how XTS bridges `bytes(ptr,len)` to `bytes_to_int128`.
- **D2 — which increment is canonical.** `inc32` (NIST, big-endian top-32 increment) vs
  `gcm_ctr_inc` (the byte-reversed lane form the ARM binary computes). They are the SAME
  arithmetic viewed through a byteswap. Keep BOTH, and prove a bridge `gcm_ctr_inc x =
  <byteswap-conjugated inc32 x>` (Task 2) so: the *spec* can be stated with `inc32`/`gctr`
  (NIST-faithful), while the *proof* folds the binary's lanes via `gcm_ctr_inc`.
- **D3 — iterator form.** Define `gcm_ctr_inc_iter k x` (or reuse `ITER k gcm_ctr_inc x`)
  so block k's counter is `gcm_ctr_inc_iter k ctr0`. A defined iterator is what lets the
  recursive ciphertext spec refer to "block k's counter" uniformly and lets an induction
  step from k to k+1. (Mila avoids this by tactic; we want it defined for composability.)
- **D4 — file location.** New shared helpers belong in `arm/proofs/utils/` (next to
  `aes_xts_encrypt_spec.ml`) or `common/`. RECOMMENDATION: a new
  `arm/proofs/utils/aes_ctr_spec.ml` (CTR spec + iterator + bridge lemmas) and
  `arm/proofs/utils/gcm_ctr_helpers.ml` (the LANE/CTR/INSERT fold lemmas + step tactics,
  ported from Mila). Keep the NIST `gctr`/`inc32` in `common/gcm.ml` (PR389) once it lands.

## Tasks

> **NOTE (2026-06-17 revision):** the tasks below were written assuming we build the
> spec layer + generic bridges + counter iterator + GHASH N-block bridge ourselves from
> XTS + PR389. Mila's `aes256_gcm_whole` branch already provides all of those, proven
> (see the REVISION section at the top). Treat Tasks 1, 3, 4, 5, 7 as **largely satisfied
> by adopting Mila's work** — keep them only as the spec of *what those pieces must
> contain* / a fallback if we cannot reuse hers. Tasks 0 (design decisions), 2 (inc32
> reconciliation / @UPSTREAM-389), 6/6b/6c (wiring OUR binary + decrypt), 8 (4/8 blocks
> AND the main loop), and 9 (PR389 convergence) remain the live work, now re-framed to sit
> on top of her spec.

### Task 0 — Settle the design decisions D1–D4 and write the interfaces
- Deliverable: a short ADDENDUM section in this doc recording the chosen list element type,
  canonical increment, iterator form, and file layout, plus the exact signatures of the new
  definitions to be added (names + types only).
- AC: D1–D4 each have a one-line resolution; signatures type-check as stubs (`new_definition`
  with `CHEAT`-free `ARITH_TAC`/trivial bodies is fine as a stub, or just `?-` existence).
- Depends on: nothing. **Do this first** — everything below references the chosen names.

### Task 1 — Promote `gcm_ctr_inc` + the lane-fold lemmas into a shared utils file
- Deliverable: `arm/proofs/utils/gcm_ctr_helpers.ml` containing `gcm_ctr_inc` and the ported
  `LANE0..3_BYTES_JOIN`, `CTR_WORD_INSERT`, `BYTEREVERSE_JOIN_FOLD`, `INSERT_IDEM`,
  `INSERT_SUBWORD` lemmas (verbatim from Mila, each `WORD_BLAST`/`WORD_BITWISE`). Plus
  `GCM_CTR_INC_LANES` re-derived FROM these compositional lemmas (not a monolithic BITBLAST),
  to validate they compose.
- Files: new `arm/proofs/utils/gcm_ctr_helpers.ml`.
- AC: file loads clean; `GCM_CTR_INC_LANES` proved from the LANE/CTR lemmas (no fresh
  BITBLAST of the full tower); no cheats.
- Depends on: Task 0 (file name/location).

### Task 2 — Reconcile `gcm_ctr_inc` with `inc32` (NIST bridge)
- Deliverable: `INC32_GCM_CTR_INC` : `gcm_ctr_inc x = <byteswap-conjugated inc32 x>` (exact
  RHS form TBD in Task 0/here), proved by `BITBLAST_TAC` (or via the lane lemmas).
- `inc32` itself: COPY verbatim from PR389 (`sgmenda:gcm-spec@2f81c762`, `common/gcm.ml`) into
  `gcm_ctr_helpers.ml` inside a BEGIN/END copied-from-PR389 block per the COPY-DON'T-STUB
  policy (it is self-contained — word primitives only, zero deps). Do NOT hand-stub it.
- Tag `INC32_GCM_CTR_INC` with `@UPSTREAM-389?` (uncertain — see directive; the PR389 authors
  decide whether the NIST↔ARM counter bridge lives upstream or in our utils).
- Files: `arm/proofs/utils/gcm_ctr_helpers.ml`.
- AC: the bridge proves; the copied `inc32` is byte-identical to PR389@2f81c762; a comment
  states the byte-order relationship precisely; both removal markers present.
- Depends on: Task 1.

### Task 3 — Define the counter iterator and its per-block fold lemma
- Deliverable: `gcm_ctr_inc_iter` (D3) and `GCM_CTR_INC_ITER_LANES n` : the k-fold counter
  equals the explicit lane form at depth k — OR, better, a single *step* lemma
  `GCM_CTR_INC_STEP` that rewrites one `gcm_ctr_inc` application on the simulator's lane
  output back to `word_insert`/iterator form, depth-independently (this is the heart of
  Mila's `GCM_NBLOCK_CT_LATER_STEP_TAC`, repackaged as a clean lemma + thin tactic).
- Files: `arm/proofs/utils/gcm_ctr_helpers.ml`.
- AC: from the iterator + step lemma, the block-k counter fold closes for k=1..8 in time
  linear in k (measure it; record in the doc); no monolithic per-depth BITBLAST.
- Depends on: Task 1.

### Task 4 — Define the recursive AES-CTR ciphertext spec (XTS-style)
- Deliverable: in `arm/proofs/utils/aes_ctr_spec.ml`:
  - `aes_ctr_block ctr0 k pt_k keys = word_xor pt_k (aes256_encrypt (gcm_ctr_inc_iter k ctr0) keys)`
    (one block);
  - `aes_ctr_rec i N P ctr0 keys` — recursion over the block list (model on
    `aes256_xts_encrypt_rec`: WF measure `(N+1)-i`, `prove_general_recursive_function_exists`
    + `new_specification`), returning the concatenated ciphertext;
  - `aes_ctr P ctr0 keys` — top spec.
  - `gctr256`: COPY PR389's `gctr` recursion shape verbatim but with `aes256_encrypt` in place
    of `aes128_cipher` (PR389's `gctr` is AES-128-only; do NOT import its `aes128_cipher`/
    `fips197.ml` stack). Wrap in a BEGIN/END copied-from-PR389 block and tag `@UPSTREAM-389`
    (an AES-256 counter-mode spec is missing upstream and is the strongest contribution-back
    candidate). If, by the time this is done, PR389 has generalized `gctr` over the cipher fn,
    use that instead and drop `gctr256`.
  - a lemma `AES_CTR_EQ_GCTR` relating our recursive `aes_ctr` to `gctr256`; tag `@UPSTREAM-389`.
- Files: new `arm/proofs/utils/aes_ctr_spec.ml`.
- AC: definitions admit (recursion existence proved); `aes_ctr` on a concrete 2-block and
  8-block list reduces by `REWRITE`/conversion to the per-block `word_xor`/`aes256_encrypt`
  forms (a KAT-style sanity check, mirroring the XTS test vectors).
- Depends on: Task 3.

### Task 5 — Bridge lemma: recursive spec ⇔ per-block buffer reads
- Deliverable: `AES_CTR_BYTES` : `read (memory :> bytes(out_p, 16*N)) s = aes_ctr P ctr0 keys`
  follows from the N per-block `read (memory :> bytes128 (out_p + 16*k)) s = aes_ctr_block ...`
  facts (and conversely). This is the lemma that lets the proof keep producing per-block
  store readbacks during simulation but state ONE buffer clause in the postcond.
- Files: `arm/proofs/utils/aes_ctr_spec.ml`.
- AC: proved generically in N (induction), or as a reusable tactic; demonstrated to collapse
  2 per-block facts into the single `bytes(out_p,32)` clause.
- Depends on: Task 4. (Check whether XTS already has an analogous `bytes(ptr,len)` ⇔ blocks
  lemma to reuse rather than reinvent — search `aes_xts_encrypt.ml` for the readback-merge.)

### Task 6 — Re-state and re-prove the 2-block enc theorem against the new spec
- Deliverable: `AESV8_GCM_8X_ENC_256_2BLOCK` postcond becomes the single buffer clause
  `read (memory :> bytes(out_p, 32)) s = aes_ctr [plaintext0; plaintext1] ctr0 keys` (CTR
  part) — replacing the two `bytes128` + literal-`gcm_ctr_inc`-in-postcond clauses. The
  proof reuses the existing front/bridge unchanged; only the ct0/ct1 abbreviation +
  store-readback + close change to go through Tasks 3 & 5.
- Files: `arm/proofs/aesv8_gcm_8x_enc_256_2block.ml` (+ `needs` the new utils files).
- AC: loadt-clean, binds, no cheats, 3 axioms; postcond no longer enumerates blocks; the
  xi_p GHASH clause unchanged for now (GHASH generalization is Task 7).
- Depends on: Tasks 3, 5. **This is the first end-to-end validation of the new machinery.**

### Task 6b — Re-state the 1-block enc theorem against the new spec
- Deliverable: `AESV8_GCM_8X_ENC_256_1BLOCK` (`arm/proofs/aesv8_gcm_8x_enc_256_1block.ml`)
  out_p postcond becomes `read (memory :> bytes(out_p,16)) s = aes_ctr [plaintext] ctr0 keys`
  (the N=1 instance of the same recursive spec), so 1- and 2-block enc share one spec shape.
  For N=1 the counter is just `ctr0` (`gcm_ctr_inc^0`), so this exercises the iterator's base
  case and the buffer bridge at N=1 — a small, fast sanity check of the machinery before dec.
- Files: `arm/proofs/aesv8_gcm_8x_enc_256_1block.ml` (+ `needs` the new utils).
- AC: loadt-clean, binds, no cheats, 3 axioms; xi_p clause unchanged. Watch the LE1BLOCK /
  byte-aligned variant in the same file — keep it consistent or note why it differs.
- Depends on: Tasks 3, 5 (and ideally after Task 6, to reuse the worked-out idiom).

### Task 6c — Carry the generalized spec to DECRYPT (1- then 2-block)
- Context: CTR is symmetric, so the decrypt keystream is the same
  `word_xor <data> (aes256_encrypt (gcm_ctr_inc^k ctr0) keys)` as encrypt — only the spec's
  data argument is the ciphertext (input) rather than the plaintext. The Tasks 3–5 machinery
  (`gcm_ctr_inc_iter`, the recursive `aes_ctr`-style spec, the buffer-read bridge) applies
  verbatim; this is a RE-USE pass, not a re-derivation.
- Deliverable, in order:
  1. **Decide the dec spec naming.** Either reuse `aes_ctr` with the ciphertext as the data
    list (cleanest — CTR enc/dec are the same transform), or add a thin `aes_ctr_dec` alias
    if it reads better at the call site. Record the choice in the Task 0 ADDENDUM.
  2. **1-block dec:** re-state `AESV8_GCM_8X_DEC_256_1BLOCK`
    (`arm/proofs/aesv8_gcm_8x_dec_256_1block.ml`) plaintext-out postcond as the single
    `bytes(out_p,16) = aes_ctr [cph] ctr0 keys` clause (N=1). Mind the byte-aligned / partial
    mask path that file handles (`word_and ... (word (2 EXP (8*bl)-1))`) — keep that as-is or
    fold it into the spec explicitly; do NOT regress it.
  3. **2-block dec:** there is NO 2-block dec proof yet — produce
    `AESV8_GCM_8X_DEC_256_2BLOCK` mirroring the 2-block enc structure (the dec 1-block already
    mirrors enc 1-block; reuse that correspondence), with the list-based out_p postcond and
    the shared counter machinery. Reuse the enc 2-block front/bridge approach where the dec
    control flow matches.
- Files: `arm/proofs/aesv8_gcm_8x_dec_256_1block.ml`; new `arm/proofs/aesv8_gcm_8x_dec_256_2block.ml`.
- AC: both dec theorems loadt-clean, bind, no cheats, 3 axioms; out_p postcond list-based;
  the dec proofs `needs` the SAME shared utils as enc (no forked counter/spec definitions).
- Depends on: Task 6 (enc 2-block worked out), Task 6b (enc 1-block worked out). The dec
  GHASH side, like enc, defers its list generalization to Task 7.

### Task 7 (parallel track) — GHASH N-block list spec
- Deliverable: adopt Mila's `kara_acc`/`kara_quad_pmul`/`ghash_Nblock_karatsuba` +
  `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` and the `POLYVAL_DOT_H{4..8}_EQ` power identities, so the
  xi_p postcond is `ghash_polyval_acc K (brev xi) (MAP brev [ct0;..;ctN-1])` over a list and
  the bridge generalizes beyond the hand-written 2-product `GHASH_POLYVAL_ACC_2`.
- Files: `arm/proofs/utils/` (a `gcm_ghash_nblock.ml`), then the enc proof.
- AC: the 2-block bridge re-derived through the list-generic lemma; ready for 4/8 blocks.
- Depends on: Task 1 (shared utils convention). Independent of Tasks 3–6 otherwise.

### Task 8 — Extend to 4 and 8 blocks (encrypt AND decrypt)
- Deliverable: `AESV8_GCM_8X_{ENC,DEC}_256_4BLOCK` / `_8BLOCK` (or one parameterized theorem
  per direction) using the list-based postcond, the iterator-based counter folds (Task 3),
  the buffer-read bridge (Task 5), and the list GHASH (Task 7). NOTE the control-flow change:
  ≥ ~6 blocks may enter `Loop_mod2x_v8` (trn1/trn2 interleave) which 2 blocks avoided — budget
  for that (it affects enc and dec alike).
- Files: new per-N proof files (or one generic) for each direction, `arm/aes-gcm/` objects
  as needed.
- AC: each loadt-clean, no cheats; counter + buffer + GHASH all via the shared machinery
  (no enc/dec fork of the spec); proof size/time grows roughly linearly per block (record it).
- Depends on: Tasks 6, 6c, 7.

### Task 9 — Converge with PR389 once it merges + push contributions back
- Deliverable: once PR389 is merged/local:
  1. DELETE every `BEGIN/END copied from PR#389` block (the copied `inc32`, and `gctr256` if
     PR389 ended up providing an AES-256 / cipher-generic `gctr`) and replace with
     `needs "common/gcm.ml";;`. The copied-block markers make these a mechanical find-delete.
  2. Re-point `INC32_GCM_CTR_INC` / `AES_CTR_EQ_GCTR` at the upstream `inc32`/`gctr` (names
     should already match if we copied verbatim → ideally a no-op).
  3. Open the upstream contributions (see "Upstream contributions to PR #389" below): file an
     issue/PR for each `@UPSTREAM-389` item, primarily `gctr256` (AES-256 counter mode).
  4. (stretch) Check whether AES-XTS's `calculate_tweak`/`GF_128_mult_by_primitive` counter and
     the GCM `gcm_ctr_inc`/`inc32` can share any helper (they likely cannot — XTS advances by
     GF multiply, GCM by inc32 — but document the decision so nobody re-investigates).
- Files: `common/gcm.ml` (consume), the utils files, both proof families.
- AC: zero `copied from PR#389` blocks remain; a single canonical increment story documented;
  every `@UPSTREAM-389` item either filed upstream or explicitly declined with a reason.
- Depends on: Tasks 4, 6, PR389 merge.

## Sequencing / critical path

```
Task 0 ─► Task 1 ─► Task 2
                 └► Task 3 ─► Task 4 ─► Task 5 ─► Task 6 (enc 2blk) ─► Task 6b (enc 1blk)
                 │                                          └► Task 6c (DEC 1+2 blk) ─► Task 8
                 └► Task 7 (GHASH list) ──────────────────────────────────────────────┘
                                                              Task 9 (after Task 8 & PR389 merge)
```
Encrypt first, then decrypt: Tasks 6/6b land the machinery on enc (2- then 1-block); Task 6c
carries the SAME shared spec/utils to dec (1- then 2-block, the latter newly written); Task 8
scales both directions to 4/8.

Minimum viable first milestone: **Tasks 0,1,3,4,5,6** = the 2-block ENC proof re-stated with a
recursive CTR postcond and a composable counter iterator. That alone proves the machinery and
removes the per-block enumeration. Then **6b** (enc 1-block) and **6c** (decrypt 1+2 block) are
re-use passes on the same machinery; 4/8-block (Task 8) and the GHASH-list spec (Task 7) are
the larger follow-ons.

## Risks / open questions

- **R1.** Whether `bytes(out_p,16N)` ⇔ per-block `bytes128` already exists as an XTS/base lemma
  (avoid reinventing in Task 5). Check `arm/proofs/base.ml` / `aes_xts_encrypt.ml` first.
- **R2.** `inc32` vs `gcm_ctr_inc` byte-order: confirm the exact conjugation (Task 2) on paper
  before coding — getting the endianness wrong makes the bridge unprovable.
- **R3.** Recursion-existence boilerplate (`prove_general_recursive_function_exists` + WF
  measure) is fiddly; copy the XTS `eth`/`wfth`/`exists_lemma` pattern verbatim.
- **R4.** 8-block control flow (`Loop_mod2x_v8`) is a separate simulation problem from the spec
  generalization; keep Task 8's spec work decoupled from the trn1/trn2 stepping.
- **R5.** Coordinating with Mila's upstream: prefer porting her lemma NAMES verbatim so a future
  merge is a no-op, and cite the permalink in each ported lemma's comment.

## Upstream contributions to PR #389 (the running list)

Anything tagged `@UPSTREAM-389` in source must appear here. Task 9 files each one upstream (or
records why not). PR #389 = `awslabs/s2n-bignum#389`, `sgmenda:gcm-spec`, NIST SP 800-38D spec.

| Candidate | Where it'll live in our tree | Why it's spec-level (upstream-worthy) | Disposition |
|-----------|------------------------------|----------------------------------------|-------------|
| `gctr256` (or cipher-generic `gctr`) | `arm/proofs/utils/aes_ctr_spec.ml` (Task 4) | PR389's `gctr` is AES-128-only; AES-256 counter mode is a genuine spec gap, reusable beyond our proof. **Strongest candidate.** | propose to #389 / follow-up |
| `AES_CTR_EQ_GCTR` | `aes_ctr_spec.ml` (Task 4) | equivalence of the recursive CTR spec to the NIST `gctr` — spec-adjacent | propose with `gctr256` |
| `INC32_GCM_CTR_INC` | `gcm_ctr_helpers.ml` (Task 2) | bridges NIST `inc32` to the ARM-binary counter `gcm_ctr_inc` | `@UPSTREAM-389?` — authors decide; likely stays in utils with a pointer |

NOT upstream (ARM-proof glue — reconcile the *binary's* lane layout with the spec, stay in
`arm/proofs/utils/`): `gcm_ctr_inc`, `gcm_ctr_inc_iter`, the LANE/CTR_WORD_INSERT/INSERT_* fold
lemmas, the `GCM_NBLOCK_*` step tactics, the `bytes(ptr,len)`⇔per-block bridge. (Many of these
originate in Mila's dev branch; coordinate THOSE with her, not with #389 — see R5.)

Two upstreams to keep distinct: **#389** = the cipher-agnostic NIST spec layer; **Mila's dev
branch** = the ARM N-block proof machinery. Spec-level additions go to #389; proof machinery
coordinates with Mila.
