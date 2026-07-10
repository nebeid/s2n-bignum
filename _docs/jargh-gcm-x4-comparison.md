# John Harrison's AES-128-GCM x4 proof vs our decrypt bands vs Mila's encrypt tail

Date: 2026-07-10.  Sources compared:

| effort | repo/branch (tip) | binary | proof target |
|---|---|---|---|
| **JRH** | `jargh/s2n-bignum-dev` branch `gcm` (c491a04c, 2026-07-10) | `arm/aes_gcm/aes_gcm_enc_kernel_x4_basic.S` — Hanno Becker's "clean" (non-interleaved, SLOTHY-input) AES-128-GCM, 4x unrolled | **encrypt**, ANY whole-block length (two genuine loops) |
| **ours** | this repo, branch `aes-gcm-nblock-tail` (9e534058) | `arm/aes-gcm/aesv8_gcm_8x_dec_256.o` — aws-lc `aesv8-gcm-armv8-unroll8.S`, production 8x interleaved | **decrypt**, tail path ≤128B (bands le1..le8, straight-line after cascade) |
| **Mila** | `mila/aes256_gcm_tail` (14154e49, 2026-06-30) | `arm/aes-gcm/aes256_gcm.S` — her own clean AES-256-GCM binary | **encrypt**, ≤128B dispatch (LT_0..LT_8BLOCK_CONCRETE) |
| shared | `common/polyval_ghash.ml` is **byte-identical** in all three lineages; JRH's `common/ghash_nist_bridge.ml` is byte-identical to Mila's | | |

Local copies of JRH's key files: `_docs/jargh_gcm/` (proof, .S, ghash_nist_bridge, his
polyval_ghash — diffed identical to ours).

The headline: JRH proved, in ~10 days (proof skeleton 2026-07-01 → subroutine theorem
2026-07-08 → six more variants by 2026-07-10), a **length-generic two-loop** theorem for a
*clean* 4x kernel, using the classical `ENSURES_WHILE_UP_TAC` loop-invariant discipline —
the piece neither we nor Mila have (our main-loop/whole-binary composition is still open;
her dispatch covers only ≤8 blocks).  Conversely, his binary is the *easy* direction:
readability-oriented, no instruction interleaving, no partial-block masking (whole blocks
only, `len_bits` a multiple of 128), AES-128 not 256.  The three efforts are largely
complementary, and his `nist_ghash` + `GHASH_POLYVAL_ACC_BATCHED` layer plugs directly
into the algebra we already share.

---

## 1. Specification layer

### 1.1 JRH's specs (the most abstract of the three)

Defined *in the proof file* (`aes_gcm_enc_kernel_x4_basic.ml`) on top of two common files:

```
ctr_block nonce ctr        = word_join (nonce:96 word) (word ctr:int32)      (NIST big-endian view)
aes_ctr_block nonce rk i   = word_reversefields 8 (aes128_cipher (ctr_block nonce (i+2)) rk)
cipher_block ... i         = word_xor (aes_ctr_block nonce rk i) (inblock i) (little-endian, what's stored)
nist_cipher_block ... i    = word_reversefields 8 (cipher_block ...)         (NIST view of same)
```

and in `common/ghash_nist_bridge.ml` (this file is ALREADY in Mila's tree, byte-identical):

```
nist_dot a b   = bit_reflect128(ghash_reduce(word_pmul (bit_reflect128 a) (bit_reflect128 b)))
nist_ghash h acc []          = acc
nist_ghash h acc (CONS x xs) = nist_ghash h (nist_dot (word_xor acc x) h) xs
NIST_GHASH_IS_POLYVAL: nist_ghash h acc xs = ghash_polyval_acc (ghash_twist h) acc xs
```

**Key observations.**
- His top-level postcondition speaks **NIST SP 800-38D language**: the tag is
  `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_cipher_block ...) nblocks)`
  — the GHASH key is literally E_K(0) and the dot is the *standard* bit-reflected GF(2^128)
  multiply.  `ghash_twist`/`ghash_polyval_acc` (the Gueron POLYVAL trick we all prove
  against) appears only *inside* the proof via `NIST_GHASH_IS_POLYVAL`.  This is one level
  more abstract than both our `ghash_polyval_acc (byteswap128 h) ...` postcondition and
  Mila's `gcm_final_xi` — ours/hers still mention the twisted key; his mentions only the
  NIST objects.  **This is the end-state spec vocabulary to converge on.**
- Round keys enter as an abstract `rk:int128 list` with
  `wordlist_from_memory(key_p,11) s = MAP (word_reversefields 8) rk` — one line, versus our
  15 explicit k0..k14 quantified variables (and Mila's rk0..rk14).  Same for the input:
  `!i. i < nblocks ==> read (bytes128 (in_p + 16i)) s = inblock i` with `inblock:num->int128`
  a function — length-generic where our `cph0..cph7` and her `co0..co7`/`pt_in` byte list
  are fixed-width.
- Htable precondition is packaged as a predicate `htable_mem_4 h ptr s` (6 entries:
  byteswap128(h_power h 0..3) + the two packed `karatsuba_mid` words).  Same content as
  Mila's inline h/h1k/h2... equations and our htable reads + byteswap hypotheses, but
  named, reusable, and stated via `h_power` instead of nested `polyval_dot` towers.
- AES spec is FIPS-197 (`common/fips197.ml`, `aes128_cipher`) with an explicit
  reconstruction theorem `AES128_CIPHER_RECONSTRUCT` proving the machine's
  aese/aesmc tower = `word_reversefields 8 (aes128_cipher (rev8 pt) (MAP rev8 rk))` —
  the analog of our `aes256_encrypt` + `EL_15_128_CLAUSES` unfold and of Mila's
  `AES256_ENCRYPT_UNFOLD`, but done ONCE as an equation instead of re-unfolding the
  14-round tower at every capture site (see §3.3).

### 1.2 Ours

Two-layer per band: literal per-block `..._BODY` + readable `byte_list_at` wrapper over
the recursive whole-buffer spec (`gcm_dec_pt_bytes` / `gcm_dec_final_xi`,
`arm/proofs/utils/aes_gcm_dec_spec.ml`).  GHASH postcondition:
`ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) [brev cph0; ...; brev cphm]`.
Handles the **masked partial tail block** (mask `2^(8*bl1)-1`) — a dimension JRH's
whole-blocks-only spec doesn't have at all.  Key packaged as 15 explicit variables;
htable as explicit reads + `byteswap128 hN = polyval_dot ...` hypotheses.

### 1.3 Mila's

3-layer XTS style: `AES256_GCM_ENCRYPT_CORRECT` (val len ≤ 128, ASM_CASES dispatch at
16/32/.../112) → per-size `LT_{0..8}BLOCK_CONCRETE`.  Spec vocab: `byte_list_at` in/out,
`aes256_gcm_encrypt` byte-list function, `gcm_final_xi` for the tag, `word_swaphalves128`
htable equations + `karatsuba_mid` hk-constraints (JRH uses the same `karatsuba_mid` from
the shared `polyval_ghash.ml`).  Like ours she has the masked partial block; like ours
her key/htable are explicit per-slot equations.

### 1.4 Spec-layer verdict

| dimension | JRH | ours | Mila |
|---|---|---|---|
| tag spec | `nist_ghash` (NIST-native, key = E_K(0)) | `ghash_polyval_acc` + byteswapped key | `gcm_final_xi` (≅ ghash_polyval_acc wrapper) |
| length | generic `len_bits` (whole blocks) | per-band ≤128B incl. partial byte | dispatch ≤128B incl. partial byte |
| input/keys | function + `wordlist_from_memory`/MAP | explicit vars | explicit vars + byte list |
| htable | named predicate `htable_mem_4`, `h_power` | inline reads + polyval_dot towers | inline reads + polyval_dot towers |
| partial blocks | **none** | yes (masked band) | yes (masked band) |

Adopting his `nist_ghash` postcondition + `htable_mem_N` packaging + list/function-style
inputs is the natural STEP-D-era convergence for us and Mila: `NIST_GHASH_IS_POLYVAL` is
a one-line rewrite from what we already prove, and `ghash_nist_bridge.ml` is already
byte-identical in Mila's tree.

---

## 2. Lemma layer

Because `common/polyval_ghash.ml` is byte-identical across all three, the deep algebra is
literally shared: `polyval_dot`, `polyval_reduce_prop3`, `h_power`, `ghash_wide`,
`GHASH_POLYVAL_ACC_BATCHED` (his batched N-block theorem = the ancestor of Mila's
`GHASH_NBLOCK_KARATSUBA_EQ_PROP3` and of our `GHASH_POLYVAL_ACC_N`/`build_GMULTn_fast`
routes), `karatsuba_mid`, `ghash_twist`, `PMUL_KARATSUBA`.

What differs is the **machine-shape bridge** — how each proof gets from the register-level
pmull/eor soup to that algebra:

- **JRH**: two purpose-built equations shaped exactly like the code.
  - `polyval_reduce_g2 p1 p2 p3` — a `new_definition` capturing the kernel's reduction
    instruction sequence verbatim (the two W-pmuls, the ext-swap, the joins), with
    `RECONSTRUCT_POLYVAL_REDUCE_G2 = GSYM` used as a *recognition rewrite* on the
    simulated state, plus `POLYVAL_REDUCE_G2` proving it equal to
    `polyval_reduce_prop3 (word_join ...)`.  So: name the machine pattern, recognize it
    by rewriting, then swap it for the spec reduction — one BITBLAST at definition time.
  - `PMUL_KARATSUBA_JOIN(_ALT)` — Karatsuba restated with the result as an explicit
    4-limb `word_join` tree (and the ALT form with the XOR argument order the code uses).
  - The per-4-block close is then: recognize g2, `PMUL_KARATSUBA_JOIN_ALT`,
    one `TRANS_TAC EQ_TRANS` to the explicit
    `prop3(pmul cb3 h0 ⊕ pmul cb2 h1 ⊕ pmul cb1 h2 ⊕ pmul (sofar⊕cb0) h3)` middle form,
    close the left leg with one final `BITBLAST_TAC` (assumption-free: `POP_ASSUM_LIST(K
    ALL_TAC)` first), and the right leg with `GHASH_POLYVAL_ACC_BATCHED` +
    `NIST_GHASH_IS_POLYVAL` + `GHASH_ACC_APPEND` list algebra.
- **ours**: `build_GMULTn_fast n` emits `GMULTn_FULL_CORRECT_BA` per band;
  `DEC_BRIDGE_CLOSE_TAC nblk sN ...` (STEP B) does spec_eq → `ABBREV_INNER_PMULS` →
  `MERGE_2BLK` → multiplier-keyed `FOLD_MID_HPOW` per h-power → WA/WV unify →
  `QQ0SPLIT`/lane-split → per-lane `bubble_fix` canonicalization + WORD_BLAST.
  More moving parts because the aws-lc binary's value graph is messier (interleaving,
  the k13 ins-carry, the carried Q18 midacc in whole-8) — but note JRH's *recognize-the-
  reduction-as-a-named-definition* trick is exactly the family of "reduction-as-rewrite"
  close Mila pioneered and we adopted for the 1-block; his version is more systematic.
- **Mila**: `ghash_Nblock_karatsuba` per size + `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` proved
  once generically (kara_acc/kara_quad machinery), instantiated per N in the eight
  `gcm_{one..eight}_block_closers.ml`; per-block ct equalities closed by the
  parameterized `GCM_NBLOCK_CT_STEP_TAC n k` generators.

All three converge on the same idea from different ends: **prove the hard GF(2^128)
algebra once, then make the per-size/per-shape close a small recognition step.**  JRH's is
the smallest lemma inventory (2 machine-shape lemmas + 1 batched theorem) because his
binary has only ONE GHASH pattern repeated; we and Mila carry per-N artifacts because the
tail cascade produces N distinct shapes.

---

## 3. Symbolic simulation & proof structure

### 3.1 The big structural difference: real loops

JRH's is the only one of the three with genuine loop invariants:

```
ENSURES_SEQUENCE_TAC (pc+0x8c)   -- init: 24 steps, registers/counters set up
ENSURES_WHILE_UP_TAC loop_count (pc+0x90) (pc+0x2f0)  -- 4x unrolled main loop
    invariant: X0/X2 advanced by 64i; Q31 = rev32(ctr_block nonce (4i+2));
               Q11 = byteswap128(nist_ghash ... (list_of_seq ... (4i)));
               out[j] written for j < 4i;  in[] untouched;  htable_mem_4; keys in Q18..Q28
    body: 152 straight-line steps (4 AES towers + 4 GHASH accumulations + reduction)
ENSURES_SEQUENCE_TAC (pc+0x2f4)  -- between loops
ENSURES_WHILE_UP_TAC loop_remain (pc+0x304) (pc+0x3b4) -- 1x tail loop, 44-step body
final: 6-9 steps writeback (rev64 tag, rev32 counter, str)
```

This is textbook s2n-bignum loop discipline (same as bignum proofs): the induction is over
`list_of_seq ... (4i)`, extended each iteration via `GHASH_ACC_APPEND`/`NIST_GHASH_APPEND`
list lemmas.  Trivial-case splits (`loop_count = 0`, `loop_remain = 0`) handled by
`ASM_CASES_TAC` + 1-step `ARM_SIM_TAC`.  The subroutine wrapper is the stock
`ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(11,11) ... 160` — the exact wrapper the
C_ARGUMENTS memory notes flagged as "deferred" for our chain.

We and Mila, by contrast, simulate **straight-line unrolled paths** (the ≤128B tail never
loops): our bands step 1→~420 through the branch cascade with per-band resolver rungs;
Mila's CONCRETEs likewise per size.  That's forced by scope (the ≤128B tail IS
straight-line) — but the missing piece for our whole-binary goal (bit_len > 128, the
`Loop_mod2x` main loop) is precisely the discipline JRH's proof demonstrates.  **His
x4_basic proof is the best available template for our future dec main-loop proof**: the
invariant shape (pointer advance, counter as function of i, tag as fold over
list_of_seq, output cells for j < ki, untouched input array) transfers directly.

### 3.2 Stepping style

- JRH steps with plain `ARM_STEPS_TAC ... [n]` + per-step
  `RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))` — one uniform
  normalizer, no discard machinery, no SIMD-fold pass.  He can afford this because the
  loop body is only 152 steps and the invariant fixes ~25 named registers, so the
  assumption pile stays small (the ENSURES_WHILE framing throws away everything else at
  each loop boundary — the loop invariant IS the discard mechanism).
- We needed the whole per-step-discard stepper family
  (`ARM_STEPS_FOLD_DISCARD/RESOLVE_SIMD_DISCARD/KEEPGH/KEEPQ18`) + `GCM_SIMD_SIMPLIFY_TAC`
  because our windows are 300-420 steps of *one* ensures goal with byte-tree REV64 bloat
  and O(n²) assumption rescans (memory: dec-band stepping optimization).
- Mila's `GCM_ENC_SIMPLIFY_TAC` / `GCM_NBLOCK_POST_SIM_NORMALIZE_TAC` sits in between:
  per-step rewrite cleanup like JRH (incl. WORD_SIMPLE_SUBWORD_CONV) plus her
  SIMD_SIMPLIFY rules, no aggressive discards.

Lesson in both directions: JRH's "invariant-as-discard" only works with loops; for
straight-line tails our discard steppers remain necessary.  But his single uniform
`WORD_SIMPLE_SUBWORD_CONV` normalizer applied to *every* step is notably simpler than our
window-specific choreography, and worth trying as the default in any new front.

### 3.3 AES tower handling

JRH proves `AES128_CIPHER_RECONSTRUCT` (and the XOR-folded variant) ONCE — the machine's
aese/aesmc chain collapses to the FIPS `aes128_cipher` by rewriting; block captures in the
loop body are then `REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT]`.  We re-unfold
`aes256_encrypt` + `EL_15_128_CLAUSES` + `let_CONV` + `WORD_BLAST` at every pt_k capture
(8-10 times per band); Mila's `AES256_ENCRYPT_UNFOLD` is similar to ours.  His approach is
strictly better: one definitional-equality lemma, then captures are pure rewriting.
**Back-portable to our bands today** (an `AES256_ENCRYPT_RECONSTRUCT` in core.ml would
replace every `REWRITE_TAC[aes256_encrypt] ... CONV_TAC WORD_BLAST` capture block and
should also shave load time).

### 3.4 Variant scaling

His 7 proved variants (basic, dual_acc, ilp, late_tag, keep_htable,
dual_acc_keep_htable, scalar_iv) reuse the x4_basic proof with only machine-code literal +
PC constants + step counts changed (~585 diff lines vs basic for ilp, mostly the mc
literal).  That's the same "one recognizable pattern, re-instantiated" philosophy as our
STEP A-C generators and Mila's closers — at the granularity of whole proofs, enabled by
the variants sharing one control-flow skeleton.  16 more variants imported but not yet
proved (fast_tail, scalar_iv_mem*, rotate, reload_round_keys...).

---

## 4. What each effort has that the others lack

| capability | JRH | ours | Mila |
|---|---|---|---|
| genuine loop invariants / length-generic | **yes** | no (tail only) | no (≤8 blocks) |
| subroutine-level wrapper (stack lift, ret) | **yes** | deferred | no (CONCRETE-level, dual exit PC) |
| NIST-native spec (`nist_ghash`, E_K(0) key) | **yes** | polyval form | polyval form (`gcm_final_xi`) |
| partial-block masked tail (any byte length) | no | **yes** | **yes** |
| AES-256 | no (128) | **yes** | **yes** |
| production interleaved binary (aws-lc unroll8) | no (clean kernel) | **yes** | no (own clean binary) |
| decrypt direction | no | **yes** | no |
| htable as named predicate | **yes** | inline | inline |
| abstract key/input lists in spec | **yes** | explicit vars | explicit vars |
| axiom check | check_axioms clean | axioms()=3, hyps=0 | (her branch, assumed clean) |

The "production vs clean binary" row is the crux: JRH + Mila verify readable kernels
(Becker's SLOTHY-input family; her own aes256_gcm.S) that would *replace* the aws-lc
assembly; we verify the exact shipping aws-lc code.  These are different theories of
change — if AWS swaps in SLOTHY-optimized verified kernels, JRH's family wins and the
partial-block/AES-256/decrypt gaps (his missing rows) become the work items; if the
shipping binary must be verified as-is, our band machinery is the only game for the tail
and needs his loop discipline for the rest.

---

## 5. Concrete take-aways for our branch

1. **Main-loop template (biggest).**  When we attack `Loop_mod2x`/whole-binary dec, copy
   the x4_basic skeleton: ENSURES_SEQUENCE to loop entry; ENSURES_WHILE_UP with the
   invariant quadruple (advanced pointers, counter = f(i), tag = nist_ghash of
   list_of_seq prefix, out cells j < ki); trivial-count ASM_CASES; APPEND list lemmas for
   the invariant extension; ARM_ADD_RETURN_STACK_TAC wrapper at the end.  His GHASH
   invariant `Q11 = byteswap128(nist_ghash ...)` also settles the accumulator-register
   convention question our le8 midacc capture danced around.
2. **`AES256_ENCRYPT_RECONSTRUCT` now.**  Port `AES128_CIPHER_RECONSTRUCT` to our 14-round
   tower in core.ml; replaces ~50 lines of repeated unfold-blast per band and likely
   measurable load time.  Low risk, pure addition.
3. **Spec convergence target = his, not just Mila's.**  STEP D's D2/D4 discussion should
   aim at `nist_ghash`/`nist_cipher_block`-style postconditions (via the already-shared
   `ghash_nist_bridge.ml` — add it to our tree) with `htable_mem_N` predicates and
   list/function inputs.  Ours and Mila's polyval-form statements become internal lemmas.
4. **Adopt `h_power` in htable hypotheses** instead of nested `polyval_dot` towers
   (cosmetic but kills the h2..h8 tower noise in every band statement).
5. **His `polyval_reduce_g2` recognition trick** is the cleanest formulation of the
   "reduction-as-rewrite" close; if we ever refight a bridge, name the machine reduction
   pattern as a definition and recognize it with GSYM, rather than folding mids piecemeal.
6. **What we should tell them:** the masked-partial-block band technique (symbolic-bl
   mask, MASK_LEMMA/BLEND_OR_XOR, byte_list_at weakening) is what their family needs for
   the `len_bits` not-multiple-of-128 case (their kernels currently spec whole blocks
   only), and our aws-lc-binary work covers the interleaved-production-code case SLOTHY
   variants sidestep.  Also the fast_tail variants (unproved as of c491a04c) will need
   cascade-resolver machinery like our `dec_blN_resolve` rungs.

---

## 6. File-level pointers

- JRH proof (local copy): `_docs/jargh_gcm/aes_gcm_enc_kernel_x4_basic.ml`
  (1320 lines: mc literal ≈ 260, specs+lemmas ≈ 420, core proof ≈ 530, wrapper ≈ 70).
  Loop-body invariant close: lines ~940-1060; tail-loop close: ~1150-1230.
- His .S: `_docs/jargh_gcm/aes_gcm_enc_kernel_x4_basic.S` (563 lines, macro-structured:
  `aes_full_block`/`ghash_block_x4`/`prepare_loop_counts` macros, Becker provenance note).
- `ghash_nist_bridge.ml` local copy in `_docs/jargh_gcm/` — candidate to `needs` from our
  chain (it is downstream of `polyval_ghash.ml` which we already share).
- Mila comparison references: memory `project_ghash_approach_vs_mila`,
  `_docs/gcm-spec-divergence-from-mila-handback.md`,
  `_docs/dec-band-homogenization-convergence-plan.md` §2.
