# AES-GCM 8x encrypt 256, 2-block: proof methodology, timing, lessons

**Status (2026-06-17): PROVED end-to-end, no CHEAT_TAC / new_axiom / mk_thm, 3 standard axioms.**
Theorem: `AESV8_GCM_8X_ENC_256_2BLOCK` in `arm/proofs/aesv8_gcm_8x_enc_256_2block.ml`.
Proves the full postcondition (both ciphertext blocks at `out_p`, and the GHASH tag at
`xi_p`) for the genuine `bit_len = 256` path through the real `aesv8_gcm_8x_enc_256` binary
(not an extracted subset). Direct `C_ARGUMENTS` entry at pc+0x18, exit pc+0x11d8.

This doc is written as a **diff against the 1-block methodology**
(`_docs/aesv8-gcm-8x-enc-256-1block-methodology-20260603.md`): it records only what is new
or different at two blocks, and points back to the 1-block doc for everything shared.

It supersedes the running session notes in `_docs/2block_handoff/` (BRIDGE.md, README.md,
q19_s361_reduced.txt), which are kept as the historical development log.

---

## 0. What's shared with the 1-block proof (read that doc for these)

- The front AES-rounds stepping style (small `ARM_STEPS_TAC` batches + discard, the GHASH-tag
  `GCM_SIMD_SIMPLIFY_TAC` fold, the `INT_SUB_REFL` branch resolution).
- The ciphertext spec-form abbreviation idiom (the `FIRST_X_ASSUM(MP_TAC o SPEC .. o MATCH_MP
  (MESON[] ...))` + unfold-`aes256_encrypt` close) — used here for **both** ct0 and ct1.
- The GHASH key convention `byteswap128 h` and the htable lane-exchange reasoning (§6/§6b of
  the 1-block doc). The 2-block adds one more htable slot (H^2) but the key convention is the
  same.
- The bridge machinery primitives: `PMUL_KARATSUBA`, `KARATSUBA_LIMBS`, `byteswap128`,
  `WORD_BYTEREVERSE_REVERSEFIELDS`, `WORD_INSERT_SUBWORD`, `ABBREV_INNER_PMULS_TAC`,
  `polyval_reduce_prop3`.
- The double-fold `GCM_SIMD_SIMPLIFY_TAC` REV64-bloat fix (§3 of the 1-block doc).

---

## 1. The theorem (what is proved)

Precondition adds, over the 1-block:
- two plaintext blocks at `in_p`, `in_p+16`; `bit_len = 256`; `out_p` region 32 bytes.
- one extra htable slot `h2 = read (htbl_p+32)` with the invariant
  `byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)` (i.e. h2 = byteswap128(H^2)).
- the packed-mid precond now has TWO lanes:
  `subword hk (0,64) = mid(h)` [block-1/H], `subword hk (64,64) = mid(h2)` [block-0/H^2].
- a spec variable `ctr1:int128` pinned by the precond `ctr1 = gcm_ctr_inc ctr0` (the lane-level once-incremented `ctr0`)
  (see §4 — this is the genuinely new modeling step).

Postcondition (full):
```
read (memory :> bytes128 out_p) s        = word_xor plaintext0 (aes256_encrypt ctr0 keys)
read (memory :> bytes128 (out_p+16)) s   = word_xor plaintext1 (aes256_encrypt ctr1 keys)
read (memory :> bytes128 xi_p) s         =
   word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                       [word_bytereverse ct0; word_bytereverse ct1])
```
MAYCHANGE frame: `bytes(out_p,32), bytes(xi_p,16), bytes(ivec_p,16), bytes(sp+64,16)`.

---

## 2. Control flow: which path 2 blocks actually takes (NOT Loop_mod2x)

`byte_len = 32` ⇒ at pc+0x163 `x0 >= x5` ⇒ branch to `.L256_enc_tail` (NOT the 8-way
main_loop). In the tail, `x5 = 32`: the `cmp x5,#112/.../#16; b.gt` cascade falls through
all but the last, taking `.L256_enc_blocks_more_than_1` (32 > 16) for block 0, then falling
into `less_than_1` for block 1. So **2 blocks = more_than_1 (block 0, GHASH vs H^2) +
less_than_1 (block 1, GHASH vs H, single Prop3 reduction folding both blocks)**.

This is the FAVORABLE path: the feared `Loop_mod2x_v8` (trn1/trn2 interleave) is only reached
at ≥ ~6 blocks; 2 blocks avoids it entirely, and the cascade's htable-loaded Karatsuba mids
match `GHASH_POLYVAL_ACC_2`'s shape directly.

PCs (objdump of the .o): more_than_1 0x10f4–0x1134 (block-0 GHASH; ldr q22,[x6,#32]=H^2),
less_than_1 0x1138–0x11d4 (block-1 GHASH + accumulate + reduce + ext/rev64 + store @ 0x11d4).

Front recipe is mechanically the 1-block recipe with two differences:
- **keep Q1 and Q7 alive** (block-1 keystream; the cascade's `mov v7,v1` routes it). The
  1-block discards Q1–Q7; here use a discard that keeps Q0,Q1 (and Q7 from the tail entry).
- **keep Q30 through the CTR setup** (steps ~6–30, fold each `add v30.4s` with
  `GCM_SIMD_SIMPLIFY_TAC`), because block 1's counter is the increment of block 0's.

---

## 3. The 2-product GHASH bridge (the algebraic core)

Goal at s367 (pc+0x11cc), the ~18.4k-char reduced Karatsuba+Prop3 byte-form in Q19:
```
read Q19 s367 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                  [word_bytereverse ct0; word_bytereverse ct1]
```
Opened via `GHASH_POLYVAL_ACC_2` (already in `common/polyval_ghash.ml`):
```
ghash_polyval_acc h a [b;c] =
  prop3(pmul(a XOR b, polyval_dot h h) XOR pmul(c, h))
```
so the spec's `polyval_dot K K` becomes `byteswap128 h2` via the htable invariant, matching
the assembly (block-0 vs H^2 from htbl+32, block-1 vs H from htbl+0, aggregated before one
reduction). Then `polyval_reduce_prop3` def + `PMUL_KARATSUBA` on **both** products +
`KARATSUBA_LIMBS` + subword normalization → opaque pmul atoms, three rounds of
`ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC`, then `FINISH_2BLK_TAC` (the lane-flatten:
`SUBW_*` collapse lemmas + `ABBREV_ALL_SUBWORDS_TAC` + `JOIN_EQ_SPLIT` + `WORD_BITWISE_TAC`
per lane — **`WORD_BITWISE_TAC`, NOT `WORD_BLAST`**; the latter times out >16 min on the same
flat-XOR identity).

### 3a. The merge — the performance-critical tactic (this is what made it tractable)

The naive all-pairs `MERGE_PMUL_ATOMS_TAC` is ~30 min here: each FAILED `PMUL_CONG_128`
`WORD_BLAST` on the big W-reduction operands costs ~90s, and it tries all pairs.
`MERGE_ONE_2BLK_TAC` instead picks **exactly one structurally-determined pair per call** and
blasts only it (REPEAT to a fixpoint). Two atom classes:

- **PRODUCT atoms** (operand 2 is a key-lane subword `h`/`h2`, or an xor of two such): the
  LHS (assembly) and RHS (spec) forms of the same GF product agree on the signature
  `(sorted non-key free-var names of operand 1, sorted free-var names of operand 2,
  operand-2's subword lane index)`. **Exclude k0..k14 from operand-1's free-var set** — the
  assembly's `ins` instruction leaves a spurious `k13` in one mid-term form that would
  otherwise split a genuine pair (this was the qq9/qq11 non-merge that stalled an earlier
  attempt).
- **W-REDUCTION atoms** (operand 2 = the same word-CONSTANT `0xC200...`): the `wa` and `wv`
  rounds differ structurally in operand 1 but multiply the same constant, so pair them by
  "operand 2 is the identical word-constant".

Merge equalities are propagated into the hypotheses (`RULE_ASSUM_TAC(REWRITE_RULE[th])`) —
essential because the `wv` atom's definition references the `wa` atom merged the round before.
Cost: ~3.6s + 3s (products) + ~92s (the one unavoidable big `wv` blast) + 2.8s (FINISH),
vs ~30 min. (`MERGE_2BLK_TAC` is the only tactic that changed vs. the structural skeleton; the
`3 × (ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC) THEN FINISH_2BLK_TAC` driver is unchanged.)

---

## 4. The block-1 counter `ctr1` (the genuinely new modeling)

Block 1's AES input is the lane-level once-incremented `ctr0`: rev32 of the byte-shuffled top
32-bit lane + 1. We expose it as a **spec variable `ctr1:int128`** pinned by the precond
`ctr1 = gcm_ctr_inc ctr0`, where

```
gcm_ctr_inc (ivec:128 word) =
  word_insert ivec (96,32)
    (word_bytereverse (word_add (word_bytereverse (word_subword ivec (96,32):32 word))
                                (word 1:32 word)))
```

is the clean rev32+ADD+rev32 increment, matching `gcm_ctr_inc` in manastasova's `s2n-bignum-dev`
(`aes256_gcm_whole` branch):
[arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml#L38](https://github.com/manastasova/s2n-bignum-dev/blob/756df852a0e42ac0229d7d67fb223b843d4afb49/arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml#L38).
This keeps the precond a one-liner and the postcond readable
(block-1 ciphertext = `word_xor plaintext1 (aes256_encrypt (gcm_ctr_inc ctr0) keys)`), and lets
`ct1` stay opaque through the bridge. A single bit-blasted bridge lemma connects it to the
explicit lane-byte form the simulator emits:

```
GCM_CTR_INC_LANES : gcm_ctr_inc ctr0 = <the 8-bit-subword word_join lane tower>   (BITBLAST, ~1s)
```

`ct1` is abbreviated to `word_xor plaintext1 (aes256_encrypt ctr1 keys)` with the SAME
MESON-SPEC idiom as ct0; the ANTS folds `ctr1 → gcm_ctr_inc ctr0` (the precond) then
`→ lane tower` (`GCM_CTR_INC_LANES`) so the spec form matches the Q9 keystream readback before
expanding `aes256_encrypt`.

**HISTORICAL GOTCHA (kept as a lesson; no longer hit now that `gcm_ctr_inc` is used).**
The first version pinned `ctr1` to the *literal* lane-shuffle (a bare tower of `word_join`).
`word_join : (M)word->(N)word->(P)word` has its OUTPUT width `P` as an INDEPENDENT type variable
— HOL cannot infer it from the operands (join of two 8-bit words could be any width ≥ 16). A
bare literal therefore left free type variables in the goal, and **`GEN_TAC`/`STRIP_TAC`
silently no-op** on an open polymorphic prop (the front tactic appears to "not run", no error).
The literal had to be fully type-annotated (every node `:(n)word`), generated programmatically
and printed with `print_types_of_subterms := 2`. Wrapping the shuffle in the typed constant
`gcm_ctr_inc` removes the problem entirely — its body is closed, so the precond is well-typed by
construction. **Lesson:** model a literal bit-shuffle of a wider word as a *named typed
function*, not a bare `word_join` literal; and after any spec edit, sanity-check that
`e GEN_TAC` actually strips a quantifier (if the goal is unchanged, free type variables remain).

---

## 5. Carrying the block-1 store readback, and the close

The block-1 store (`st1 v9,[x2]` @ 0x1188, x2 = out_p+16) happens in the s346–353 fold window
and is then dropped by `DISCARD_OLDSTATE`. **Capture it as a self-contained fact before
discarding** (same trick as the dec 1-block out_p carry):
```
SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 16))) s353 = ct1`
  ASSUME_TAC THENL [EXPAND_TAC "ct1" THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST; ALL_TAC]
```
(mask v0 is all-ones for x1=128, so the masked/bif stored value is exactly ct1). out_p+16 is
not written again, so this survives unchanged to s370.

Close (after the bridge, ext+rev64, the gval store):
```
ENSURES_FINAL_STATE_TAC THEN
(* fold ctr1 = gcm_ctr_inc ctr0 UNIFORMLY into goal AND the ct0/ct1 defs *)
FIRST_ASSUM(fun th -> if lhs(concl th) = `ctr1` then
              RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC) THEN
ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
TRY(MAYCHANGE close THEN NO_TAC) THEN
TRY(block-0: GSYM ct0-def THEN expand aes256_encrypt to the raw aese tower)
```
- The first step eliminates `ctr1` everywhere by rewriting it to `gcm_ctr_inc ctr0` in BOTH the
  goal and the ct0/ct1 spec-form def hypotheses. This is essential: the postcond's block-1
  clause reaches the final state as `aes256_encrypt (gcm_ctr_inc ctr0)`, so the ct1-def
  (`aes256_encrypt ctr1`) must be rewritten the same way or the two won't match.
  (Discarding the precond instead, or rewriting only the goal, leaves a residual
  `ct1 = aes256_encrypt (gcm_ctr_inc ctr0)` that can't close — a trap I hit; see the commit log.)
- **block-1** and **xi_p** then fall out by pure ASM_REWRITE (the ct1 store readback and the
  now-aligned spec-form def match).
- **block-0** is the only conjunct needing the aes256_encrypt expansion: its store predates the
  ct0 abbreviation, so the s370 readback is the RAW aese/aesmc tower; GSYM the ct0 def to get
  ct0 → spec form on the RHS, then `ONCE_REWRITE WORD_XOR_ASSOC; aes256_encrypt;
  EL_15_128_CLAUSES; aes256_encrypt_round; aese; aesmc; let_CONV; WORD_XOR_ASSOC`.
- **MAYCHANGE** via `MONOTONE_MAYCHANGE_TAC`.

---

## 6. Timing

| Phase | ~Time |
|-------|-------|
| 1-block dependency load (`needs`) | ~657s (one-time per session) |
| Front (prologue + AES + cascade to s367) | ~180s |
| Bridge (3 merge rounds + FINISH) | ~73s (was ~155s before the FAST_OPERAND_TAC merge speedup) |
| ext+rev64 + store + close | ~38s |
| **Full `loadt` (deps cached)** | **~290s** (was ~385s) |
| **Full `loadt` from cold (incl. 1-block dep)** | **~16 min** |

### Bridge merge speedup (the wv operand)
Profiling showed the bridge was dominated by ONE step: round-3's `wv` W-reduction merge,
whose operand equality closed by `CONV_TAC WORD_BLAST` in ~144s (the flattened operand alone
is ~93s of BDD blasting over ~6 opaque qq atoms). Both operands are the SAME GF product's
structural lane form (`word_zx`/`word_shl`/`word_subword` over the qq atoms, no `pmul`), so it
is really a flat XOR lane identity — exactly what `WORD_BITWISE_TAC` closes in <1s once the
256-bit Karatsuba lanes are collapsed to 64-bit. `FAST_OPERAND_TAC` does that collapse
(the `SUBW_*` lemmas + the new `SUBSUB_JOIN_DUP` for the duplicated mid-half `word_subword
(word_subword (word_join a a) (64,128)) (lo,64)`), abbreviates the residual atom-lanes, then
`WORD_BITWISE_TAC`. `MERGE_ONE_2BLK_TAC` now closes each operand with
`FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST`, dropping the wv merge from ~93s to ~1s and the
whole bridge from ~155s to ~73s. (Pure-XOR-identity ⇒ `WORD_BITWISE_TAC` not `WORD_BLAST` is
the same lesson as §7.2 / the FINISH close.)

---

## 7. Lessons (new at 2 blocks)

1. **Targeted merge by structural signature, not all-pairs.** When the post-Karatsuba goal has
   N matched LHS/RHS pmul atoms, pair them by a cheap signature (free vars + lane + key) and
   blast only matched pairs; never trial-blast non-matches (each failed big-operand
   `WORD_BLAST` is ~90s). Propagate each merge eq into the hyps so dependent atoms update.
2. **`WORD_BITWISE_TAC`, not `WORD_BLAST`, for the final flat-XOR lane identity.** Once the goal
   is a pure XOR identity over 64-bit vars (no subword/join/shift/pmul), `WORD_BITWISE_TAC`
   closes each lane in <1s; BDD-blasting the same goal times out >16 min.
3. **Model a literal bit-shuffle counter as a precond-pinned spec VARIABLE defined by a NAMED
   typed function** (here `ctr1 = gcm_ctr_inc ctr0`), not a bare `word_join` literal. The named
   function's body is closed so the precond is well-typed by construction (a bare `word_join`
   tower leaves free output-width type variables that silently no-op `GEN_TAC`/`STRIP_TAC`), and
   a single BITBLAST lemma (`GCM_CTR_INC_LANES`) bridges it to the simulator's lane-byte form.
   In the close, fold the precond UNIFORMLY into the goal and all spec-form defs (RULE_ASSUM +
   REWRITE) so the spec var is eliminated consistently — rewriting only the goal leaves a
   residual the defs can't match.
4. **Capture a store readback as a self-contained equality before `DISCARD_OLDSTATE`** if the
   stored region isn't written again — it then survives to the final state unchanged.
5. **Fold spec literals back to spec vars in the close** (GSYM the pinning precond) so the
   postcond matches the abbreviation defs under a single `ASM_REWRITE`.

---

## 8. How it compares to the 1-block proof

| | 1-block | 2-block |
|--|---------|---------|
| Path | `less_than_1` only | `more_than_1` (block 0) + `less_than_1` (block 1) |
| GHASH | 1 product, `GMULT_FULL_CORRECT_BA` | 2 products, `GHASH_POLYVAL_ACC_2` |
| htable | H + mid | H + H^2 + 2 mids (+ `byteswap128 h2 = polyval_dot K K` invariant) |
| counter | ctr0 only | + ctr1 = gcm_ctr_inc ctr0 (named typed increment fn) |
| bridge merge | `MERGE_PMUL_ATOMS_TAC` (≈3 atoms) | `MERGE_2BLK_TAC` (≈8 atoms, signature-targeted) |
| flat close | manual r1/u/r2 lane-fold | `FINISH_2BLK_TAC` (`ABBREV_ALL_SUBWORDS` + `WORD_BITWISE_TAC`) |
| postcond | out_p + xi_p | out_p (2 blocks) + xi_p |

The 2-block is a faithful extension, not a re-derivation: the front, the ciphertext spec-form
idiom, the key convention, and the Prop3/Karatsuba primitives are all inherited; the new work
is the 2-product bridge, the targeted merge, and the ctr1 modeling.
