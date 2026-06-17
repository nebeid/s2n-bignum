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
- a spec variable `ctr1:int128` pinned by a precond to the lane-level once-incremented `ctr0`
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

## 4. The block-1 counter `ctr1` (the genuinely new modeling, + the gotcha)

Block 1's AES input is the lane-level once-incremented `ctr0`: rev32 of the byte-shuffled top
32-bit lane + 1. We expose it as a **spec variable `ctr1:int128`** pinned by a precond
`ctr1 = <lane-shuffle of ctr0>`. This keeps the postcond readable and lets `ct1` stay opaque
through the bridge.

**TYPE-INFERENCE GOTCHA (the single biggest time sink — write this down).**
The lane-shuffle is a tower of `word_join`, and `word_join : (M)word->(N)word->(P)word` has its
OUTPUT width `P` as an INDEPENDENT type variable — HOL cannot infer it from the operands (join
of two 8-bit words could be any width ≥ 16). A bare term leaves free type variables in the
goal, and then **`GEN_TAC`/`STRIP_TAC` silently no-op** (the goal is an open polymorphic prop,
not a closed proposition) — the front tactic appears to "not run" with no error message.

FIX: the pinning term must be **fully type-annotated** — every `word_join`/`word_subword`/
`word_add`/`word` literal carries an explicit `(n)word`. Generate it by building the term
programmatically with concrete widths (`mk_finty(num n)` for the index type `:n`, and
`width = wa+wb` for each join), then printing with `print_types_of_subterms := 2`. The
annotations are absorbed during type-checking; the displayed/stored term is clean.
**Sanity check after any spec edit:** `e GEN_TAC` must actually strip a quantifier — if the
goal is unchanged, you still have free type variables.

`ct1` is then abbreviated to `word_xor plaintext1 (aes256_encrypt ctr1 keys)` with the SAME
MESON-SPEC idiom as ct0, except the ANTS first folds `ctr1 → <lane-shuffle>` via the precond
(`GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ctr1_precond]`) so the spec form matches the
Q9 readback before expanding `aes256_encrypt`.

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
(* fold the postcond's literal CTR1 back to the spec var ctr1, so block-1/xi_p match ct1's def *)
FIRST_ASSUM(GSYM ctr1_precond) THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
TRY(MAYCHANGE close THEN NO_TAC) THEN
TRY(block-0: GSYM ct0-def THEN expand aes256_encrypt to the raw aese tower)
```
- **block-1** and **xi_p** fall out by pure ASM_REWRITE once CTR1 is folded to `ctr1` (then the
  ct1 store readback and ct1's spec-form def match).
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
| Bridge (3 merge rounds + FINISH) | ~100s (most of it the one wv blast) |
| ext+rev64 + store + close | ~30s |
| **Full `loadt` (deps cached)** | **~385s** |
| **Full `loadt` from cold (incl. 1-block dep)** | **~17 min** |

---

## 7. Lessons (new at 2 blocks)

1. **Targeted merge by structural signature, not all-pairs.** When the post-Karatsuba goal has
   N matched LHS/RHS pmul atoms, pair them by a cheap signature (free vars + lane + key) and
   blast only matched pairs; never trial-blast non-matches (each failed big-operand
   `WORD_BLAST` is ~90s). Propagate each merge eq into the hyps so dependent atoms update.
2. **`WORD_BITWISE_TAC`, not `WORD_BLAST`, for the final flat-XOR lane identity.** Once the goal
   is a pure XOR identity over 64-bit vars (no subword/join/shift/pmul), `WORD_BITWISE_TAC`
   closes each lane in <1s; BDD-blasting the same goal times out >16 min.
3. **Model a literal bit-shuffle counter as a precond-pinned spec VARIABLE** — readable
   postcond, opaque through the bridge — **but fully type-annotate the pinning term**, because
   `word_join`/`word_subword` widths do not propagate through type inference and free type
   variables silently no-op `GEN_TAC`/`STRIP_TAC`.
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
| counter | ctr0 only | + ctr1 (precond-pinned spec var, lane-incremented) |
| bridge merge | `MERGE_PMUL_ATOMS_TAC` (≈3 atoms) | `MERGE_2BLK_TAC` (≈8 atoms, signature-targeted) |
| flat close | manual r1/u/r2 lane-fold | `FINISH_2BLK_TAC` (`ABBREV_ALL_SUBWORDS` + `WORD_BITWISE_TAC`) |
| postcond | out_p + xi_p | out_p (2 blocks) + xi_p |

The 2-block is a faithful extension, not a re-derivation: the front, the ciphertext spec-form
idiom, the key convention, and the Prop3/Karatsuba primitives are all inherited; the new work
is the 2-product bridge, the targeted merge, and the ctr1 modeling.
