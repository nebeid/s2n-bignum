# AES-GCM 8x encrypt 256, 1-block: proof methodology, timing, comparisons, lessons

**Status (2026-06-03): PROVED end-to-end, no CHEAT_TAC / new_axiom / mk_thm.**
Theorem: `AESV8_GCM_8X_ENC_256_1BLOCK` in `arm/proofs/aesv8_gcm_8x_enc_256_1block.ml`.
Proves BOTH the ciphertext (`out_p`) and GHASH tag (`xi_p`) postconditions for the 1-block
path through the real `aesv8_gcm_8x_enc_256` binary (not an extracted subset).

Companion: the **decrypt** counterpart is proved too — see
`_docs/aesv8-gcm-8x-dec-256-1block-methodology-20260611.md`, which is written as a diff
against this doc (what is shared vs. the five things that differ).

This doc supersedes the running notes in:
- `_docs/aesv8-gcm-8x-enc-256-1block-proof-plan.md` (the old plan — historical)
- `_docs/ghash-1block-session-handoff-20260602.md`, `ghash-vsteps-fix-findings-20260602.md`
- `_docs/ghash-drop-vsteps-step-and-simplify-plan.md`
- `_docs/ghash-1block-bridge-halfswap-findings-20260603.md` (the bridge discovery; the
  "lane-swap" sections there are OBSOLETE — see §6.)

It draws on (and verifies the relevant claims of) these earlier reference docs:
- `_docs/aes-gcm-ghash-aarch64-reference.md` — the unified GHASH/Gueron/AArch64 reference
  (NIST↔Q(x), the twist H̄=x·H, Prop 3 reduction by W(x)=0xC200…, and the per-function lane
  conventions). This is the doc that explains *why* the unroll8 key is `byteswap128 h`. See §6b.
- `_docs/htable-byteswap-analysis.md` — the focused htable lane-exchange analysis (init stores
  lanes-exchanged; gmult/ghash convert with `ext #8`; unroll8 uses as-is). See §6b.

---

## 0. Sources & provenance (every artifact this proof/doc relies on)

**Proof artifacts**
- Proved theorem: `arm/proofs/aesv8_gcm_8x_enc_256_1block.ml` (the work file).
- Frozen copy of the proved file: `_backups/aesv8_gcm_8x_enc_256_1block_bck0071_PROVED.ml`.
- Machine code: `arm/aes-gcm/aesv8_gcm_8x_enc_256.o` (assembled from
  `arm/aes-gcm/aesv8-gcm-armv8-unroll8.S`).

**Reused lemmas / bridge (where they came from)**
- `GMULT_FULL_CORRECT_BA` (Karatsuba+Prop3 byte-form = `polyval_dot`), `GHASH_1BLOCK_CORRECT`,
  `GHASH_1BLOCK_SIM`, `REV64_LANES_EQ`, `BYTESWAP128_INVOLUTION`, the "abbreviate-the-pmul-limbs
  then BITBLAST" close pattern — all ported/adapted from the standalone gcm_gmult_v8 proof:
  **`_backups/ghash_v8_sim.ml.bck0020`** (documented in `_docs/ghash-v8-symbolic-sim-walkthrough.md`).
- POLYVAL/GHASH algebra (`polyval_dot`, `ghash_polyval_acc`, `polyval_reduce_prop3`,
  `byteswap128`, `word_pmul`, `PMUL_KARATSUBA`): `common/polyval_ghash.ml`,
  `common/polyval.ml`, `common/karatsuba_pmul.ml`.
- AES spec + `AESENC`-style close: `arm/proofs/utils/aes_encrypt_spec.ml`,
  `arm/proofs/utils/aes.ml`, `common/aes.ml`.
- ARM simulation infrastructure: `arm/proofs/base.ml`.

**Math/spec basis**
- Gueron, "A New Interpretation for the GHASH Authenticator" (2023):
  `_docs/Shay-NewInterpretationGHASH-2023.txt` — Q(x), the twist, Prop 3 reduction.
- NIST SP 800-38D (GHASH definition) and RFC 8452 (`_docs/rfc8452-aes-gcm-siv.txt`, POLYVAL).
- These are surveyed in `_docs/aes-gcm-ghash-aarch64-reference.md` (cited above).

**Comparison baselines**
- Mila's standalone 1-block proof (extracted 112-instr subset). Remote `mila` =
  `https://github.com/manastasova/s2n-bignum-dev`, branch `one_block_very_messy_v1`,
  pinned at commit `8bc5c9e141f75007034d50fc9db70d30cb3b6b13`. GitHub permalinks:
  - proof (messy/working): https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/one_block_aes256_gcm_preloop_tail.ml
  - proof (claude 4.7 variant): https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/one_block_aes256_gcm_preloop_tail_claude_4.7.ml
  - proof (direct/POLYVAL bridge, source of `GHASH_1BLOCK_SIM`): https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/one_block_aes256_gcm_preloop_tail_direct.ml
  - spec: https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/proofs/utils/one_block_preloop_tail_spec.ml
  - extracted assembly: https://github.com/manastasova/s2n-bignum-dev/blob/8bc5c9e141f75007034d50fc9db70d30cb3b6b13/arm/aes-gcm/one_block_aes256_gcm_preloop_tail.S
  - branch tree at that commit: https://github.com/manastasova/s2n-bignum-dev/tree/8bc5c9e141f75007034d50fc9db70d30cb3b6b13

  The `GMULT_FULL_CORRECT_BA` lemma reused here comes from the nebeid fork
  (`origin` = `https://github.com/nebeid/s2n-bignum`), branch `ghash-v8-symbolic-sim`,
  file `arm/proofs/ghash_v8_sim.ml`, pinned at commit `38236a49c661bce61e9c5c2069e121ecd1f24241`:
  https://github.com/nebeid/s2n-bignum/blob/38236a49c661bce61e9c5c2069e121ecd1f24241/arm/proofs/ghash_v8_sim.ml
  (this is what `_backups/ghash_v8_sim.ml.bck0020` was taken from). Mila's parallel gmult
  proof on branch `gcm_gmult_proof` (commit `872af9212ebec47c349bea24ae5fecd6cec974e0`,
  https://github.com/manastasova/s2n-bignum-dev/tree/872af9212ebec47c349bea24ae5fecd6cec974e0)
  is the upstream lineage but is not on the nebeid fork — it is not under `origin`.
  Dependency analysis in `_docs/mila-gmult-proof-dependency-analysis.md` and
  `_docs/mila-gmult-proof-dependency-analysis-pr390.md`.
- XTS 1-block proof: `arm/proofs/aes-xts-encrypt-1-block.ml` (see §9).
- Approach comparison context: `_docs/ghash-gmult-proof-approach-comparison.md`.

All HOL claims attributed to "verified" in this doc were re-checked in-session on 2026-06-03
against the loaded definitions (not merely cited from the source docs).

---

## 1. The theorem (what is actually proved)

`ensures arm` from `pc+0x2c` to `pc+0x11d8` with:
- precondition: standard register/memory layout (X0=in_p, X1=word 128 i.e. 128 bits = 1
  block, Q30=ctr0, key schedule k0..k14 in `key_p`, H and Hk in `htbl_p`, xi in `xi_p`),
  PLUS two non-obvious carried facts:
  - `read (memory :> bytes64 (word_add stackpointer (word 64))) s = word 0xC200000000000000`
    — the Prop3 reduction constant the prologue MOVZ/STP'd to `[SP+64]` before the pc+0x2c
    entry. Carried as a precondition because the prologue is not simulated.
  - `word_subword hk (0,64) = word_xor (word_subword h (0,64)) (word_subword h (64,64))`
    — the Hk/H Karatsuba relation from htable init.
- postcondition:
  - `out_p = word_xor plaintext (aes256_encrypt ctr0 [k0..k14])`
  - `xi_p = word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
            [word_bytereverse (word_xor plaintext (aes256_encrypt ctr0 [k0..k14]))])`
    — **note the GHASH key is `byteswap128 h`, not `h`** (see §6).
  - `read PC s = word (pc + 0x11d8)` (stops before the callee-saved D8–D15 restore epilogue,
    which the pc+0x2c entry can't simulate — XTS-blessed PC-stop, see §8 of the old handoff).

---

## 2. Final proof methodology (the structure that worked)

Phase by phase (state numbers are cumulative instruction counts from s0; verify by PC, not by
assuming step==state — see §7 "dead ends"):

1. **AES rounds, steps 1–265** — `ARM_STEPS_TAC` in small batches with
   `DISCARD_COUNTER_REGS_TAC` after each (drops the >500-char counter-increment Q1–Q7/Q30 and
   Q16–Q19 terms). Batch boundaries matter: large un-discarded ranges are O(n²) in CLARIFY.
   - **Step 174–176 = GHASH tag load** (`LDR Q19,[xi_p]; EXT; REV64`). The REV64 makes a
     ~49k-char byte-tree; apply `GCM_SIMD_SIMPLIFY_TAC` immediately so Q19 folds to a clean
     ~120-char `word_join (reversefields 8 (subword xi 0,64)) (reversefields 8 (subword xi
     64,64))` that stays below the 500-char discard threshold and survives to the tail.
   - Step 255 branch resolved with a single `ARM_VSTEPS_TAC [255]` + `REWRITE_RULE
     [INT_SUB_REFL; INT_OF_NUM_EQ]`.
   - At s265, assert `Q9 = word_xor plaintext (aes256_encrypt ctr0 [..])` via the XTS
     `FIRST_X_ASSUM(MP_TAC o SPEC .. o MATCH_MP ..)` + `AESENC`-style close (unfold
     aes256_encrypt, let_CONV, BITBLAST). This replaces the bloated aese-tree with a clean term.

2. **Cascade + mask, steps 266–326** — `ARM_STEPS_RESOLVE_TAC` (branch resolution per step);
   the all-ones mask makes `AND/BIF v9` the identity. Re-assert Q9 clean after the mask via
   `CONV_TAC WORD_BLAST` (proves the all-ones-mask identity without expanding the aese tree).

3. **Ciphertext store window, steps 327–332** — `ARM_VSTEPS_RESOLVE_SIMD_TAC` (VSTEPS keeps
   the store read-back alive; per-step **double-fold** `GCM_SIMD_SIMPLIFY_TAC` keeps Q8 ≤352
   chars — see §3). Then assert `out_p = ciphertext` via `WORD_BLAST`.

4. **GHASH multiply/reduce, steps 333–348** — `ARM_VSTEPS_FOLD_TAC` (straight-line VSTEPS +
   per-step fold, NO branch resolution — the tail has no branches and RESOLVE_BRANCH caused
   state-label drift). Lands the reduced Karatsuba+Prop3 result in Q19 at s348.

5. **The s348 bridge** (the hard part — §5) — `DISCARD_OLDSTATE_TAC "s348"` (prune
   1357→77 hyps), then assert
   `read Q19 s348 = polyval_dot (word_xor (brev xi)(brev ct)) (byteswap128 h)`
   and prove it with the GMULT-based close.

6. **Tail + close, steps 349–351** — `ARM_VSTEPS_FOLD_TAC (349--350)` (EXT then REV64 =
   `word_bytereverse` via `REV64_LANES_EQ`), `ARM_VSTEPS_TAC [351]` (the `STR Q19,[X3]`
   store), `DISCARD_COUNTER_ONLY_TAC` (drops stale flags but **keeps PC** — §7),
   `ENSURES_FINAL_STATE_TAC`, then close the three conjuncts: PC by ASM, xi_p by
   `REV64_LANES_EQ` + `GHASH_1BLOCK_CORRECT`, frame by `MONOTONE_MAYCHANGE_TAC`.

---

## 3. The Q8/Q19 REV64-bloat fix (the "double-fold")

Root cause: `rev64 v8,v9` (0x1174, ~step 327) is emitted 5 instructions before the
ciphertext store, and a blanket `ARM_VSTEPS_TAC` does no per-step simplification, so the
4-level nested `word_join/word_subword` byte-tree (128→64→32→16→8) accumulates to ~582k chars
in `read Q8`. `DISCARD_COUNTER_REGS_TAC` never removed it (its filter listed Q1–Q7/Q16–Q19,
not Q8), so it poisoned every downstream tactic.

Fix: `GCM_SIMD_SIMPLIFY_TAC` applies its core **TWICE** (pass 1 normalizes nested subwords,
pass 2 fires the REV64 lane rules `REV64_LOWER_LANE/UPPER_LANE/128`). One pass leaves ~2.5k
chars; two passes reach the ~320-char fixpoint. Same fix folds the step-176 Q19 tag load.

---

## 4. Where the time goes (this machine, ~5.5 min total CPU, excludes one-time ELF decode)

| Phase | ~Time | Notes |
|-------|-------|-------|
| ELF `define_from_elf` + `ARM_MK_EXEC_RULE` (one-time, on file load) | ~40s | ~1150 instrs decoded |
| AES rounds 1–265 | ~19s | cheap, ~40ms/step + discards |
| Cascade 266–326 | ~22s | branch resolution per step |
| Ciphertext store 327–332 (VSTEPS+double-fold) | ~14s | |
| **GHASH multiply/reduce 333–348 (VSTEPS+fold)** | **~96s** | keeps every intermediate state s333..s348 alive, each carrying k-char GHASH terms |
| `DISCARD_OLDSTATE` + **s348 bridge** | **~185s** | dominated by 2 WORD_BLASTs (MERGE operand-equalities ~76s + FINISH_WV skeleton ~107s) |
| Tail 349–351 + ENSURES_FINAL + xi_p/frame/PC close | ~15s | |
| **Total (warm, EXEC already loaded)** | **~330s** | cold `loadt` from scratch ≈ 6–7 min |

The two hot spots are the **GHASH tail VSTEPS** (~96s) and the **s348 bridge WORD_BLASTs**
(~185s). Together they are ~85% of the runtime.

**Authoritative clean-checkpoint measurement (2026-06-03):** a full `loadt` of the unmodified
file on a freshly-restarted `polyval-aes` checkpoint (chdir'd to the repo root so the relative
ELF path resolves) completed in **371 s CPU** end-to-end (`define_from_elf` + all preamble
lemmas + the proof), binding `AESV8_GCM_8X_ENC_256_1BLOCK` with **0 hypotheses** and no
CHEAT_TAC/new_axiom/mk_thm. This confirms the file is **self-sufficient**: its only external
dependencies are the six `needs` (`arm/proofs/base.ml`, `common/aes.ml`,
`arm/proofs/utils/aes.ml`, `arm/proofs/utils/aes_encrypt_spec.ml`, `common/karatsuba_pmul.ml`,
`common/polyval_ghash.ml`) plus the polyval-aes checkpoint — every lemma/tactic the proof uses
is defined in the file's own preamble.

---

## 5. The s348 bridge close (the technically hard step)

Goal: `read Q19 s348 = polyval_dot (word_xor (brev xi)(brev ct)) (byteswap128 h)`.
Both sides are Karatsuba+Prop3 byte-forms over `word_pmul` of symbolic 64-bit limbs;
`word_pmul` is not ground so it can't be reduced — it must stay opaque. Recipe:

1. Rewrite LHS `read Q19 s348` to its simulator byte-form via its own hypothesis
   (`FIRST_ASSUM ... GEN_REWRITE_TAC LAND_CONV`). **Required** — without it the LHS stays
   the atom `read Q19 s348` and the final WORD_BLAST sees an unexpandable term and fails.
2. `GEN_REWRITE_TAC RAND_CONV [GSYM (ISPECL [blk; byteswap128 h] GMULT_FULL_CORRECT_BA)]`
   — expands the RHS `polyval_dot` to the same Karatsuba+Prop3 byte-form. **Apply as its own
   step**; folded deep into a mega-THEN chain it intermittently no-ops (head-of-chain is fine).
3. `REWRITE_TAC[byteswap128]` then subword normalization (`WORD_INSERT_SUBWORD`,
   `WORD_SUBWORD_SUBWORD`, the subword-over-xor/join distribution lemma, `JOIN_SUBWORD_RULES`).
4. `ABBREV_INNER_PMULS_TAC` — abstract the 3 innermost `word_pmul` limbs (the Karatsuba
   lo/hi/mid) to fresh atoms `qqN`. **Must extract the exact goal subterms programmatically** —
   hand-written ABBREV operands fail to match because of `word_join` output-width typing
   (128 vs 256). After this both sides are in qq0,qq1,qq2 but in different argument order.
5. `MERGE_PMUL_ATOMS_TAC` — for each pair of pmul atoms, prove they're equal (same product up
   to argument order via `WORD_PMUL_SYM`, operands equal by `WORD_BLAST` through a typed
   `PMUL_CONG_128` congruence) and rewrite to merge. Collapses the LHS/RHS limbs to one set.
6. clean `word 0` noise (`WORD_XOR_0`, `SUBWORD0_LEMMAS`).
7. `ABBREV_WA_TAC` (abstract the inner Prop3 reduction pmul `pmul (subword _ 0,64) W`),
   then `FINISH_WV_TAC` (prove the two outer `wv` reduction pmuls equal, then `WORD_BLAST`
   the residual structural XOR/join/subword skeleton over the atoms).

All helper lemmas/tactics (`PMUL_CONG_128`, `SUBWORD_XOR_JOIN_DIST`, `SUBWORD0_LEMMAS`,
`ABBREV_INNER_PMULS_TAC`, `MERGE_PMUL_ATOMS_TAC`, `ABBREV_WA_TAC`, `FINISH_WV_TAC`) are in the
file preamble.

---

## 6. The key insight: GHASH key is `byteswap128 h` (and the half-swap red herring)

The single fact that unblocked everything: at s348 the assembly has computed
`polyval_dot (word_xor (brev xi)(brev ct)) (byteswap128 h)` — the **block is the plain spec
block**, and the **GHASH key is `byteswap128 h`** (the htable stores H in a twisted/byteswapped
layout; the real key is `byteswap128(read htbl_p)`).

This was found by brute numeric search: instantiating GMULT with candidate `(block, key)`
pairs and evaluating concretely, only `(blk_plain, byteswap128 h)` reproduced `read Q19 s348`.

**Obsolete detour (don't repeat):** for a long time the *block* looked lane-swapped
(`block_a = lane_swap(blk_plain)`), leading to a "polyval_dot is not lane-swap invariant"
dead-end. That was a **mis-extracted operand** — the operand was pulled from one inner pmul
rather than identifying the actual `(a,b)` GMULT instantiation. The numeric test
`read Q19 s348 = polyval_dot block_a h` was FALSE; `= polyval_dot blk_plain (byteswap128 h)`
was TRUE. Lesson: when an operand "looks lane-swapped", suspect the *key* convention and test
the whole `polyval_dot a b` numerically before theorizing.

**Consequence:** the postcondition's GHASH key had to change `h → byteswap128 h`. ⚠️ This is a
change to the theorem *statement* — before composing with the loop proof, confirm the rest of
the GCM development treats `read htbl_p` as the twisted key (i.e. uses `byteswap128 h` too).

This matches Mila's standalone `GHASH_1BLOCK_SIM`, which used
`h_from_htable = byteswap128(byteswap128 h)` (two byteswaps cancelling) — her extracted
function had a different load/EXT placement, so her net key was plain `h`; ours nets one
byteswap.

---

## 6b. WHY the key is `byteswap128 h`: the htable lane-exchange convention (verified)

The `byteswap128 h` key is not an accident — it is forced by the htable's storage convention,
explained in `_docs/htable-byteswap-analysis.md` and `_docs/aes-gcm-ghash-aarch64-reference.md`
(§3, §7). The bridging facts below were **verified in HOL** (2026-06-03):

**What `byteswap128` actually is (verified).** Despite the name, the HOL `byteswap128` is NOT
a per-byte reversal — it is the pure **64-bit lane swap**:
```
byteswap128 x = word_join (word_subword x (0,64)) (word_subword x (64,64))    [the definition]
```
PROVED in HOL: `byteswap128 x = word_join (subword x 0,64)(subword x 64,64)` (TRUE) and
`byteswap128 x = word_bytereverse x` (FALSE). So **`byteswap128` = exactly the `ext v,v,#8`
instruction** (swap the two 64-bit halves), and it is distinct from `word_bytereverse` (the
genuine 16-byte reversal, = `word_reversefields 8`, also verified via
`WORD_BYTEREVERSE_REVERSEFIELDS`).

**The lane conventions (from the reference docs).** A 128-bit GF(2¹²⁸) element has two layouts:
- *natural polynomial order*: `d[0]`=low coeffs (x⁰..x⁶³), `d[1]`=high. `pmull` on `d[0]` gives
  low×low. This is what gmult/ghash-2x/4x work in.
- *lanes-exchanged*: `d[0]`=high, `d[1]`=low. Produced by `ext #8` from natural order.

Per the reference's per-function table:
| Function | H from htable | data prep | working order |
|---|---|---|---|
| gcm_gmult_v8 / ghash 2x / 4x | `ext #8` → natural | `rev64` + `ext #8` → natural | **natural** |
| **aesv8_gcm_8x (the unroll8)** | **used as-is (lanes-exchanged)** | **`rev64` only** | **lanes-exchanged** |

`gcm_init_v8` stores all H powers **lanes-exchanged** (it computes the twist H̄=x·H in natural
order, then applies `ext #8` before every store). The unroll8 consumes them **as-is** with no
conversion, and prepares data with **`rev64` only** (no `ext #8`) — `rev64` alone lands data in
lanes-exchanged order too, so both operands agree. This is a deliberate optimization: it keeps
the hottest loop (8-block interleaved AES+GHASH) free of lane-conversion `ext`s, pushing the
conversions into the small gmult/ghash functions instead.

**Why this produces `byteswap128 h` in the spec.** The htable value `h = read htbl_p` is the
twisted key in **lanes-exchanged** order. The GHASH algebra (`polyval_dot`, `ghash_polyval_acc`)
is stated in **natural** order. Converting lanes-exchanged → natural is exactly one `ext #8` =
one `byteswap128`. So the GHASH key the algebra sees is `byteswap128 h`. The unroll8 never
emits that `ext` (it works lanes-exchanged), so the conversion surfaces in the *spec* instead —
which is precisely the `h → byteswap128 h` change required in the spec. Contrast gmult, which DOES
emit the `ext #8` on its H load, so its spec key is plain `h` (and Mila's extraction, modeling
that `ext`, nets `byteswap128(byteswap128 h) = h`).

**Cross-check on the data side (verified).** The reference's stage analysis says `rev64`-alone
= lanes-exchanged and `rev64`+`ext8` = natural; these are genuinely different orders. Confirmed
in HOL: `REV64_LANES_EQ` gives `rev64-per-lane(R) = word_bytereverse R` (no ext8), whereas
`rev64(ext8 x) = word_bytereverse(byteswap128 x) ≠ word_bytereverse x`. So the tail
EXT(349)+REV64(350) on the reduced result is `word_bytereverse` of the natural-order result —
matching the spec's outer `word_bytereverse` wrapper, with no stray lane swap.

**Net:** the `byteswap128 h` key is the formal shadow of "the unroll8 keeps H lanes-exchanged
to avoid `ext`s in the hot loop." It is correct, not a workaround — but because it is a
convention encoded in `gcm_init_v8`'s storage, the composed correctness statement must be
consistent about it (see the ⚠️ in §6 and §11).

---

## 7. Things that didn't work / took too long (dead ends — do not retry)

- **Hand-written `ABBREV_TAC` operands for the pmul limbs** — fail silently (no substitution)
  because the goal's `word_join (brev xi)(brev xi)` is typed `(256)word` while a freshly-parsed
  identical-looking term is `(128)word`. Always extract subterms from the live goal.
- **`CONV_TAC WORD_BLAST` on the whole bridge before abbreviating the 5 pmuls** — explodes /
  times out (>400–500s) because it tries to bit-blast the 128×128 carryless multiplies.
- **The original file close abbreviated only 3 pmuls** (p_lo/p_hi/p_mid) — leaving wa/wv
  un-abbreviated, so BITBLAST still tried to blast the reduction pmuls. Need all 5.
- **`WORD_PMUL_SYM` as a bare rewrite** — loops. Use it one-directionally via `GEN_REWRITE_TAC
  LAND_CONV` or inside a congruence.
- **A single mega-`e(...)` THEN chain for the whole proof** intermittently leaves the GSYM
  GMULT step a no-op (RHS stays `polyval_dot`), then the final blast fails. Apply GMULT GSYM
  as a discrete step, or run the proof in phases.
- **Not pruning before the bridge** — with 1357 intermediate-state hyps, `ASM_REWRITE`/the
  bridge crawl (timed out at 400–500s twice). `DISCARD_OLDSTATE_TAC "s348"` (1357→77) is
  essential and safe (Q19@s348's RHS has no old-state refs).
- **`DISCARD_COUNTER_ONLY_TAC` discarding `read PC`** — left the final
  `read PC s351 = word(pc+4568)` goal unprovable. Now keeps PC (drops only NF/ZF/CF/VF).
- **`RESOLVE_BRANCH_TAC` in the straight-line GHASH tail** — caused `s{n}` label drift from
  the true PC. Use plain `ARM_VSTEPS_FOLD_TAC` there.
- **State==step assumption** — false across branches; always verify by reading PC.
- **`ARM_VSTEPS_FOLD_TAC` folding the store step itself (351)** — drops the store read-back.
  Fold 333–350, then plain VSTEP the store.
- **`(* ... *)` comment INSIDE the goal term** (between backticks) — HOL Light's term parser
  does NOT accept OCaml comments inside a quotation; it throws `Failure "term after binary
  operator expected"`. A documentation comment had been placed inside the precondition
  conjunction, which made the whole `prove` fail to parse — yet a `loadt` of the file returned
  without a propagated error (the parse failure was reported to stdout but `AESV8_..._1BLOCK`
  was silently left unbound, and the load "finished" in ~40s instead of ~370s). This masked a
  non-loading file as proved. **Lesson: keep all prose in OCaml comments OUTSIDE the backticks,
  and verify the theorem actually *binds* (not just that `loadt` returns) after a load.**

---

## 8. How it compares to Mila's proof

(GitHub permalinks to Mila's files/branches/commits are in §0 "Comparison baselines".)

| | Mila's standalone | This proof |
|---|---|---|
| Target | `one_block_aes256_gcm_preloop_tail` — a manually extracted 112-instruction subset, straight-line, dead code removed | the real full `aesv8_gcm_8x_enc_256` (1505 instrs), 1-block path = 352 steps with branch cascade |
| Per-step simplify | `GCM_ENC_SIMPLIFY_TAC` after *every* tail step (no branches) | `GCM_SIMD_SIMPLIFY_TAC` (double-fold) only in the REV64 windows; bulk `ARM_STEPS` elsewhere |
| Branch handling | none (straight-line) | `ARM_STEPS_RESOLVE_TAC` for the B.GE/B.GT cascade |
| GHASH key | `byteswap128(byteswap128 h) = h` (two byteswaps cancel) | `byteswap128 h` (one net byteswap) — different EXT placement in the full fn |
| Bridge lemma | `GMULT_FULL_CORRECT_BA` (same lemma reused) | same, instantiated with `b := byteswap128 h` |
| Composability | applies to a synthetic extraction | applies to the shipped aws-lc binary; composes with the loop/2-block/4-block proofs |

We deliberately did NOT use Mila's per-step `GCM_ENC_SIMPLIFY_TAC` everywhere — bulk stepping
+ targeted double-fold is faster for a bounded proof. We DID reuse her algebraic bridge lemmas.

## 9. How it compares to XTS (`aes-xts-encrypt-1-block.ml`)

| | XTS 1-block | This proof |
|---|---|---|
| Instr count | ~108 | ~352 (1-block path of a 1505-instr fn) |
| AES close | `XTSENC_TAC` (wraps AESENC with tweak/XOR) | direct `FIRST_X_ASSUM + AESENC`-style (no tweak; GCM just XORs CTR output) |
| Store capture | "assert register = spec right before the store" so the read-back survives | same pattern for `out_p` (s332) and `xi_p` (s348 bridge) |
| Branches | 1–2 | ~10 (cascade) → `ARM_STEPS_RESOLVE_TAC` (O(1)/branch vs RULE_ASSUM_TAC O(n) which hung) |
| GHASH | none | the entire hard part (Karatsuba+Prop3 ↔ polyval_dot bridge) |
| D-reg epilogue | simulated (enters at function start, matching STP prologue) | NOT simulated (enters pc+0x2c) → PC-stop at pc+0x11d8, Prop3 constant carried as precond |

XTS supplied the overall bounded-proof skeleton and the assert-before-store idiom; GHASH and the
byteswap-key reconciliation are entirely new here.

---

## 10. Optimization opportunities (if a faster proof is wanted)

1. **The s348 bridge as a standalone abstract lemma (~185s → near-0 in the sim).** Prove once,
   over abstract `xi cc h : int128`,
   `<Q19-byteform>(xi,cc,h) = polyval_dot (word_xor (brev xi)(brev cc)) (byteswap128 h)`, then
   in the main proof just `MATCH_MP`/rewrite with it. Moves the two big WORD_BLASTs out of the
   per-run simulation and makes them cacheable. **Biggest single win.** (The blocker today is
   that the LHS byte-form is a 20k-char term not easily written by hand — generate it once via
   the simulator, abstract `ct→cc`, and `prove` it as a named theorem.)
2. **GHASH tail VSTEPS (~96s).** VSTEPS keeps every intermediate state alive. Either
   `DISCARD_OLDSTATE` more aggressively mid-tail, or step plain + re-assert Q19 at fewer points.
3. **`MERGE_PMUL_ATOMS_TAC` is O(pairs) WORD_BLASTs.** It currently tries all pairs; restrict to
   the known LHS↔RHS pairing (lo↔lo, hi↔hi, mid↔mid) to cut redundant blasts.
4. **Tighten `DISCARD_COUNTER_REGS_TAC` thresholds** so fewer huge terms ever form (the 500-char
   cutoff is heuristic).

---

## 11. Lessons (updated from the old plan doc)

- The old plan's "bulk-step then BITBLAST at the end" works for AES/ciphertext but NOT for
  GHASH — `word_pmul` is opaque, so you must bridge via `GMULT_FULL_CORRECT_BA`, not blast the
  pmul tree.
- "Only the stack constant remains" (repeated across handoffs) was wrong — the constant was the
  easy part (a precondition). The real wall was the **GHASH key byteswap convention**, invisible
  until you evaluate `polyval_dot a b` numerically against the simulator output.
- Per-step SIMD folding is only needed at REV64/EXT instructions; folding everywhere is wasteful.
  But under-folding (single pass, or starting too late) lets the 582k-char tree form.
- Verify state numbers by PC, never assume step==state across branches.
- When a WORD_BLAST "should" close but times out, the goal almost always still contains an
  opaque `word_pmul` (or an un-rewritten `read Qn sN` atom) — abstract it, don't wait.
- Keep `read PC` until `ENSURES_FINAL_STATE_TAC`.

### Stepping-cost lessons (apply to enc too; derived during the dec optimization pass)

These were found while optimizing the *decrypt* proof but are properties of the shared
stepping tactics, so they apply equally to this encrypt proof and to any future
multi-block proof. Full detail in the decrypt doc §7b/§8.

- **`ARM_(V)STEPS` cost is O(pile) per step** (memory-read resolution + `GCM_SIMD_SIMPLIFY`'s
  `RULE_ASSUM_TAC` re-scanning every hyp). A straight-line region that lets the pile grow to
  hundreds of hyps becomes quadratic. Discard (`DISCARD_OLDSTATE`) as soon as the live
  registers are self-contained in the input vars; carry the one fact you still need across the
  discard via `MP_TAC`/`DISCH`.
- **To carry a value across a discard, assert the self-contained *register* fact, not the
  *store read-back*.** The read-back references registers the discard drops; the register
  value (after the per-step fold) is expressed purely in the input vars and survives.
- **A dead running register can dominate a bulk step group.** In dec, the unused CTR counter
  `Q30` grew to a ~25k-char rev32 tree and a single lane-`add` over it cost ~34s inside an
  un-split `(1--11)` group. Split the group so `DISCARD_COUNTER_REGS` fires before the
  expensive op. (Profiling caveat: attribute a spike to the *exact* step, not the enclosing
  range — the dec spike was mis-blamed on a coarse `(12--84)` group for a long time.)
- **The code-range constant in the spec must equal the function's actual byte length** — never
  copy it from a sibling proof (dec needed 4612, not enc's 4600), or tail stores fail
  store-safety (decrypt doc §7b item 1).

--------------------------------------------------------------------------------
## 12. Byte-aligned ≤1-block generalization (`AESV8_GCM_8X_ENC_256_LE1BLOCK_BODY`)

Status: **PROVED** end-to-end (appended to `arm/proofs/aesv8_gcm_8x_enc_256_1block.ml`;
full-file `loadt` ~714s, both theorems bound, no cheats, 3 axioms). Mirror of the decrypt
`AESV8_GCM_8X_DEC_256_LE1BLOCK_BODY` (see the dec methodology doc §11–§12 for the shared
machinery: `MASK_LEMMA` via the structural `BL16_DISJ` enumeration, `INSERT2_JOIN`,
`BLEND_OR_XOR`, the `bl_resolve_pc` cascade resolvers, the one symbolic-`bl` run).

Generalizes `bit_len = 128` to `bit_len = 8*bl`, `1 <= bl <= 16`, one symbolic-`bl` run.
With `CT = word_xor plaintext (aes256_encrypt ctr0 keys)` and `MK = word(2^(8*bl)-1)`:
- output `out_p := word_xor (word_and CT MK) (word_and outprev (word_not MK))`
- tag GHASHes `word_and CT MK`; extra precond `outprev` = prior out_p contents (the `bif` reads it).
At `bl=16` (MK all-ones) both collapse to the full-block forms. Entry pc+0x2c, exit pc+0x11d8,
code range 4600, bridge at s348 — same as the full-block enc body.

**The one enc-specific subtlety (vs dec).** Dec's GHASH block was `word_and cph MK` with `cph`
an *atom* (the loaded input ciphertext), so its block term stayed compact through the multiply.
Enc's block is `word_and CT MK` where `CT` is the full 15-round AES tower — compound. Two
consequences, both fixed by keeping the block atomic:
1. **Abbreviate the ciphertext to an atom `ct` right after the AES rounds (s265)**, where
   `read Q9 s265 = CT`. Use the MESON-SPEC trick to fold the `aese/aesmc` tower to
   `word_xor plaintext (aes256_encrypt ...)` (needs a *leading* `ONCE_REWRITE_TAC[WORD_XOR_ASSOC]`
   before expanding, then a trailing one), then `ABBREV_TAC ct = ...`. The whole mask region,
   GHASH multiply, and bridge then carry the atom.
2. **Collapse the partial-block mask on Q9 BEFORE the `rev64 v8,v9`, not after.** Enc runs
   `and v9,v9,v0` (step 326) then `rev64 v8,v9` (step 327) then `bif`+store — all inside the
   less_than_1 VSTEPS window. The GHASH block lives in Q8 = rev64(Q9). If you collapse the mask
   only at s328 (after the rev64), Q8 already holds the *uncollapsed* csel mask-tower and the
   multiply blows `Q19 s348` up to ~150k chars, so `FINISH_WV_TAC` fails. Fix: split the window —
   `ARM_VSTEPS_RESOLVE_SIMD_TAC (312--326)`, re-assert `read Q9 s326 = word_and ct MK`
   (`INSERT2_JOIN` + `MASK_LEMMA` + `WORD_RULE`), then `(327--328)` so the rev64 reads the clean
   Q9 and Q8 s328 is the rev64 of the compact masked block. (Instruction 15 of the less_than_1
   block = `and v9` = step 326; instruction 16 = `rev64 v8,v9` = step 327, counting the block
   start 0x1138 as step 312.)

With those, the out_p blend collapse (s340, `word_or → word_xor` via `BLEND_OR_XOR`+`MASK_LEMMA`)
and the bridge (`GMULT_FULL_CORRECT_BA` + `ABBREV_INNER_PMULS_TAC` + `MERGE_PMUL_ATOMS_TAC` +
`ABBREV_WA_TAC` + `FINISH_WV_TAC`, all over the atomic masked block) close exactly as the
full-block enc proof. The final close expands `gval` and `ct` back. The standalone development
copy is `_docs/enc_le1block_full.ml`.

Like dec, this is the k=1 instance of a `less_than_k` family and the partial-block masking is
dead from the whole-block-only aws-LC caller (proven for completeness).
