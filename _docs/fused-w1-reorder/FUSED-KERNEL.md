# The fused short-message decrypt kernel (`d5r`)

A fused straight-line path for **1–4 whole blocks** (16/32/48/64 B), which the
generic whole-blocks kernel otherwise handles by entering the 8-way cascade.
It is worth **−22 % to −47 %** at those sizes and nothing at all above them.

This directory is the experiment record for how it was found. Most files here are
generators and intermediate patches from that search. **Two files are the
result:**

| file | what |
|---|---|
| `aesv8_gcm_8x_dec_256_wb.fused.S` | the complete fused kernel, ready to assemble |
| `base-to-fused.patch` | the delta that produces it from the kernel on this branch |

Everything else (`gen_*.py`, `d5.patch`, `w1-to-d5.patch`, `provision*_w1.sh`, …)
is scaffolding, kept so the search can be re-run. The full narrative — every
candidate ordering tried and rejected — is in
[`../fused-w1-reorder.md`](../fused-w1-reorder.md).

## Applying it

```bash
git apply _docs/fused-w1-reorder/base-to-fused.patch
```

The base is `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` as it stands on
`aes-gcm-fused-wip`. The patch is **purely additive — 3 hunks, +260 / −0 lines**.
Nothing in the existing kernel is modified, moved or deleted; the `nblk >= 8`
code, including the entire main loop, is byte-for-byte untouched.

## What it adds

Twelve labels, and no changes outside them:

| label | role |
|---|---|
| `.L256_dec_w5r_stub_{1,2,3,4}` | per-block-count entry; seeds the GHASH accumulator directly as `Xi' * H^k` instead of accumulating it |
| `.L256_dec_w5r_g{1,2,3,4}` | the single-block GHASH bodies, one per power of H |
| `.L256_dec_frame_restore` | **one** shared frame restore, giving a single `ret` for all `nblk >= 1` |
| `.L256_dec_w5r_small`, `_h1`, `_done` | dispatch and rejoin |

The shared frame restore is the only thing separating `d5r` from the earlier
`d5`, which duplicated the epilogue.

## Performance

Fused (`d5r`) versus the non-fused kernel, both in the same binary with an A/A
twin alongside every variant. Negative = faster. All four hosts, from
[`../fused-w1-reorder.md`](../fused-w1-reorder.md) §8.4:

| size | V1 / Graviton3 | V2 / Graviton4 | V2 / r8g | V3 / Graviton5 |
|---:|---:|---:|---:|---:|
| 16 B | **−47.50 %** | **−46.29 %** ‡ | *floor* | **−46.17 %** |
| 32 B | **−42.52 %** | **−43.56 %** | **−43.54 %** | **−42.89 %** |
| 48 B | **−32.33 %** | **−37.66 %** | **−37.70 %** | **−40.31 %** |
| 64 B | **−21.92 %** | **−27.23 %** | **−27.24 %** | **−31.02 %** |
| 80 B | +0.28 % | −0.01 % | +0.01 % | −0.05 % |
| 128 B | −0.15 % | +0.28 % | +0.19 % | +0.03 % |
| 4096 B | −0.40 % | −0.02 % | −0.02 % | +0.00 % |

**The size of the win depends strongly on the core** — at 64 B it spans −21.9 %
on V1 to −31.0 % on V3 — so no single number represents that row.

*floor*: the non-fused baseline drew a bad 16 B link slot in that binary, where
its own A/A floor was 4.38 % (GV4) and 7.55 % (r8g), so no 16 B figure was
claimable. The V1 and V3 floors at 16 B are 1.6 % and 0.02 %. ‡ = re-measured
2026-08-21 on the spliced object in a fresh binary, where Graviton4's 16 B floor
is 0.381 % and the cell resolves cleanly; r8g was not re-run.

A later, independent run on r8g covers the sizes the table above omits — a
different binary, different link slots, and a **median of per-process paired
deltas** rather than an absolute minimum ([`../aead-bench-2026-08-20/`](../aead-bench-2026-08-20/)):

| 16 B | 32 B | 64 B | 128 B | 256 B | 512 B | 1024 B | 4096 B |
|---:|---:|---:|---:|---:|---:|---:|---:|
| −46.4 % | −43.6 % | −26.9 % | −0.05 %~ | −0.22 %~ | +0.14 % | +0.44 %~ | −0.00 %~ |

`~` = inside that size's placement floor, i.e. not resolved. Where the two runs
overlap they agree to 0.1–0.4 points (32 B: −43.54 vs −43.6; 64 B: −27.24 vs
−26.9) despite different binaries and different estimators, and this run resolves
16 B because the baseline drew a better slot.

### Three things to know before quoting any of this

1. **An earlier revision claimed +1.48 % at 512 B. That is retracted.** It was an
   artifact of taking the minimum over processes. A dedicated four-host study
   (32–40 processes per host, bootstrap CIs, 5 link permutations × 5 padding
   offsets) found **no regression on any core**: −0.29 % on V1, +0.14 % on V2,
   +0.02 % on V3 — see [`../512b-placement-2026-08-20/`](../512b-placement-2026-08-20/).
2. **The §8.4 table uses that same absolute-min estimator.** It is sound for the
   −22…−47 % cells, which sit two to three orders of magnitude above any floor,
   and *not* sound for its 80/128/4096 B rows — treat those as indicative and
   prefer the median-based run for small effects.
3. **Above 128 B on V1, the dominant effect is code placement, not the variant.**
   Runtime there tracks the main loop's address mod 16. Any sub-1 % reading at
   those sizes is measuring layout unless placement is controlled for.

### Reach

The wins live at 16–64 B. aws-lc's dispatch currently gates this kernel on
`len >= 256` (moving to 128), so its own callers do not route those sizes here
today. The value is for callers that do, or for a future threshold change.

## Size cost

`__text` is **5960 bytes**: +992 B (+20.0 %) against the pre-`.balign` base of
4968 B, or **+984 B (+19.8 %)** against `aes-gcm-wb-mainloop`'s current 4976 B.

The spliced object comes out at 5960 B either way, md5
`968b7a2f0e89093da5d1961d978e4f44` — the same object as the standalone fused
kernel. The fused prologue's 8 extra bytes are absorbed by the existing
`.balign 16`, which then emits zero padding instead of eight, so the main loop
keeps its address and the body stays byte-identical at the same offsets (940
instructions diff-confirmed, same backedge).

## Verification status

All four fused bodies are proof-complete — `WB_FUSED_{1,2,3,4}BLOCK`, each
`hyps=0`, `axioms=3`, 0-CHEAT, re-validated against upstream's current
instruction model.

The splice itself is done and cold-gated, on `aes-gcm-splice-wip-s143`
@ `d7b524e2` rather than on `aes-gcm-wb-mainloop`: `loadsecs=4010.6 axioms=3`,
both exported targets bound at 0 hypotheses, 0 CHEAT / `new_axiom` / `mk_thm`,
against the CI-pinned HOL Light. It is held on its own branch because the splice
is atomic — installing the fused literal breaks the staggered front simulations
until the front-sim surgery and DISPATCH re-case land with it — and mainloop does
not accept a tip that fails to load.

Correctness was re-checked independently of the proof: the 4968 B, 4976 B and
5960 B committed objects each pass the differential test, the whole-blocks guard
and 7/7 aws-lc known-answer vectors on Graviton3, Graviton4 and Graviton5.

## Is this the exact file that was measured?

**Same machine code: yes. Same text: no.** If you diff this `.S` against our
benchmark input you will find differences, so here is what they are before you
wonder whether the numbers describe some other kernel.

The fused kernel is *a base version of the whole-blocks kernel, plus our
additions*. It was developed and measured against an older copy of that base.
Since then the base on this branch changed by **57 lines, every one of them a
comment** — `[opt]` progress markers that were stripped out. No instruction
changed.

So:

* what was measured = **older base + fused additions**
* what is published here = **current base + fused additions**

Comments never become instructions, so both assemble to the same machine code.
That is checked rather than assumed — assemble each and compare the `.text`
section:

```bash
cc -E -Iinclude f.S | as -arch arm64 -o f.o -    # then compare .text bytes
```

Both give `.text` md5 `fd19c342…` under Apple `as`. The two *bases* likewise
agree with each other (`81cd87ce…`), which is what shows the comment-only drift
is non-semantic. Identical instructions means identical performance, by
construction — so the measurements above apply to the file published here.

For anyone re-deriving the numbers or the proof, the four inputs by md5:

| file | md5 | why it matters |
|---|---|---|
| the base we measured against | `6de404aca78da9799a911b126727c73f` | v5, commit `91b1ce25` |
| the fused file we measured | `94b4f2c9efc7b85341def2858074c1b1` | the actual benchmark input |
| that file assembled | `968b7a2f0e89093da5d1961d978e4f44` | also the object baked into the fused HOL checkpoint, so this pins the *proved* kernel too |
| this branch's base | `484fc2d025accfee8d08feaf360be5cc` | the 57-comment-line variant published here builds on |
