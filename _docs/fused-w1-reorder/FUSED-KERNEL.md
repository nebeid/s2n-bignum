# The fused short-message decrypt kernel — shareable artifact

This directory is the experiment record for the fused variant (`d5r`). Most of
the files here are generators and intermediate patches from the search. **If you
just want the result, you want these two files:**

| file | what |
|---|---|
| `aesv8_gcm_8x_dec_256_wb.fused.S` | the complete fused kernel, ready to assemble |
| `base-to-fused.patch` | the delta that produces it from the kernel on this branch |

Everything else (`gen_*.py`, `d5.patch`, `w1-to-d5.patch`, `provision*_w1.sh`, …)
is search scaffolding, kept for reproducibility. The narrative is in
[`../fused-w1-reorder.md`](../fused-w1-reorder.md); the numbers are in
[`../percommit-crosscore-benchmark-2026-08-14.md`](../percommit-crosscore-benchmark-2026-08-14.md).

## Applying it

```bash
git apply _docs/fused-w1-reorder/base-to-fused.patch
```

The base is `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` **as it stands on
`aes-gcm-fused-wip`**. The patch is purely additive — **3 hunks, +260 / −0
lines** — so nothing in the existing whole-blocks kernel is modified, moved or
deleted. The `nblk >= 8` code, including the entire main loop, is untouched.

## What it adds

Fused straight-line paths for **1–4 whole blocks** (16/32/48/64 B), which the
generic kernel otherwise handles by entering the 8-way cascade. Twelve new
labels:

* `.L256_dec_w5r_stub_{1,2,3,4}` — per-block-count entry, seeding the GHASH
  accumulator directly as `Xi' * H^k` instead of accumulating it
* `.L256_dec_w5r_g{1,2,3,4}` — the single-block GHASH bodies at each power of H
* `.L256_dec_frame_restore` — **one** shared frame restore, so there is a single
  `ret` for all `nblk >= 1` (this is what distinguishes `d5r` from the earlier
  `d5`, which duplicated the epilogue)
* `.L256_dec_w5r_small`, `.L256_dec_w5r_h1`, `.L256_dec_w5r_done` — dispatch and
  rejoin

## Provenance — read this before trusting the numbers

The file here is byte-equivalent **as machine code** to the object that was both
benchmarked and proved, but it is not the same *text* as the benchmark input,
because it has been rebased onto this branch's `.S`. Specifically:

| artifact | md5 | note |
|---|---|---|
| benchmark input `C.S` (base) | `6de404aca78da9799a911b126727c73f` | v5 `91b1ce25` |
| benchmark input `D.S` (fused) | `94b4f2c9efc7b85341def2858074c1b1` | what was timed |
| assembled `D.o` | `968b7a2f0e89093da5d1961d978e4f44` | the object baked into the fused HOL checkpoint |
| this branch's base `.S` | `484fc2d025accfee8d08feaf360be5cc` | differs from `C.S` by 57 lines, **all comments** (`[opt]` markers stripped) |
| `aesv8_gcm_8x_dec_256_wb.fused.S` | rebased | — |

The two bases assemble to identical `.text` (md5 `81cd87ce…` under Apple `as`),
and this rebased fused file assembles to the same `.text` as the benchmarked
`D.S` (md5 `fd19c342…` under Apple `as`). So the comment-only drift is confirmed
non-semantic and the file below is the kernel the measurements describe.

`__text` is **4968 → 5960 bytes, +992 B (+20.0 %)** — the footprint cost of the
fused entry paths.

## Verification status

Four fused bodies are proof-complete: `WB_FUSED_{1,2,3,4}BLOCK`, each `hyps=0`,
`axioms=3`, 0-CHEAT, re-validated against upstream's current instruction model.
They are **not yet spliced** into the shipped kernel on
`aes-gcm-wb-mainloop` — that is a separate, sequenced step, because splicing
changes the object bytes and therefore requires a full re-gate of the
whole-blocks proof.

## Performance, in one table

Fused versus the non-fused whole-blocks kernel, Graviton4 / Neoverse-V2, median
of per-process paired deltas; negative = faster. `~` = below that size's
measured placement floor, i.e. not resolved.

| size | delta |
|---:|---:|
| 16 B | **−46.4 %** |
| 32 B | **−43.6 %** |
| 64 B | **−26.9 %** |
| 128 B | −0.05 %~ |
| 256 B | −0.22 %~ |
| 512 B | −0.29 % (V1) / +0.14 % (V2) / +0.02 % (V3) |
| 1024 B | +0.44 %~ |
| 4096 B | −0.00 %~ |

Two things to know:

1. An earlier revision of these numbers reported **+1.48 % at 512 B**. That was
   an artifact of a `min`-over-processes estimator and is **retracted**; a
   four-host study (32–40 processes per host, bootstrap CIs, 5 link permutations
   × 5 padding offsets) found no regression on any core. Details in
   [`../512b-placement-2026-08-20/`](../512b-placement-2026-08-20/).
2. The wins are confined to 16/32/64 B. aws-lc's dispatch currently gates the 8x
   kernel on `len >= 256` (moving to 128), so those sizes are not ones its
   dispatch routes here today. The value is for callers that do route them, or
   for a future threshold change.
