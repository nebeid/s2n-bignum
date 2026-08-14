# Per-commit cross-core benchmark: AES-256-GCM decrypt kernel (`aesv8_gcm_8x_dec_256_wb`)

Date: 2026-08-14. Six commit versions, three Graviton generations, one interleaved binary per host.

## Method

* Six versions of `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` extracted with `git show <commit>:<path>`
  from `/Volumes/workplace/git-code/s2n-bignum-kiro` (branch `aes-gcm-wb-mainloop`, read-only).
* Each assembled separately with gcc 13.3.0, then `objcopy --redefine-sym
  aesv8_gcm_8x_dec_256_wb=aes_dec_vN` so the six exported symbols are distinct.
* **All six linked into ONE binary** with two extra A/A duplicates: `aa5` is a second copy of
  v5's code and `aa0` a second copy of v0's code, under different symbol names.
* Measured **round-robin interleaved in a single process**: for each rep, for each size, all
  eight symbols are timed back-to-back; the symbol visiting order is rotated by rep index to
  defuse position bias. Best-of-200 reps per process, 10 independent processes per host,
  final figure = min across all of them.
* Pinned with `taskset` to one non-zero core (core 3 on GV3, core 5 on GV4/GV5).
* Batch sizes: 40000/20000/12000/6000/3000 calls for 128/256/512/1024/4096 B, so every timed
  batch is >1 ms. Buffers are static and L1/L2-resident.
* Core clock measured in-process with a dependent scalar-add chain (1 cycle/add on V1/V2/V3),
  before and after the sweep.
* Sizes are whole blocks only. `Xi`/`ivec` are reset to the same seed before every batch.

### Correctness self-check

Mandatory gate, run before any timing in every process on every host: all eight symbols are
called on identical input and their **plaintext output, `Xi` and `ivec` compared byte-for-byte**
against v0, at all five sizes, plus the return value (bytes processed).

**Result: PASS on all three hosts, all 30 processes (10 per host).** Timings below therefore come from a build
where symbol wiring is verified and all six versions are functionally identical.

### Caveats

* GV4/GV5 here are **4xlarge**, while the project's earlier benchmark doc used **2xlarge**.
  Absolute ns figures are therefore not comparable to that report; percentages are.
* Absolute ns also differ from the project's `benchmarks/benchmark.c` numbers because this
  harness uses its own tighter timing loop (best-of-min over >1 ms batches, hot buffers,
  pinned core) rather than the project harness's averaging over bit-densities.

## GV3 — c7g.2xlarge, Neoverse-V1 (0xd40)

Measured core clock: **2.591 GHz** (range across all 20 in-process measurements: 2.5912-2.5915 GHz).

### A/A noise floor

Same code under two symbol names (`v5` vs `aa5`, `v0` vs `aa0`), computed on exactly the same
min-over-10-processes statistic as the reported figures. The last column is the spread of the
10 individual per-process minima, shown for information only (the reported figure is their min).

| size | v5 | aa5 | A/A delta | v0 | aa0 | A/A delta | max run-to-run spread (any symbol) |
|---|---|---|---|---|---|---|---|
| 128 | 30.058 | 30.227 | +0.56% | 38.022 | 38.260 | +0.63% | 1.07% |
| 256 | 52.183 | 52.425 | +0.46% | 61.742 | 62.012 | +0.44% | 1.24% |
| 512 | 94.485 | 95.057 | +0.61% | 104.787 | 104.409 | -0.36% | 1.27% |
| 1024 | 180.512 | 180.172 | -0.19% | 190.024 | 190.063 | +0.02% | 0.51% |
| 4096 | 692.424 | 692.199 | -0.03% | 701.455 | 701.403 | -0.01% | 0.52% |

**Noise floor used below** (max of the two A/A deltas, per size): 128B 0.63%, 256B 0.46%, 512B 0.61%, 1024B 0.19%, 4096B 0.03%.
Any per-commit delta smaller in magnitude than the floor for its size is called noise.

### ns/call, all six versions

| version | commit | change | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|---|---|
| v0 | `5500b7e6` | baseline (whole-blocks-only decrypt) | 38.02 | 61.74 | 104.79 | 190.02 | 701.46 |
| v1 | `51a51943` | ins->ext in GHASH tail mids | 33.09 | 55.14 | 98.30 | 183.46 | 694.83 |
| v2 | `8ca8a201` | exact-8 GHASH drain | 32.20 | 53.87 | 96.70 | 181.99 | 694.15 |
| v3 | `6f144724` | eor3-fuse exact-8 drain accumulate chains | 31.40 | 53.27 | 95.66 | 181.06 | 693.41 |
| v4 | `fc42a21a` | flatten SETUP counter chain (depth 7->2) | 30.50 | 52.75 | 94.77 | 180.12 | 692.92 |
| v5 | `91b1ce25` | TAIL odd-block mids ins+pmull2 -> ext+pmull | 30.06 | 52.18 | 94.49 | 180.51 | 692.42 |

Cycles/call at 2.591 GHz:

| version | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|
| v0 | 99 | 160 | 272 | 492 | 1818 |
| v1 | 86 | 143 | 255 | 475 | 1801 |
| v2 | 83 | 140 | 251 | 472 | 1799 |
| v3 | 81 | 138 | 248 | 469 | 1797 |
| v4 | 79 | 137 | 246 | 467 | 1796 |
| v5 | 78 | 135 | 245 | 468 | 1794 |

### Per-commit incremental gain (each commit vs its immediate predecessor)

Negative = faster. `~` marks a delta below this host+size noise floor.

| step | change | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|---|
| v0->v1 (`51a51943`) | ins->ext in GHASH tail mids | -12.96% | -10.70% | -6.19% | -3.46% | -0.94% |
| v1->v2 (`8ca8a201`) | exact-8 GHASH drain | -2.70% | -2.29% | -1.63% | -0.80% | -0.10% |
| v2->v3 (`6f144724`) | eor3-fuse exact-8 drain accumulate chains | -2.49% | -1.13% | -1.07% | -0.52% | -0.11% |
| v3->v4 (`fc42a21a`) | flatten SETUP counter chain (depth 7->2) | -2.86% | -0.96% | -0.94% | -0.52% | -0.07% |
| v4->v5 (`91b1ce25`) | TAIL odd-block mids ins+pmull2 -> ext+pmull | -1.45% | -1.08% | -0.30%~ | +0.22% | -0.07% |

### Cumulative: baseline `5500b7e6` -> HEAD `91b1ce25`

| size (bytes) | old ns/call | new ns/call | ratio (new/old) | speedup |
|---|---|---|---|---|
| 128 | 38.0 | 30.1 | 0.791 | +20.9% |
| 256 | 61.7 | 52.2 | 0.845 | +15.5% |
| 512 | 104.8 | 94.5 | 0.902 | +9.8% |
| 1024 | 190.0 | 180.5 | 0.950 | +5.0% |
| 4096 | 701.5 | 692.4 | 0.987 | +1.3% |

## GV4 — c8g.4xlarge, Neoverse-V2 (0xd4f)

Measured core clock: **2.792 GHz** (range across all 20 in-process measurements: 2.7919-2.7924 GHz).

### A/A noise floor

Same code under two symbol names (`v5` vs `aa5`, `v0` vs `aa0`), computed on exactly the same
min-over-10-processes statistic as the reported figures. The last column is the spread of the
10 individual per-process minima, shown for information only (the reported figure is their min).

| size | v5 | aa5 | A/A delta | v0 | aa0 | A/A delta | max run-to-run spread (any symbol) |
|---|---|---|---|---|---|---|---|
| 128 | 25.492 | 25.491 | -0.00% | 32.438 | 32.451 | +0.04% | 1.72% |
| 256 | 45.420 | 45.461 | +0.09% | 54.235 | 54.250 | +0.03% | 1.37% |
| 512 | 83.963 | 84.558 | +0.71% | 94.337 | 94.486 | +0.16% | 0.81% |
| 1024 | 162.025 | 161.970 | -0.03% | 171.201 | 171.699 | +0.29% | 0.84% |
| 4096 | 628.473 | 628.007 | -0.07% | 638.007 | 638.275 | +0.04% | 0.20% |

**Noise floor used below** (max of the two A/A deltas, per size): 128B 0.04%, 256B 0.09%, 512B 0.71%, 1024B 0.29%, 4096B 0.07%.
Any per-commit delta smaller in magnitude than the floor for its size is called noise.

### ns/call, all six versions

| version | commit | change | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|---|---|
| v0 | `5500b7e6` | baseline (whole-blocks-only decrypt) | 32.44 | 54.24 | 94.34 | 171.20 | 638.01 |
| v1 | `51a51943` | ins->ext in GHASH tail mids | 28.82 | 48.49 | 88.10 | 164.50 | 632.28 |
| v2 | `8ca8a201` | exact-8 GHASH drain | 27.78 | 47.94 | 86.67 | 164.04 | 629.91 |
| v3 | `6f144724` | eor3-fuse exact-8 drain accumulate chains | 26.71 | 47.12 | 85.84 | 163.40 | 629.45 |
| v4 | `fc42a21a` | flatten SETUP counter chain (depth 7->2) | 25.68 | 45.65 | 84.38 | 162.05 | 628.07 |
| v5 | `91b1ce25` | TAIL odd-block mids ins+pmull2 -> ext+pmull | 25.49 | 45.42 | 83.96 | 162.02 | 628.47 |

Cycles/call at 2.792 GHz:

| version | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|
| v0 | 91 | 151 | 263 | 478 | 1781 |
| v1 | 80 | 135 | 246 | 459 | 1765 |
| v2 | 78 | 134 | 242 | 458 | 1759 |
| v3 | 75 | 132 | 240 | 456 | 1758 |
| v4 | 72 | 127 | 236 | 452 | 1754 |
| v5 | 71 | 127 | 234 | 452 | 1755 |

### Per-commit incremental gain (each commit vs its immediate predecessor)

Negative = faster. `~` marks a delta below this host+size noise floor.

| step | change | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|---|
| v0->v1 (`51a51943`) | ins->ext in GHASH tail mids | -11.16% | -10.60% | -6.61% | -3.92% | -0.90% |
| v1->v2 (`8ca8a201`) | exact-8 GHASH drain | -3.60% | -1.13% | -1.62% | -0.28%~ | -0.38% |
| v2->v3 (`6f144724`) | eor3-fuse exact-8 drain accumulate chains | -3.87% | -1.72% | -0.95% | -0.39% | -0.07%~ |
| v3->v4 (`fc42a21a`) | flatten SETUP counter chain (depth 7->2) | -3.86% | -3.12% | -1.70% | -0.82% | -0.22% |
| v4->v5 (`91b1ce25`) | TAIL odd-block mids ins+pmull2 -> ext+pmull | -0.72% | -0.50% | -0.50%~ | -0.02%~ | +0.06%~ |

### Cumulative: baseline `5500b7e6` -> HEAD `91b1ce25`

| size (bytes) | old ns/call | new ns/call | ratio (new/old) | speedup |
|---|---|---|---|---|
| 128 | 32.4 | 25.5 | 0.786 | +21.4% |
| 256 | 54.2 | 45.4 | 0.837 | +16.3% |
| 512 | 94.3 | 84.0 | 0.890 | +11.0% |
| 1024 | 171.2 | 162.0 | 0.946 | +5.4% |
| 4096 | 638.0 | 628.5 | 0.985 | +1.5% |

## GV5 — c9g.4xlarge, Neoverse-V3 (0xd84)

Measured core clock: **3.291 GHz** (range across all 20 in-process measurements: 3.2902-3.2912 GHz).

### A/A noise floor

Same code under two symbol names (`v5` vs `aa5`, `v0` vs `aa0`), computed on exactly the same
min-over-10-processes statistic as the reported figures. The last column is the spread of the
10 individual per-process minima, shown for information only (the reported figure is their min).

| size | v5 | aa5 | A/A delta | v0 | aa0 | A/A delta | max run-to-run spread (any symbol) |
|---|---|---|---|---|---|---|---|
| 128 | 21.466 | 21.471 | +0.03% | 25.951 | 25.949 | -0.01% | 0.29% |
| 256 | 38.190 | 38.187 | -0.01% | 44.265 | 44.250 | -0.03% | 0.10% |
| 512 | 71.133 | 70.643 | -0.69% | 77.918 | 78.389 | +0.60% | 0.95% |
| 1024 | 138.491 | 138.518 | +0.02% | 146.300 | 146.407 | +0.07% | 0.48% |
| 4096 | 546.579 | 546.549 | -0.01% | 554.412 | 554.388 | -0.00% | 0.06% |

**Noise floor used below** (max of the two A/A deltas, per size): 128B 0.03%, 256B 0.03%, 512B 0.69%, 1024B 0.07%, 4096B 0.01%.
Any per-commit delta smaller in magnitude than the floor for its size is called noise.

### ns/call, all six versions

| version | commit | change | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|---|---|
| v0 | `5500b7e6` | baseline (whole-blocks-only decrypt) | 25.95 | 44.27 | 77.92 | 146.30 | 554.41 |
| v1 | `51a51943` | ins->ext in GHASH tail mids | 23.75 | 40.37 | 73.44 | 140.08 | 547.98 |
| v2 | `8ca8a201` | exact-8 GHASH drain | 23.00 | 39.75 | 72.87 | 139.23 | 547.59 |
| v3 | `6f144724` | eor3-fuse exact-8 drain accumulate chains | 22.43 | 39.32 | 71.63 | 138.19 | 546.33 |
| v4 | `fc42a21a` | flatten SETUP counter chain (depth 7->2) | 21.53 | 38.21 | 71.13 | 138.52 | 546.50 |
| v5 | `91b1ce25` | TAIL odd-block mids ins+pmull2 -> ext+pmull | 21.47 | 38.19 | 71.13 | 138.49 | 546.58 |

Cycles/call at 3.291 GHz:

| version | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|
| v0 | 85 | 146 | 256 | 481 | 1824 |
| v1 | 78 | 133 | 242 | 461 | 1803 |
| v2 | 76 | 131 | 240 | 458 | 1802 |
| v3 | 74 | 129 | 236 | 455 | 1798 |
| v4 | 71 | 126 | 234 | 456 | 1798 |
| v5 | 71 | 126 | 234 | 456 | 1799 |

### Per-commit incremental gain (each commit vs its immediate predecessor)

Negative = faster. `~` marks a delta below this host+size noise floor.

| step | change | 128B | 256B | 512B | 1024B | 4096B |
|---|---|---|---|---|---|---|
| v0->v1 (`51a51943`) | ins->ext in GHASH tail mids | -8.47% | -8.81% | -5.74% | -4.25% | -1.16% |
| v1->v2 (`8ca8a201`) | exact-8 GHASH drain | -3.17% | -1.53% | -0.78% | -0.61% | -0.07% |
| v2->v3 (`6f144724`) | eor3-fuse exact-8 drain accumulate chains | -2.49% | -1.09% | -1.70% | -0.75% | -0.23% |
| v3->v4 (`fc42a21a`) | flatten SETUP counter chain (depth 7->2) | -3.99% | -2.80% | -0.70% | +0.24% | +0.03% |
| v4->v5 (`91b1ce25`) | TAIL odd-block mids ins+pmull2 -> ext+pmull | -0.31% | -0.06% | +0.01%~ | -0.02%~ | +0.02% |

### Cumulative: baseline `5500b7e6` -> HEAD `91b1ce25`

| size (bytes) | old ns/call | new ns/call | ratio (new/old) | speedup |
|---|---|---|---|---|
| 128 | 26.0 | 21.5 | 0.827 | +17.3% |
| 256 | 44.3 | 38.2 | 0.863 | +13.7% |
| 512 | 77.9 | 71.1 | 0.913 | +8.7% |
| 1024 | 146.3 | 138.5 | 0.947 | +5.3% |
| 4096 | 554.4 | 546.6 | 0.986 | +1.4% |

## Cross-core comparison of each optimization

Incremental gain of each commit at each size, side by side across V1/V2/V3. Negative = faster.
`~` = below that host+size noise floor.

**v0 -> v1 (`51a51943`): ins->ext in GHASH tail mids**

| size | GV3 / V1 | GV4 / V2 | GV5 / V3 |
|---|---|---|---|
| 128 | -12.96% | -11.16% | -8.47% |
| 256 | -10.70% | -10.60% | -8.81% |
| 512 | -6.19% | -6.61% | -5.74% |
| 1024 | -3.46% | -3.92% | -4.25% |
| 4096 | -0.94% | -0.90% | -1.16% |

**v1 -> v2 (`8ca8a201`): exact-8 GHASH drain**

| size | GV3 / V1 | GV4 / V2 | GV5 / V3 |
|---|---|---|---|
| 128 | -2.70% | -3.60% | -3.17% |
| 256 | -2.29% | -1.13% | -1.53% |
| 512 | -1.63% | -1.62% | -0.78% |
| 1024 | -0.80% | -0.28%~ | -0.61% |
| 4096 | -0.10% | -0.38% | -0.07% |

**v2 -> v3 (`6f144724`): eor3-fuse exact-8 drain accumulate chains**

| size | GV3 / V1 | GV4 / V2 | GV5 / V3 |
|---|---|---|---|
| 128 | -2.49% | -3.87% | -2.49% |
| 256 | -1.13% | -1.72% | -1.09% |
| 512 | -1.07% | -0.95% | -1.70% |
| 1024 | -0.52% | -0.39% | -0.75% |
| 4096 | -0.11% | -0.07%~ | -0.23% |

**v3 -> v4 (`fc42a21a`): flatten SETUP counter chain (depth 7->2)**

| size | GV3 / V1 | GV4 / V2 | GV5 / V3 |
|---|---|---|---|
| 128 | -2.86% | -3.86% | -3.99% |
| 256 | -0.96% | -3.12% | -2.80% |
| 512 | -0.94% | -1.70% | -0.70% |
| 1024 | -0.52% | -0.82% | +0.24% |
| 4096 | -0.07% | -0.22% | +0.03% |

**v4 -> v5 (`91b1ce25`): TAIL odd-block mids ins+pmull2 -> ext+pmull**

| size | GV3 / V1 | GV4 / V2 | GV5 / V3 |
|---|---|---|---|
| 128 | -1.45% | -0.72% | -0.31% |
| 256 | -1.08% | -0.50% | -0.06% |
| 512 | -0.30%~ | -0.50%~ | +0.01%~ |
| 1024 | +0.22% | -0.02%~ | -0.02%~ |
| 4096 | -0.07% | +0.06%~ | +0.02% |

**Cumulative baseline -> HEAD, side by side**

| size | GV3 / V1 | GV4 / V2 | GV5 / V3 |
|---|---|---|---|
| 128 | 0.791 (+20.9%) | 0.786 (+21.4%) | 0.827 (+17.3%) |
| 256 | 0.845 (+15.5%) | 0.837 (+16.3%) | 0.863 (+13.7%) |
| 512 | 0.902 (+9.8%) | 0.890 (+11.0%) | 0.913 (+8.7%) |
| 1024 | 0.950 (+5.0%) | 0.946 (+5.4%) | 0.947 (+5.3%) |
| 4096 | 0.987 (+1.3%) | 0.985 (+1.5%) | 0.986 (+1.4%) |

### GV4 version-5 at 128 B (harness cross-check)

GV4 (Neoverse-V2, c8g.4xlarge) measures v5 at 128 B = **25.492 ns/call**.

## Verdict on the cross-core hypothesis

Hypothesis under test: these commits are mostly false-dependency and dependency-depth
fixes, so they should pay most on Neoverse-V1 and least on V3.

**Partly confirmed. It holds for the two `ins`->`ext` commits (1 and 5) and for the cumulative
short-message picture; it is refuted for commit 4, which pays *more* on V2/V3 than on V1.**

Evidence, at the short sizes where the tail/setup code is a large fraction of the call:

| commit | 128 B: V1 / V2 / V3 | 256 B: V1 / V2 / V3 | monotone V1>V2>V3? |
|---|---|---|---|
| v1 (`51a51943`) | -12.96% / -11.16% / -8.47% | -10.70% / -10.60% / -8.81% | yes |
| v2 (`8ca8a201`) | -2.70% / -3.60% / -3.17% | -2.29% / -1.13% / -1.53% | no |
| v3 (`6f144724`) | -2.49% / -3.87% / -2.49% | -1.13% / -1.72% / -1.09% | no |
| v4 (`fc42a21a`) | -2.86% / -3.86% / -3.99% | -0.96% / -3.12% / -2.80% | no |
| v5 (`91b1ce25`) | -1.45% / -0.72% / -0.31% | -1.08% / -0.50% / -0.06% | yes |

Reading:

* **Commit 1 (`ins`->`ext` in the GHASH tail mids)** is by far the largest single win and it does
  shrink V1 -> V3 at short sizes: -12.96% / -11.16% / -8.47% at 128 B. This is the classic
  false-dependency signature: `ins v18.d[0], v24.d[1]` reads-modifies-writes v18, so it
  serialises on the previous writer of v18; `ext` writes the whole register. V1's narrower
  rename/dependency handling suffers most, V3 least. Confirmed.
* **Commit 5 (TAIL odd-block mids `ins`+`pmull2` -> `ext`+`pmull`)** is the same transformation
  applied to the odd-block tail, and shows the same ordering, but an order of magnitude smaller:
  -1.45% / -0.72% / -0.31% at 128 B and -1.08% / -0.50% / -0.06% at 256 B. So the
  encrypt analogue's -4.4% on V1 vs -0.6..-0.75% on V2 is **not** reproduced in magnitude for
  decrypt (V1 gets only ~-1.1..-1.5%), but the V1 >> V2 > V3 *ordering* is reproduced exactly.
  On V3 its largest effect anywhere is -0.31% (128 B) and it is at or below the floor from
  512 B up: effectively a wash on Neoverse-V3.
* **Commit 4 (flatten SETUP counter chain, depth 7->2)** refutes the hypothesis: it pays
  *least* on V1 (-2.86% at 128 B, -0.96% at 256 B) and most on V2/V3 (-3.86%/-3.99% at 128 B,
  -3.12%/-2.80% at 256 B). That is consistent with it being a pure latency-chain shortening
  rather than a false-dependency fix: the wider, deeper V2/V3 cores can exploit the extra
  independent counter work immediately, whereas on V1 the surrounding AES round work is
  already the binding constraint, so shortening the counter chain buys less.
* **Commits 2 and 3 (exact-8 GHASH drain, then `eor3`-fusing its accumulate chains)** show no
  monotone cross-core trend: 2 is -2.70/-3.60/-3.17% and 3 is -2.49/-3.87/-2.49% at 128 B.
  Both are work-*removal* / instruction-count reductions rather than dependency fixes, so they
  pay roughly equally on all three cores, with V2 slightly favoured. Neither is core-specific.

### Size dependence (all hosts agree)

Verified structurally: diffing every version against the baseline shows **zero hunks between the
`.L256_dec_main_loop` label and the end of `.L256_dec_prepretail`** - all six versions have a
bit-identical 8-block mainloop and prepretail; every change lives in SETUP (before the first
mainloop entry) or in TAIL (`.L256_dec_tail` onwards). So the whole
effect amortises away with message length: the cumulative win is ~+17..21% at 128 B, ~+14..16%
at 256 B, ~+9..11% at 512 B, ~+5% at 1024 B and only ~+1.4% at 4096 B, essentially identically
on all three cores. At 4096 B (256 blocks) most commits are at or near the noise floor.

## Negative and noise-level results, stated plainly

* Commit 5 measures **+0.22% (slower) at 1024 B on GV3/V1** and **+0.06% at 4096 B on GV4/V2**,
  and **+0.01%/+0.02% at 512/4096 B on GV5/V3**. These are at or barely above the floor; the
  honest reading is that commit 5 is a wash at >=512 B on every core, and only a real win at
  128-256 B on V1 and V2.
* Commit 4 measures **+0.24% at 1024 B and +0.03% at 4096 B on GV5/V3** - slower, above the
  0.07%/0.01% floor at those sizes. So commit 4's win on V3 is confined to <=512 B.
* Commit 2 at 1024 B on GV4/V2 (-0.28%) is below that host+size floor: noise there.
* Commit 3 at 4096 B on GV4/V2 (-0.07%) is below the floor: noise there.
* The **512-byte column has a visibly worse A/A floor than its neighbours** on GV3 (0.61%) and
  GV5 (0.69%) - two byte-identical code copies differ by that much - while 128/256/1024/4096 B
  are all <=0.3%. 512 B = 32 blocks = exactly 4 mainloop iterations plus an empty tail, and it
  appears to sit on a code-placement/alignment cliff. Treat sub-1% 512 B deltas with suspicion.
* No version was ever slower than its predecessor by more than 0.24% anywhere, so there is no
  regression to chase - only diminishing returns.

## Harness-consistency cross-check: version 5 at 128 B on Neoverse-V2

| source | ns/call |
|---|---|
| this harness, GV4 c8g.4xlarge, min of 10 x best-of-200 | **25.492** |
| independent measurement, different V2 host | 25.589 |
| project benchmark doc | 27.98 |

This harness lands within **0.38%** of the independent V2 figure (25.589 ns), and both differ
from the project doc's 27.98 ns by ~9%. Two independent harnesses on two different V2 hosts
agreeing to 0.4% is strong evidence that **~25.5 ns is the trustworthy figure** and the 27.98 ns
in the project doc is inflated - most plausibly by the project harness's averaging over
bit-density groups and its per-call setup (key/Htable/Xi/ivec re-initialisation inside the
timed helper) rather than by any difference in the kernel. Note this host is a 4xlarge, but
instance size affects clock/uncore, not a 9% single-core delta of this shape.

## Reproduction

Harness and raw output live under `/tmp/pcbench` on this workstation and on each of the three
hosts (nothing was written into any git repo on any host):

* `/tmp/pcbench/src/<commit>.S` - the six extracted kernels
* `/tmp/pcbench/harness.c` - interleaved timing + correctness harness
* `/tmp/pcbench/build.sh` - assemble, `objcopy --redefine-sym`, link one binary
* `/tmp/pcbench/out_GV{3,4,5}.txt` - raw `RES` lines, 10 runs per host
* `/tmp/pcbench/analyze.py` - generates this report

