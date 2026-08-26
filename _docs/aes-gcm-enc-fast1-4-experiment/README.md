# AES-256-GCM small-path code-size experiment

Measurement date: 2026-08-26. This branch is based on `aes-gcm-dec-clean` at
`29c532644f8f1ac0c0a5ae520a06768ebcb4ac3f`.

## Decision

Keeping Mila's final `fast1` through `fast4` encrypt paths and removing
`fast5` through `fast7` produces an 8,624-byte kernel. It is 1.72x the
optimized pre-fast-path baseline and 1.85x AWS-LC's original 8x kernel, so it
meets a strict "less than 2x original" constraint. The full kernel is 11,848
bytes, 2.37x and 2.54x those respective baselines.

The compact kernel preserves the full kernel's performance at 16--64 and
128 bytes. At the omitted 80/96/112-byte sizes it is 13--26% slower than full,
although it remains 10--20% faster than AWS-LC's 4x kernel in the pure-kernel
harness. This is a defensible code-size compromise if staying below 2x is a
hard constraint; it is not free performance.

Use the s2n-bignum in-tree harness as the primary variant-to-variant result:
it embeds each kernel at the same executable offset and reproduced Mila's G3
full-kernel results. Use the co-linked harness as the pure-kernel and reference
cross-check: it has a nanosecond timer, real key/H-table initialization, strong
differential checks, and compares all kernels in one process, but each co-linked
kernel necessarily has a different address. Neither harness measures production
AWS-LC EVP/AEAD behavior or instruction-cache pressure from mixed application
code; that is the final acceptance benchmark.

## Construction and correctness

The full source is Mila's `aes_gcm_256_x8_verbose_opt` at
`c262508d0e792f23bc45c8395f2904fb3a5d10d1`. The benchmark tree and her report
are from `aes_gcm_256_x8_verbose_opt_bench` at
`d19155150baf043412094be24b67eb17629e9aab`.

- [`full-fast1-7.S`](src/full-fast1-7.S) is the final proved kernel.
- [`compact-fast1-4.S`](src/compact-fast1-4.S) is generated from it by
  [`make_compact.awk`](harness/make_compact.awk), removing only the three
  dispatch pairs and contiguous `fast5`--`fast7` bodies.
- [`baseline.S`](src/baseline.S) retains the common optimizations but predates
  the per-size fast paths. The AWS-LC references are
  [`awslc-8x.S`](src/awslc-8x.S) and [`awslc-4x.S`](src/awslc-4x.S).

The generator reproduces the checked-in compact source byte-for-byte. On all
three hosts every object assembled successfully, and
[`bench.c`](harness/bench.c) compared output, Xi, counter, and return value
against the baseline for every whole-block length from 1 through 256 blocks.
All seven variants agreed. The full source retains Mila's completed HOL Light
proof. The compact source is **measurement-only** until the top-level proof
dispatch is reduced to `fast1`--`fast4` and the proof is rerun.

| object | `.text` | vs optimized baseline | vs AWS-LC original |
|---|---:|---:|---:|
| AWS-LC original 8x | 4,672 B | 0.93x | 1.00x |
| optimized pre-fast baseline | 5,008 B | 1.00x | 1.07x |
| compact `fast1`--`fast4` | **8,624 B** | **1.72x** | **1.85x** |
| full `fast1`--`fast7` | 11,848 B | 2.37x | 2.54x |

The compact choice saves 3,224 bytes, or 27.2% of the full kernel.

## Encrypt results

Instances were c7g.2xlarge/G3 (Neoverse V1), c8g.4xlarge/G4 (V2), and
c9g.4xlarge/G5 (V3), pinned to CPU 3.

### In-tree harness

Each source was swapped into Mila's exact benchmark tree, rebuilt through
`arm/Makefile`, and linked into a separate benchmark binary. Object bytes were
found in every executable at the same file offset, `0xf824c`. The full and
full-A/A binaries were byte-identical. The table is median ns/call over three
complete round-robin rounds with 1,000 inner repetitions; each cell is
`compact / full`.

| bytes | G3 | G4 | G5 |
|---:|---:|---:|---:|
| 16 | 30.4 / 30.4 | 22.4 / 22.6 | 15.7 / 15.7 |
| 32 | 32.4 / 32.3 | **24.4 / 25.4** | 17.2 / 17.2 |
| 48 | 33.7 / 33.7 | 26.4 / 26.4 | 20.3 / 20.3 |
| 64 | 34.6 / 34.7 | 28.4 / 28.5 | 22.1 / 22.1 |
| 80 | 43.4 / **37.5** | 34.9 / **30.1** | 27.8 / **23.7** |
| 96 | 44.3 / **39.1** | 35.9 / **32.0** | 28.3 / **25.0** |
| 112 | 45.5 / **41.1** | 37.4 / **33.9** | 29.0 / **26.5** |
| 128 | 43.1 / 43.0 | 35.9 / 35.9 | 27.6 / 27.7 |

Mila reported 30.0/32.0/33.4/34.4/37.2/39.0/40.9/42.7 ns for the full kernel
on G3. This campaign reproduced that curve within 0.0--0.9 ns. The repeatable
G4 32-byte compact advantage (about 4%) did not appear on G3/G5 or at that
magnitude in the co-linked harness. It is likely a V2 layout/branch-target
effect and should be confirmed with the default 10,000 inner repetitions before
being treated as part of the compromise.

### Co-linked harness

The co-linked run used 160 rotated repetitions, five processes, a
`CLOCK_MONOTONIC` timer, and baseline/compact A/A slots. Each cell is
`compact vs full / compact vs AWS-LC 4x`, using the median process timing.
Negative is faster.

| bytes | G3 | G4 | G5 |
|---:|---:|---:|---:|
| 16 | -0.5% / -22.4% | -0.3% / -27.7% | +0.3% / -32.5% |
| 32 | -0.8% / -24.0% | -0.3% / -29.0% | -0.1% / -37.2% |
| 48 | -0.2% / -12.1% | -0.9% / -16.3% | +0.0% / -24.6% |
| 64 | -1.1% / -15.1% | -0.5% / -11.5% | -0.0% / -19.6% |
| 80 | **+26.3%** / -10.3% | **+24.6%** / -14.5% | **+25.4%** / -16.3% |
| 96 | **+21.0%** / -13.0% | **+20.3%** / -15.8% | **+19.9%** / -20.1% |
| 112 | **+14.9%** / -15.9% | **+14.1%** / -16.8% | **+12.9%** / -20.0% |
| 128 | -0.2% / -23.7% | +0.2% / -26.6% | +0.0% / -25.4% |

The worst compact A/A difference over these sizes was 2.0% on G3, 1.1% on G4,
and 0.3% on G5. The 13--26% omitted-path effects are well outside that floor.
Raw data: [`custom-g3.log`](results/custom-g3.log),
[`custom-g4.log`](results/custom-g4.log), and
[`custom-g5.log`](results/custom-g5.log). In-tree data:
[`intree-g3.log`](results/intree-g3.log),
[`intree-g4.log`](results/intree-g4.log), and
[`intree-g5.log`](results/intree-g5.log).

## Encrypt and decrypt compromise

The earlier decrypt experiment reached the same code-size warning by a
different route. Eight exact-size decrypt bodies grew `.text` from 4,968 to
12,376 bytes (2.49x) and delivered approximately -47/-43/-44/-41/-36/-30/-24/
-10% at 16 through 128 bytes on G4. Truncating at four bodies cost 7,312 bytes
(1.47x) and retained the first four gains only. The chosen decrypt design did
better: a shared one-block cascade for 1--4 blocks is 5,960 bytes (1.20x);
after ordering work its 64-byte gain versus the pre-fused kernel was
-21.9/-27.2/-31.0% on G3/G4/G5, with larger lengths unchanged.

| direction/design | `.text` | growth | accelerated sizes | key result |
|---|---:|---:|---|---|
| encrypt full per-size | 11,848 B | 2.54x original | 16--112 B | best fixed-size speed |
| **encrypt compact per-size** | **8,624 B** | **1.85x original** | **16--64 B** | full speed at retained sizes; still beats 4x at 80--112 B |
| decrypt full per-size | 12,376 B | 2.49x | 16--128 B | rejected on shape/code size |
| decrypt truncated per-size C=4 | 7,312 B | 1.47x | 16--64 B | clean partial-adoption curve |
| **decrypt chosen shared 1--4** | **5,960 B** | **1.20x** | **16--64 B** | much better code reuse |

Decrypt can GHASH input ciphertext while AES produces plaintext, which made a
shared cascade effective. Encrypt must GHASH ciphertext produced by AES, so
the dependency structure makes Mila's unbraided exact-width setup and dedicated
drains more valuable and harder to share without losing speed. The decrypt
1.20x result therefore should not be assumed achievable for encrypt.

## Reproduction

[`build-custom.sh`](harness/build-custom.sh) assembles and links the co-linked
binary; [`run-custom.sh`](harness/run-custom.sh) runs it. The crypto helper
object is built from AWS-LC's `aesv8-armx.S` and `ghashv8-armx.S`.

[`build-intree.sh`](harness/build-intree.sh) expects a
`mila-benchmark-tree.tgz` made with:

```sh
git archive --format=tar.gz -o mila-benchmark-tree.tgz \
  mila/aes_gcm_256_x8_verbose_opt_bench
```

It builds all four same-offset binaries and validates embedded kernel bytes.
Run three interleaved rounds with:

```sh
harness/run-intree.sh /tmp/intree-enc-fast1-4 3 1000 3
```

Before choosing the compact kernel, run an AWS-LC EVP/AEAD mixed-size workload
with the intended 16-byte dispatch threshold. That is the measurement that can
show whether saving 3.2 KB offsets the 80--112-byte fixed-size loss through
better instruction-cache behavior in production.
