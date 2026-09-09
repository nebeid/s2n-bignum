# AES-256-GCM small-path code-size experiment

Initial measurement date: 2026-08-26; final 8x Pareto rerun: 2026-09-08.
This branch is based on `aes-gcm-dec-clean` at
`29c532644f8f1ac0c0a5ae520a06768ebcb4ac3f`.

## Decision

The final 8x choice is the 7,504-byte **shared-setup, parallel
`fast1`--`fast4`** kernel. It retains Mila's four width-specific parallel AES
schedules, but shares entry setup and final GHASH reduction, constructs final
counters directly, and removes unreachable older bodies. It is 1.50x the
5,008-byte optimized baseline and 1.61x AWS-LC's 4,672-byte original 8x
kernel.

Against the 8,624-byte compact control, the new result is 1,120 bytes smaller
and faster at every measured 16--64 B point on G3--G5. Its geometric-mean
advantage is 6.76% on G3, 6.54% on G4, and 8.88% on G5. The existing main loop
and common tails are byte-identical. Construction, KAT/differential checks,
all measurements, and logs are in the
[AES-256-GCM 4x experiment report](aes256-gcm-4x-experiment/README.md#final-8x-shared-setup-with-parallel-1--4-block-bodies).

The 5,140-byte 4x shared-entry result remains the smaller choice. It is
competitive with compact 8x through 48 B, then returns to `late_tag` at 64 B.
Use it when saving another 2,364 bytes matters more than 64 B latency.

The original full-versus-compact experiment below remains useful provenance.
Compact preserves full's performance at 16--64 and 128 B, and is 13--26%
slower at the omitted 80/96/112 B sizes. The full kernel is 11,848 bytes.

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
- The final follow-up source is
  [`x8-enc-pareto-full.S`](aes256-gcm-4x-experiment/src/x8-enc-pareto-full.S);
  its build, KAT, differential gates, and logs are in the same directory.

The generator reproduces the checked-in compact source byte-for-byte. On all
three hosts every object assembled successfully, and
[`bench.c`](harness/bench.c) compared output, Xi, counter, and return value
against the baseline for every whole-block length from 1 through 256 blocks.
All seven variants agreed. The full source retains Mila's completed HOL Light
proof. The compact source is **measurement-only** until the top-level proof
dispatch is reduced to `fast1`--`fast4` and the proof is rerun. The final
shared-setup candidate is also a measurement artifact without a HOL proof.

| object | `.text` | vs optimized baseline | vs AWS-LC original |
|---|---:|---:|---:|
| AWS-LC original 8x | 4,672 B | 0.93x | 1.00x |
| optimized pre-fast baseline | 5,008 B | 1.00x | 1.07x |
| **shared-setup parallel `fast1`--`fast4`** | **7,504 B** | **1.50x** | **1.61x** |
| compact `fast1`--`fast4` | **8,624 B** | **1.72x** | **1.85x** |
| full `fast1`--`fast7` | 11,848 B | 2.37x | 2.54x |

The final shared-setup choice saves 1,120 bytes versus compact and 4,344 bytes
versus full. The earlier compact choice by itself saves 3,224 bytes, or 27.2%
of the full kernel.

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
(1.47x) and retained the first four gains only. Retaining bodies 1--4 and 8
instead cost 8,832 bytes (1.78x), retained the first four gains and the
approximately 10% 128-byte gain, and left 80--112 bytes unchanged. The current
PR uses a shared one-block cascade for 1--4 blocks at 5,960 bytes
(1.20x); after ordering work its 64-byte gain versus the pre-fused kernel was
-21.9/-27.2/-31.0% on G3/G4/G5, with larger lengths unchanged.

| direction/design | `.text` | growth | accelerated sizes | key result |
|---|---:|---:|---|---|
| encrypt full per-size | 11,848 B | 2.54x original | 16--112 B | best fixed-size speed |
| **encrypt shared-setup parallel 1--4** | **7,504 B** | **1.61x original** | **16--64 B** | smaller and faster than compact at retained sizes; preserved main loop |
| **encrypt compact per-size** | **8,624 B** | **1.85x original** | **16--64 B** | full speed at retained sizes; still beats 4x at 80--112 B |
| decrypt full per-size | 12,376 B | 2.49x | 16--128 B | largest code/proof cost |
| decrypt per-size `{1,2,3,4,8}` (`t4p8`) | 8,832 B | 1.78x | 16--64 B, 128 B | full per-size speed at retained sizes |
| decrypt truncated per-size C=4 | 7,312 B | 1.47x | 16--64 B | clean partial-adoption curve |
| decrypt current shared 1--4 | 5,960 B | 1.20x | 16--64 B | shared code across four sizes |

### Decrypt equivalent of the compact encrypt experiment

There are two useful decrypt comparisons. The contiguous `t4` variant is the
literal four-body truncation: it retains exact-size bodies for 16--64 bytes,
costs 7,312 bytes (1.47x), and leaves every larger length on the existing path.
It does not retain the full decrypt experiment's faster body 8.

The performance-equivalent analogue of compact encrypt is `t4p8`: exact-size
bodies `{1,2,3,4,8}` for 16--64 and 128 bytes. It costs 8,832 bytes (1.78x),
retains the full eight-body decrypt variant's performance at all five selected
sizes, and leaves 80, 96, and 112 bytes on the existing path. This matches the
compact encrypt result in outcome, although not in assembly shape: encrypt has
no separate `fast8` body, because its retained common 8-wide path and dedicated
`exact8` drain already match the full encrypt kernel at 128 bytes.

| bytes | G3 / V1 vs pre-fusion | G4 / V2 vs pre-fusion | G5 / V3 vs pre-fusion |
|---:|---:|---:|---:|
| 16 | -46.86% | -47.27% | -46.27% |
| 32 | -43.84% | -42.83% | -42.40% |
| 48 | -43.56% | -43.48% | -44.92% |
| 64 | -41.29% | -40.81% | -42.01% |
| 128 | -9.72% | -9.95% | -8.61% |

The current PR's shared 1--4-block path is 5,960 bytes. In the PR's in-tree
rerun, the separate-body implementation measured the following additional
change relative to that path at the five `t4p8` sizes:

| bytes | G3 / V1 | G4 / V2 | G5 / V3 |
|---:|---:|---:|---:|
| 16 | -7.26% | -2.92% | -0.70% |
| 32 | -3.44% | -5.58% | -2.87% |
| 48 | -7.93% | -8.04% | -5.03% |
| 64 | -14.09% | -12.11% | -4.90% |
| 128 | -5.76% | -3.91% | -2.87% |

These in-tree incremental percentages come from the eight-body object, whose
retained bodies are the same exact-size designs. The separately measured
`t4p8` object reproduced the full object's 128-byte gain to 0.08 percentage
points against the placement-matched control. It adds 2,872 bytes over the
shared-path object; `t4` adds 1,352 bytes but does not target 128 bytes.

The decrypt measurements and construction are preserved in the
[`t4p8` report](https://github.com/nebeid/s2n-bignum/blob/aes-gcm-fused-wip/_docs/fused-t4p8.md)
and its
[`gen_set.py` generator](https://github.com/nebeid/s2n-bignum/blob/aes-gcm-fused-wip/_docs/fused-t4p8/gen_set.py).
The encrypt inputs are Mila's
[`aes_gcm_256_x8_verbose_opt`](https://github.com/manastasova/s2n-bignum-dev/tree/aes_gcm_256_x8_verbose_opt)
source branch and
[`aes_gcm_256_x8_verbose_opt_bench`](https://github.com/manastasova/s2n-bignum-dev/tree/aes_gcm_256_x8_verbose_opt_bench)
benchmark branch; complete source snapshots are also committed under
[`src/`](src/).

Decrypt can GHASH input ciphertext while AES produces plaintext, which made a
shared cascade effective. Encrypt must GHASH ciphertext produced by AES, so
the dependency structure makes Mila's unbraided exact-width setup and dedicated
drains more valuable and makes the same serial cascade slow. The final encrypt
result instead retains all four parallel schedules and shares setup and final
reduction. It reaches 1.61x the original size, not decrypt's 1.20x, while
improving on compact's short-message performance.

## AES-256-GCM 4x experiment

### Exact comparison controls

The G3--G5 encrypt control is the 8,624-byte
[compact `fast1`--`fast4` 8x snapshot](aes256-gcm-4x-experiment/src/x8-enc-compact.S),
generated from Mila's
[`aesv8_gcm_8x_enc_256.S`](https://github.com/manastasova/s2n-bignum-dev/blob/c262508d0e792f23bc45c8395f2904fb3a5d10d1/arm/aes-gcm/aesv8_gcm_8x_enc_256.S).
It is a hand-optimized, hand-scheduled AWS-LC-derived 8-way kernel with
separate 1-, 2-, 3-, and 4-block paths; it is not SLOTHY-generated.

The G3--G5 decrypt control is the 5,960-byte fused 1--4-block
`aesv8_gcm_8x_dec_256_wb` from
[s2n-bignum PR 445](https://github.com/awslabs/s2n-bignum/pull/445), pinned to
[`29c532644`](https://github.com/nebeid/s2n-bignum/blob/29c532644f8f1ac0c0a5ae520a06768ebcb4ac3f/arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S).
It is also hand-optimized rather than SLOTHY-generated. Both 8x controls use
SHA3-extension `EOR3` and were run unchanged only on G3--G5; the G2 large-message
8x screen used mechanically expanded adaptations.

The fixed 4x candidates come from Hanno Becker's
[`aarch64_aes_gcm_slothy`](https://github.com/hanno-becker/aws-lc/tree/aarch64_aes_gcm_slothy)
branch at
[`83d5627a`](https://github.com/hanno-becker/aws-lc/commit/83d5627a1d4315a71057fe6bc75900e080f255be):

- encrypt `scalar_iv_mem_late_tag_scalar_rk`, Hanno's best sustained G2
  candidate from about 2 KiB through 32 KiB;
- decrypt `basic`, Hanno's fastest committed decrypt candidate;
- generated decrypt `fast_tail`, which reuses Hanno's optimized `basic`
  preamble and software-pipelined body and adds independently N1/SLOTHY-
  scheduled fused 1-, 2-, and 3-block tails.

Hanno's committed 4x encrypt and decrypt kernels are N1 SLOTHY outputs with
software-pipelined main loops. Generated decrypt `fast_tail` is not one of his
committed outputs, but its unchanged main loop and its added tails are also
N1/SLOTHY-scheduled.

### Final result

The recommended encrypt construction is a 5,140-byte 4x shared entry: fused
`fast_tail` bodies for 16, 32, and 48 B, followed by Hanno's unchanged
`late_tag` setup and loop at 64 B and above. It is 3,484 bytes smaller than
compact 8x. Against compact 8x over 16--48 B, it is tied on G3 and faster on
G4 and G5:

| geometric-mean 4x shared-entry advantage over compact 8x | G3 | G4 | G5 |
|---|---:|---:|---:|
| 16--48 B | +0.01% | +5.62% | +4.90% |

The conclusion is **competitive through 48 B, not through 64 B**. Compact 8x
has a dedicated `fast4` path; the measured 4x shared entry does not. The older
16--128 B table comparing compact 8x with bare 4x `late_tag` is only a baseline
showing why an encrypt short path was needed.

For decrypt, generated 4x `fast_tail` is 964 bytes (49.6%) larger than Hanno
`basic` and was 9.6% faster by geometric-mean latency over 16--128 B on G2.
Its G3--G5 results are:

| geometric-mean comparison over 16--128 B | G3 | G4 | G5 |
|---|---:|---:|---:|
| 4x decrypt `fast_tail` advantage over 4x `basic` | 14.7% | 15.4% | 16.6% |
| PR-445 8x advantage over 4x `fast_tail` | 1.7% | 0.8% | -1.1% |

Every process passed output/state differential checks from 1 through 256
blocks before timing. Full per-size tables, detailed scheduling provenance,
generated source, scripts, object hashes, and raw logs are in the
[`AES-256-GCM 4x experiment`](aes256-gcm-4x-experiment/README.md).

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
