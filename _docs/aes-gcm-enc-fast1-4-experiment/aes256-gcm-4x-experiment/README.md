# AES-256-GCM 4x experiment

## Candidates and provenance

This report evaluates three AES-256-GCM 4x kernels:

- **Encrypt `scalar_iv_mem_late_tag_scalar_rk`**: Hanno Becker's best
  sustained-throughput encrypt candidate on Graviton2 from about 2 KiB through
  32 KiB.
- **Decrypt `basic`**: Hanno's fastest existing optimized AES-256 decrypt
  candidate at every size in his committed Graviton2 table.
- **Decrypt `fast_tail`**: generated during this experiment to combine Hanno's
  optimized `basic` body with dedicated short-message tails.

Hanno's committed candidates come from the
[`aarch64_aes_gcm_slothy`](https://github.com/hanno-becker/aws-lc/tree/aarch64_aes_gcm_slothy)
branch, pinned at
[`83d5627a`](https://github.com/hanno-becker/aws-lc/commit/83d5627a1d4315a71057fe6bc75900e080f255be).
The branch's
[`slothy` directory](https://github.com/hanno-becker/aws-lc/tree/83d5627a1d4315a71057fe6bc75900e080f255be/crypto/fipsmodule/modes/asm/slothy)
contains the clean inputs, optimization script, generated outputs, and
Graviton2 measurements.

Both Hanno kernels are outputs of `optimize_x4()`, which invokes SLOTHY with
software pipelining enabled for Neoverse N1, the Graviton2 core. Their
steady-state x4 loops have 70-cycle SLOTHY estimates.

## Generated decrypt `fast_tail`

Hanno's branch contains a clean decrypt `fast_tail` input but no optimized
output for it. The
[`fast_tail` generated here](src/aesv8-gcm-armv8-dec-opt-256_x4_fast_tail.S)
is therefore **not one of Hanno's committed optimized kernels**.

It was constructed as follows:

1. Reuse the preamble and software-pipelined 4-block loop from Hanno's
   N1/SLOTHY-optimized decrypt `basic`.
2. Keep that body instruction-for-instruction identical through
   `Lloop_unrolled_end`.
3. Independently schedule the fused 1-, 2-, and 3-block tails with SLOTHY's
   Neoverse N1 model.
4. Differentially check output, authentication state, counter state, and
   return value for every length from 1 through 256 blocks.

Thus `fast_tail` is optimized specifically for Graviton2/N1: its main loop is
Hanno's N1 software-pipelined loop, while its finite tails are separately
N1/SLOTHY-scheduled straight-line code.

The cost is code size:

| decrypt 4x kernel | `.text` bytes | change |
|---|---:|---:|
| Hanno `basic` | 1,944 | baseline |
| generated `fast_tail` | 2,908 | +964 B / +49.6% |

On G2, `fast_tail` improved geometric-mean latency over 16--128 B by 9.6%:

| bytes | `basic` ns | `fast_tail` ns | `fast_tail` change |
|---:|---:|---:|---:|
| 16 | 19.003 | 17.303 | -8.9% |
| 32 | 30.405 | 24.904 | -18.1% |
| 48 | 41.605 | 31.605 | -24.0% |
| 64 | 40.806 | 41.206 | +1.0% |
| 80 | 51.989 | 51.607 | -0.7% |
| 96 | 63.197 | 57.587 | -8.9% |
| 112 | 74.764 | 64.010 | -14.4% |
| 128 | 69.010 | 69.428 | +0.6% |

The raw G2 run is
[`g2-dec-opt-fasttail-ip-172-31-11-58.log`](results/g2-dec-opt-fasttail-ip-172-31-11-58.log).
Because the 4-block body is identical, `fast_tail` does not improve sustained
large-message throughput. It only removes fixed tail overhead for lengths
ending in 1--3 blocks, so its percentage benefit approaches zero as messages
grow.

## Fixed G3--G5 short-message rerun

The selected kernels were rerun without reselection on:

- G3: `c7g.2xlarge`, Neoverse V1;
- G4: `c8g.4xlarge`, Neoverse V2;
- G5: `c9g.4xlarge`, Neoverse V3.

The encrypt comparison used compact 8x versus Hanno's
`scalar_iv_mem_late_tag_scalar_rk`. The decrypt comparison used the
live-PR-equivalent 8x kernel versus Hanno `basic` and generated `fast_tail`.
Positive percentages mean the first named kernel is faster.

### Encrypt: compact 8x advantage over 4x `late_tag`

| bytes | G3 / V1 | G4 / V2 | G5 / V3 |
|---:|---:|---:|---:|
| 16 | +48.1% | +51.9% | +53.7% |
| 32 | +54.5% | +59.6% | +62.2% |
| 48 | +53.5% | +57.9% | +61.1% |
| 64 | +49.6% | +48.3% | +48.9% |
| 80 | +38.5% | +39.4% | +39.3% |
| 96 | +45.5% | +46.3% | +47.3% |
| 112 | +50.9% | +51.5% | +52.9% |
| 128 | +36.0% | +41.1% | +43.7% |

The compact 8x geometric-mean advantage is **47.4% on G3, 50.0% on G4,
and 51.7% on G5**. Hanno's large-message G2 winner is therefore not a
competitive short-message fallback on these three cores.

### Decrypt: generated `fast_tail` advantage over `basic`

| bytes | G3 / V1 | G4 / V2 | G5 / V3 |
|---:|---:|---:|---:|
| 16 | +1.2% | -0.2% | -0.2% |
| 32 | +31.2% | +36.3% | +36.6% |
| 48 | +39.6% | +40.3% | +46.5% |
| 64 | +0.6% | -1.2% | -0.4% |
| 80 | +0.9% | +0.3% | -0.5% |
| 96 | +11.7% | +12.4% | +12.6% |
| 112 | +20.2% | +20.8% | +21.4% |
| 128 | +1.1% | +1.3% | +0.2% |

The `fast_tail` geometric-mean advantage over `basic` is **14.7% on G3,
15.4% on G4, and 16.6% on G5**.

### Decrypt: 8x advantage over generated 4x `fast_tail`

| bytes | G3 / V1 | G4 / V2 | G5 / V3 |
|---:|---:|---:|---:|
| 16 | -13.4% | -12.7% | -11.2% |
| 32 | -5.5% | -11.2% | -12.0% |
| 48 | -7.3% | +2.7% | -2.9% |
| 64 | +7.0% | +3.0% | +4.6% |
| 80 | -2.6% | -7.8% | -11.7% |
| 96 | +4.6% | -0.7% | -4.1% |
| 112 | +5.7% | +7.2% | +4.9% |
| 128 | +20.9% | +21.4% | +19.3% |

Across 16--128 B, 8x is only **1.7% faster on G3 and 0.8% faster on G4**;
generated 4x `fast_tail` is **1.1% faster on G5**. These aggregate differences
are small enough to require an application-level code-placement benchmark
before choosing between them.

Raw logs:

- [G3 / V1](results/selected-ip-172-31-4-159.log)
- [G4 / V2](results/selected-ip-172-31-44-56.log)
- [G5 / V3](results/selected-ip-172-31-42-229.log)

The fixed rerun is reproduced by
[`build-selected-g3-g5.sh`](build-selected-g3-g5.sh) and
[`run-selected-g3-g5.sh`](run-selected-g3-g5.sh).

## Graviton2 large-message screening

Hanno's committed G2 measurements select:

- encrypt `scalar_iv_mem_late_tag_scalar_rk` from about 2 KiB through 32 KiB;
- decrypt `basic` at every reported size.

A fixed-source G2 follow-up confirmed that selection. The encrypt kernel
overtook `basic` at 1344 B and was 1.36% faster at 32 KiB. Decrypt `basic`
remained fastest. A mechanically G2-compatible AWS-LC 8x graph was not an
improvement:

| bytes | enc selected | enc `basic` | enc 8x | dec selected | dec control | dec 8x |
|---:|---:|---:|---:|---:|---:|---:|
| 1344 | 608.501 | 609.402 | 707.816 | 604.880 | 618.657 | 721.670 |
| 2048 | 918.580 | 923.714 | 1071.251 | 912.997 | 932.906 | 1051.508 |
| 4096 | 1818.163 | 1836.196 | 2086.641 | 1812.666 | 1847.902 | 2092.675 |
| 8192 | 3617.888 | 3660.757 | 4117.461 | 3612.463 | 3677.378 | 4175.043 |
| 16384 | 7216.050 | 7311.222 | 8179.604 | 7212.138 | 7338.317 | 8340.305 |
| 32768 | 14419.260 | 14616.020 | 16305.560 | 14459.413 | 14713.358 | 16671.167 |

At 32 KiB, that 8x adaptation was 13.08% slower for encrypt and 15.30%
slower for decrypt. It expands each Armv8.4 `EOR3` into two `EOR`
instructions and is not a purpose-built N1 8x design. The
[raw G2 log](results/g2-large-ip-172-31-11-58.log) records object hashes and
all measurements.

## Earlier candidate screen

Before the fixed rerun, all seven Hanno AES-256 encrypt candidates and both
committed decrypt candidates were screened on G2 over 16--128 B:

- encrypt `fast_tail` was the best fixed small-message candidate by geometric
  mean, 17.6% faster than encrypt `basic`;
- decrypt `basic` beat `scalar_iv_mem2_late_tag` at every size.

That earlier screen explains why previous G3--G5 tables used encrypt
`fast_tail`. It was a small-message experiment selection, not Hanno's
large-message recommendation. The fixed rerun above deliberately measures the
large-message encrypt candidate likely to be considered for AWS-LC.

## Method

- Sizes: every whole-block length from 16 through 128 B.
- Timing: CPU 3, 160 interleaved samples per size, rotated variant order, and
  seven independent processes. Each table uses the median of process medians.
- Correctness: each process first compared output, Xi, ivec, and return value
  for every length from 1 through 256 blocks.
- Inputs: identical real AES-256 key schedule and H-power table in one process.
- Scope: raw kernels only; AEAD setup, dispatch, tag finalization, and caller
  overhead are excluded.

Differences around 1% should be treated as a wash because no code-placement
A/A campaign was included.

## Additional artifacts

- Existing multi-candidate analyzer: [`analyze.py`](analyze.py)
- Original broad build: [`build.sh`](build.sh)
- Original broad run: [`run.sh`](run.sh)
- Generated decrypt source SHA-256:
  `d9ae5e3171f6afe67c9d0e0d7c83a2bef3ce53c6b40b944de8f8e3b709e225fb`
- Generated decrypt object SHA-256:
  `7ab681a1d77ba8b0eec2f9b672e631bb66046556c1da3ba1c5a5d3b69830a24f`
