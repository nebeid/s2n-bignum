# AES-256-GCM 4x experiment

## Candidates and provenance

This report evaluates six AES-256-GCM 4x kernels:

- **Encrypt `scalar_iv_mem_late_tag_scalar_rk`**: Hanno Becker's best
  sustained-throughput encrypt candidate on Graviton2 from about 2 KiB through
  32 KiB.
- **Encrypt shared-entry `fast_tail` + `late_tag`**: the recommended result,
  with one frame, common round-key setup, dedicated fused 1-, 2-, and 3-block
  paths, and Hanno's unchanged large-message loop.
- **Encrypt helper `fast_tail` + `late_tag`**: the earlier two-kernel version,
  retained in the appendix as the performance control.
- **Direct integrated encrypt**: a smaller follow-up that puts SLOTHY-scheduled
  exact tails directly into late-tag; retained as a negative performance
  result, not the recommended short path.
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

Hanno's committed late-tag encrypt and basic decrypt kernels are outputs of
`optimize_x4()`, which invokes SLOTHY with software pipelining enabled for
Neoverse N1, the Graviton2 core. Their steady-state x4 loops have 70-cycle
SLOTHY estimates.

## Recommended encrypt shared entry

The recommended result is one exported function with one stack frame and an
early dispatch before the incompatible counter setup:

- common entry code saves registers, loads AES round keys 0--13, and prepares
  the GHASH reduction constant;
- 1--3 blocks load round key 14 as a vector and use the vector-counter
  `fast_tail` setup;
- 4 or more blocks load round key 14 as two scalars and use Hanno's
  `scalar_iv_mem_late_tag_scalar_rk` setup and loop;
- both paths share the register restore and return sequence.

The [`shared entry`](src/hanno-enc-entry-wrapper.S) is 172 bytes. The
[`body generator`](make-enc-entry-body.awk) removes the duplicate frame,
common key loads, and return shell from the
[`short body`](src/hanno-enc-entry-short.S) and
[`large body`](src/hanno-enc-entry-large.S). For the short-only body it also
replaces generic `udiv`/`msub` loop counting with one shift and removes a
branch to the immediately following instruction.

The fused 1-, 2-, and 3-block AES-CTR + GHASH schedules come unchanged from
Hanno's [`fast_tail` N1/SLOTHY output](src/hanno-enc-fast-tail.S). The large
loop comes unchanged from Hanno's N1 software-pipelined
[`late-tag` output](src/hanno-enc-large.S). Its 2,612-byte machine-code range
is byte-identical in the generated body and original object; both hash to
`f008425433b1e55216d9848f97f432d2406035aa1ca6e03e14595a47ff22abdd`.
Thus no new unscheduled AES/GHASH body replaces either SLOTHY result.

### Correctness and size

The independent one-block KAT checked ciphertext, GHASH state, counter, and
return value. Differential gates then checked output, Xi, counter, and return
value for every whole-block length from 1 through 256 blocks. G2 compared
shared entry, full `fast_tail`, and late-tag; G3--G5 additionally compared
compact 8x. Every gate passed on all four processors.

| encrypt object | `.text` bytes | change from late-tag |
|---|---:|---:|
| Hanno late-tag | 3,864 | baseline |
| rejected tail-only integration | 4,892 | +1,028 B / +26.6% |
| **recommended shared entry** | **5,140** | **+1,276 B / +33.0%** |
| earlier helper hybrid | 5,312 | +1,448 B / +37.5% |
| compact 8x `fast1`--`fast4` | 8,624 | +4,760 B / +123.2% |

The shared entry is 172 bytes smaller than the helper hybrid and 3,484 bytes
smaller than compact 8x. Its object SHA-256 is
`8988bf398f1a4083f76954af5185b578c0a6ffc5db61beee6b7f387a93f23d01`.

### Short-message performance

Positive values mean shared entry is faster than compact 8x:

| bytes | G3 / V1 | G4 / V2 | G5 / V3 |
|---:|---:|---:|---:|
| 16 | +12.5% | +15.1% | +11.5% |
| 32 | -5.8% | +2.3% | +3.4% |
| 48 | -8.1% | -1.4% | -0.7% |

Over 16--48 B, shared entry is effectively tied with compact 8x on G3
(+0.01%) and is faster by 5.62% on G4 and 4.90% on G5.

A direct entry-versus-helper control linked the same two objects in both
orders. The 16--48 B geometric-mean shared-entry advantage was:

| layout | G2 / N1 | G3 / V1 | G4 / V2 | G5 / V3 |
|:---|---:|---:|---:|---:|
| shared entry first | +0.07% | +0.27% | +0.74% | +0.66% |
| helper first | -0.03% | +0.37% | +1.03% | +0.67% |

This is a performance tie on G2 and a small shared-entry win on G3--G5, while
using 172 fewer bytes. Individual points still move by a few percent with
layout, which is why the recommendation uses the geometric mean and both
orders rather than one favorable placement.

The dispatch deliberately selects late-tag at 64 B and above. It is therefore
not a compact-8x replacement over 64--128 B; it is the smaller measured way to
add competitive 16--48 B handling while preserving the G2 large-message
winner.

### Large-message preservation

The geometric-mean shared-entry advantage over late-tag from 1,344 B through
32 KiB was noise-level:

| G2 / N1 | G3 / V1 | G4 / V2 | G5 / V3 |
|---:|---:|---:|---:|
| +0.058% | +0.134% | +0.014% | +0.012% |

Authoritative logs:

- [G2 short](results/entry-small-ip-172-31-11-58.log) and
  [G2 large](results/entry-large-ip-172-31-11-58.log)
- [G3 short](results/entry-small-ip-172-31-4-159.log) and
  [G3 large](results/entry-large-ip-172-31-4-159.log)
- [G4 short](results/entry-small-ip-172-31-44-56.log) and
  [G4 large](results/entry-large-ip-172-31-44-56.log)
- [G5 short](results/entry-small-ip-172-31-42-229.log) and
  [G5 large](results/entry-large-ip-172-31-42-229.log)

Two-layout control logs:

- G2 [entry first](results/entry-compare-entry-first-ip-172-31-11-58.log) and
  [helper first](results/entry-compare-hybrid-first-ip-172-31-11-58.log)
- G3 [entry first](results/entry-compare-entry-first-ip-172-31-4-159.log) and
  [helper first](results/entry-compare-hybrid-first-ip-172-31-4-159.log)
- G4 [entry first](results/entry-compare-entry-first-ip-172-31-44-56.log) and
  [helper first](results/entry-compare-hybrid-first-ip-172-31-44-56.log)
- G5 [entry first](results/entry-compare-entry-first-ip-172-31-42-229.log) and
  [helper first](results/entry-compare-hybrid-first-ip-172-31-42-229.log)

The run is reproduced by [`build-enc-entry.sh`](build-enc-entry.sh) and
[`run-enc-entry.sh`](run-enc-entry.sh). The two-layout control uses
[`build-enc-entry-compare.sh`](build-enc-entry-compare.sh) and
[`run-enc-entry-compare.sh`](run-enc-entry-compare.sh); calculations are in
[`analyze-enc-entry.py`](analyze-enc-entry.py).

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

Differences around 1% should normally be treated as a wash. The shared-entry
promotion additionally used the two-order entry-versus-helper control described
above to expose code-placement sensitivity.

## Appendix: earlier encrypt integrations

### Separate short helper

The first performant construction used a
[`12-byte wrapper`](src/hanno-enc-hybrid-wrapper.S) to tail-call either a
1,424-byte [`short-only fast-tail helper`](src/hanno-enc-short.S) or the
3,864-byte [`unchanged late-tag kernel`](src/hanno-enc-large.S). With section
alignment, the linked object was 5,312 bytes: **+1,448 bytes over late-tag**.

This design established that separate vector-oriented short setup was
necessary. At 16--48 B it was 0.7% slower than compact 8x on G3 and faster by
5.6% on G4 and 5.2% on G5. It passed the KAT and 1--256-block differential
gate. It is superseded, not rejected: the recommended shared entry preserves
its performance while sharing the frame, key loads, and return code, saving
172 bytes.

Raw logs:

- [G3 / V1](results/hybrid-ip-172-31-4-159.log)
- [G4 / V2](results/hybrid-ip-172-31-44-56.log)
- [G5 / V3](results/hybrid-ip-172-31-42-229.log)

The run is reproduced by [`build-enc-hybrid.sh`](build-enc-hybrid.sh) and
[`run-enc-hybrid.sh`](run-enc-hybrid.sh); the independent KAT is
[`kat-enc-hybrid.c`](kat-enc-hybrid.c).

### Tail-only late-tag integration

The smaller follow-up put SLOTHY-scheduled exact tails directly after
late-tag's scalar setup. Its
[`4,892-byte output`](src/hanno-enc-integrated.S) was **+1,028 bytes over
late-tag**, but it retained the wrong setup for small messages.

Compact 8x was faster at 16, 32, and 48 B by 91.3%, 79.8%, and 46.6% on G3;
113.2%, 98.6%, and 64.9% on G4; and 113.5%, 115.9%, and 77.6% on G5. On G2,
full 4x `fast_tail` was faster by 42.4%, 20.7%, and 16.2%. Large performance
remained unchanged and all correctness gates passed, but this construction is
rejected as a short path.

Its [`clean source`](src/hanno-enc-integrated-clean.S),
[`pre-SLOTHY source`](src/hanno-enc-integrated-vector-preslothy.S), and final
output remain available for audit.

Raw logs:

- [G2 short](results/integrated-small-ip-172-31-11-58.log) and
  [G2 large](results/integrated-large-ip-172-31-11-58.log)
- [G3 short](results/integrated-small-ip-172-31-4-159.log) and
  [G3 large](results/integrated-large-ip-172-31-4-159.log)
- [G4 short](results/integrated-small-ip-172-31-44-56.log) and
  [G4 large](results/integrated-large-ip-172-31-44-56.log)
- [G5 short](results/integrated-small-ip-172-31-42-229.log) and
  [G5 large](results/integrated-large-ip-172-31-42-229.log)

The run is reproduced by
[`build-enc-integrated.sh`](build-enc-integrated.sh) and
[`run-enc-integrated.sh`](run-enc-integrated.sh).

## Additional artifacts

- Existing multi-candidate analyzer: [`analyze.py`](analyze.py)
- Original broad build: [`build.sh`](build.sh)
- Original broad run: [`run.sh`](run.sh)
- Generated decrypt source SHA-256:
  `d9ae5e3171f6afe67c9d0e0d7c83a2bef3ce53c6b40b944de8f8e3b709e225fb`
- Generated decrypt object SHA-256:
  `7ab681a1d77ba8b0eec2f9b672e631bb66046556c1da3ba1c5a5d3b69830a24f`
