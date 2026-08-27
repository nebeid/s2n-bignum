# John AES-256 4x versus compact/tuned 8x

## Result

John's fastest single encrypt kernel across 16--128 B on all three hosts is
`aesv8-gcm-armv8-enc-opt-256_x4_fast_tail.S`, using geometric mean latency.
His fastest decrypt kernel is
`aesv8-gcm-armv8-dec-opt-256_x4_basic.S`.

The tables compare those two fixed 4x champions with compact 8x encrypt and
the decrypt implementation currently in PR #445. Positive values mean **8x
is faster**; negative values mean John's 4x kernel is faster.

### Encrypt: compact 8x versus John `fast_tail` 4x

| bytes | G3 / V1 | G4 / V2 | G5 / V3 |
|---:|---:|---:|---:|
| 16  | -8.2% | -17.6% | -13.3% |
| 32  | +5.6% | -1.4% | -3.0% |
| 48  | +6.5% | +1.7% | +0.7% |
| 64  | +13.7% | +8.0% | +11.1% |
| 80  | +4.9% | +4.5% | +1.2% |
| 96  | +12.7% | +9.7% | +9.7% |
| 112 | +18.8% | +18.1% | +18.4% |
| 128 | +27.9% | +25.8% | +26.5% |

Across all sizes, compact 8x has a 9.1% latency geometric-mean advantage
(G3 12.1%, G4 7.4%, G5 7.7%). John 4x wins 16 B on every host and narrowly
wins 32 B on G4/G5; compact 8x wins every host from 48 B onward.

### Decrypt: live PR `t4` versus John `basic` 4x

| bytes | G3 / V1 | G4 / V2 | G5 / V3 |
|---:|---:|---:|---:|
| 16  | -12.0% | -12.9% | -11.4% |
| 32  | +27.4% | +29.1% | +28.9% |
| 48  | +35.2% | +41.9% | +45.0% |
| 64  | +6.5% | +2.0% | +4.2% |
| 80  | -1.0% | -8.4% | -12.4% |
| 96  | +15.7% | +11.4% | +9.1% |
| 112 | +24.8% | +26.2% | +25.2% |
| 128 | +22.0% | +22.3% | +19.4% |

Across all sizes, the live PR `t4` has an 18.8% latency geometric-mean advantage
(G3 19.1%, G4 18.9%, G5 18.5%). John 4x wins 16 B and 80 B; the live PR wins
the other six sizes.

The earlier run used a local `t4` snapshot. A subsequent assembly comparison
against live PR #445 head `29c532644f8f1ac0c0a5ae520a06768ebcb4ac3f`
found identical `.text` on G3, G4, and G5. The comparison therefore did
include the implementation currently in the PR. That implementation has the
shared fused 1--4 block path and the older exact-8 drain; it does not have the
newer dedicated fused body-8 path from the separate `t4p8` experiment.

At 128 B, `t4p8` reduces latency relative to the live PR by 10.2% on G3,
9.3% on G4, and 8.7% on G5. John `basic` 4x is respectively 32.4%, 27.9%,
and 24.4% slower than the live PR at that size. See
`results/pr-compare-*.log` for the direct PR/`t4`/`t4p8` run.

## Graviton2 optimization screening

All candidates were assembled for `armv8.2-a+crypto` and checked to contain
no `EOR3`. Each process self-checked output and state for every length from 1
through 256 blocks before timing. The G2 run used nine processes, 200
interleaved samples per size and process, and CPU 3.

For encrypt, the fixed `fast_tail` candidate is 17.6% faster than John
`basic` by latency geometric mean over 16--128 B. Dedicated candidates win at
individual sizes: `dual_acc` at 16 and 64 B, `fast_tail` at 32, 48, 80, 96,
and 112 B, and `reload_round_keys_partial` at 128 B. The gains relative to
`basic` range from 1.7% at 128 B to 30.2% at 48 B.

For decrypt, the existing optimized `basic` beats the existing
`scalar_iv_mem2_late_tag` at every size. The source tree contains a clean
decrypt `fast_tail`, analogous to encrypt's useful fused 1-, 2-, and 3-block
tails, but no optimized decrypt output for it.

The optimized decrypt `fast_tail` combines the existing optimized `basic`
preamble and 4-block body with independently N1-scheduled fused 1-, 2-, and
3-block tails. The body before `Lloop_unrolled_end` is identical to optimized
`basic`. It passes the no-`EOR3` and 1--256 block differential gates and is
9.6% faster by latency geometric mean over 16--128 B:

| bytes | `basic` ns | optimized `fast_tail` ns | change |
|---:|---:|---:|---:|
| 16 | 19.003 | 17.303 | -8.9% |
| 32 | 30.405 | 24.904 | -18.1% |
| 48 | 41.605 | 31.605 | -24.0% |
| 64 | 40.806 | 41.206 | +1.0% |
| 80 | 51.989 | 51.607 | -0.7% |
| 96 | 63.197 | 57.587 | -8.9% |
| 112 | 74.764 | 64.010 | -14.4% |
| 128 | 69.010 | 69.428 | +0.6% |

As a structural control, the wholly unscheduled decrypt `fast_tail` was 8.5%
faster than optimized `basic` at 32 B and 12.6% faster at 48 B but lost at
body-heavy sizes. The final result confirms that the dedicated tails, rather
than an accidental body schedule difference, provide the G2 gain.

## Per-size selection

The fixed encrypt champion is not the fastest John variant at every size.
`reload_round_keys_partial` wins G3 16 B and some 128 B measurements;
`dual_acc` wins 64/80 B; `fast_tail` wins most remaining small sizes. Run
`python3 analyze.py` for absolute nanoseconds and the fastest John candidate
at every host and size. Decrypt `basic` wins every G3--G5 host and size.

## Method

- Hosts: c7g.2xlarge / Neoverse-V1, c8g.4xlarge / Neoverse-V2, and
  c9g.4xlarge / Neoverse-V3.
- Sizes: every whole-block length from 16 through 128 B.
- Timing: CPU 3, 160 interleaved samples per size, rotated variant order,
  seven independent processes. Reported values are the median process
  latency, where each process contributes its sample median.
- Correctness: each process first compared output, Xi, ivec, and return value
  for every length from 1 through 256 blocks. All 42 gates passed.
- Inputs: identical real AES-256 key schedule and H-power table in one process.
- All seven John encrypt candidates and both decrypt candidates were included.
  Object SHA-256 and `.text` sizes are recorded in each raw log.
- Maximum cross-process CV observed for the 8x reference was 1.09%.

This is a raw-kernel experiment. It excludes AEAD setup, dispatch, tag
finalization, and caller overhead. Differences around 1% should be treated as
a wash because no code-placement A/A campaign was included.

## Provenance

- John bundle:
  [AWS-LC commit `83d5627a`](https://github.com/hanno-becker/aws-lc/tree/83d5627a1d4315a71057fe6bc75900e080f255be/crypto/fipsmodule/modes/asm/slothy).
- Compact encrypt source: s2n-bignum commit
  `e6b3289ffde496e7b5b97b676ec46ab8114f3a85`, source SHA-256
  `669ae3413f69ce89a76ea85b8cb5e8e912429b43d0863e459b2cdee1a5f88b00`.
- Live-PR-equivalent `t4` decrypt source: s2n-bignum commit
  `9e9020e411f5660438270b1e0f5f45c9918f8449`, source SHA-256
  `7496af5959dfcc67f5a70e8d019358556720fa4492368e3aaf3ff2a8e323d365`.
- Live PR #445 source snapshot SHA-256:
  `95158882065cdd1c8930e5e767b59d7a774b914054ff91266393188f517fe293`.
- `t4p8` source SHA-256:
  `c9bff319de0642ca4d39af5dbbd844b8971b696fdaa1fa69ceb9bca5321b6556`.
- Generated G2 decrypt candidate:
  [`aesv8-gcm-armv8-dec-opt-256_x4_fast_tail.S`](src/aesv8-gcm-armv8-dec-opt-256_x4_fast_tail.S),
  SHA-256
  `d9ae5e3171f6afe67c9d0e0d7c83a2bef3ce53c6b40b944de8f8e3b709e225fb`.
- Raw logs are under [`results/`](results/).
