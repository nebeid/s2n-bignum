# A shared fall-through fused cascade for the AES-256-GCM decrypt small path — measurement only

Companion to `_docs/fused-small-path-experiment.md` (the **eight-separate-bodies**
version). Same kernel, same host set, same harness, same discipline:
`arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` at local HEAD, `obj/base.o` md5
`114cedb51f36c584e50843d2838d871e` on **all four hosts** — byte-identical to the
object `arm/Makefile` produces in the synced tree, so every variant here is a
genuine `.S → .o → fresh link`. **No HOL Light, no `.ml`, no proofs, no gates.**
All work in `/tmp/fsp` on each host; no tracked file was modified; no instance
was stopped, started, rebooted or terminated.

Clocks measured on the spot (`clk.c`) at the start of the run used for every
table below:

| label | core | clock |
|---|---|---|
| GV3 | Neoverse-V1 `0xd40` | **2.5914 GHz** |
| GV4 | Neoverse-V2 `0xd4f` | **2.7927 GHz** |
| GV5 | Neoverse-V3 `0xd84` | **3.2903 GHz** |
| r8g | Neoverse-V2 (dev)   | **2.7928 GHz** |

---

## 0. Headline

| | |
|---|---|
| **Was the cascade built?** | **Yes**, and correct: KAT **35/35** on GV3/GV4/GV5/r8g, in-process byte-compare of `out`/`Xi`/`ivec`/return over **all 256 whole-block lengths** (which includes each `nblk = 1..8` explicitly), **32/32 liveness probes exact**, **0 `aese`/`aesmc` adjacency violations**. |
| **Frame** | **UNCHANGED at 80 bytes** — `stp d8,d9,[sp,#-80]!` / `ldp d8,d9,[sp],#80`, no other `sp` adjustment anywhere, in every variant. |
| **`nblk > 8` path** | **Instruction-for-instruction unchanged.** Normalised `objdump`: 2 instructions inserted at baseline instruction 14, then **1226 more identical**, and the 2-instruction `.L256_dec_ret` stub found verbatim, relocated. |
| **Code size** | `.text` **4968 → 6836 B (×1.38)** for the cascade, vs **12376 B (×2.49)** for the eight-body version. The ×1.08 hoped for in the brief was optimistic: the eight one-block sections still carry 8 copies of the 14-round sequence (224 AES instructions), plus 8 copies of the per-block GHASH. |
| **The OoO-window question — ANSWER: NO.** | The out-of-order window does **not** cover it. Achieved/slot-floor ratio at `nblk = 8`: **1.76 / 1.52 / 1.41** (V1/V2/V3) for the cascade, against **1.26 / 1.14 / 1.16** for the eight-body version and **1.38 / 1.26 / 1.25** for the untouched baseline. Steady-state cost of one extra block: **10.80 / 9.32 / 8.52 cycles** against a **6.50-cycle** slot floor. |
| **Mechanism, measured** | Made the interleave width `W` a parameter of one generator (identical slot counts for every `W`). Cycles per extra block on V2: **W=1 (keys hoisted) → 9.32, W=2 → 8.68, W=4 → 8.01, W=8 → 6.51 (= the 6.50 floor slope).** The ratio is a monotone function of how much independent work sits **adjacent in program order** — the window's *capacity* is not the limit, the *ordering* is. |
| **Head-to-head vs the eight-body version** | Equal at 16 B and 32 B (within ±2.7 %, no consistent sign across hosts: GV3 −0.2/+2.7 %, GV4 +2.1/−0.8 %, GV5 +0.7/−0.8 %). Then **+9…+20 % at 48 B, +20…+33 % at 64 B, +26…+39 % at 80 B, +26…+42 % at 96–112 B, +26…+44 % at 128 B.** |
| **vs our HEAD kernel** | Cascade still wins at small `nblk`: −47/−50/−46 % at 16 B, −42/−43/−43 % at 32 B, −33/−38/−40 % at 48 B, −21/−27/−30 % at 64 B, −11/−17/−21 % at 80 B. **Crossover to a loss at `nblk = 6` (V1), `7` (V2), `8` (V3).** At 128 B the cascade is **+31/+24/+16 % slower than doing nothing.** |
| **≥256 B** | **Wash, as required.** Max \|Δ\| over all variants, all hosts, 256 B–4 KB = **0.68 %**, and every value is at or below its own host's A/A floor at that length. |
| **Hybrid** | A **width-4** cascade (`.text` 9336 B, ×1.88) recovers most of it: −42/−38/−25/−18/−10 % vs HEAD at 48/64/80/96/112 B, but is still **+7 % vs HEAD at 128 B**, so it needs the existing path for `nblk = 8`. It is still 3–19 % behind the eight-body version. |
| **Verdict** | **The cascade does not match the eight-body version.** Crossover is at **`nblk = 3`**: at 1–2 blocks it is equal, from 3 blocks on it loses monotonically. Reported as a **measured negative** — the hypothesis in the brief is dead, and the reason is now quantified. |

---

## 1. What was built

### 1.1 Structure

Two instructions inserted after `add x10, sp, #64` — the same anchor and the
same test the eight-body version uses, before any CTR or AES work:

```
	cmp	x9, #128			//[CASC] nblk <= 8 ?
	b.le	.L256_dec_casck_small
```

and one new region appended before `.L256_dec_ret`:

```
.L256_dec_casck_small:   common prep + 3-deep balanced compare tree on x9
.L256_dec_casck_stub_8 .. _stub_1     acc <- Xi' * H^n  (3 pmull), then b <entry>
.L256_dec_casck_8:  one block, GHASH power H^8   <- enter here for nblk = 8
.L256_dec_casck_7:  one block, H^7               <- enter here for nblk = 7
   ...                                              (falls through)
.L256_dec_casck_1:  one block, H^1, plus the MODULO reduce, the tag store and
                    the counter store interleaved into this section's AES units
.L256_dec_casck_done:   mov x0,x9 / frame pop / ret
```

One instruction stream, eight entry labels, each section falling through to the
next. Entering at `.L256_dec_casck_j` executes sections `j, j-1, …, 1` = exactly
`j` blocks. **No dead AES at any entry point** (`14n` `aese` for `nblk = n`,
verified by the slot counter), and the 14-round sequence appears **eight times
(once per section)** instead of **thirty-six times** (once per block per body)
as in the eight-body version.

### 1.2 The three things a fall-through cascade has to solve

A section cannot know `n`, but it can know its own GHASH power. Section
`.L_j` is the one that uses `H^j`; that section handles block index `i = n − j`,
which is *not* an assembly-time constant. Resolved as follows.

1. **Addresses.** Since the sections execute with `i = 0,1,…,n−1` in program
   order, the ciphertext load and the plaintext store use **post-increment**
   (`ldr q,[x0],#16` / `str q,[x2],#16`), which is `n`-independent. The baseline
   already post-increments `x0` and `x2` (22 and 23 sites), so the GPR footprint
   is unchanged.
2. **The counter.** The CTR block for a section is `base + i`, so `v29` is
   advanced by `+1` at the top of every section. This is a **serial add chain**,
   2 cycles per link — unavoidable in a cascade, and *not* the bottleneck
   (14 cycles at `nblk = 8` against a 58-cycle floor).
3. **The incoming tag.** GHASH needs `(Xi ⊕ C₀)·H^n ⊕ C₁·H^(n−1) ⊕ …`, so `Xi`
   must be multiplied by `H^n`, which *is* entry-dependent. The eight-body
   version XORs the tag into block 0 for free. A cascade cannot. Instead each
   **entry stub** exploits the GF(2)-linearity of the three product maps and
   computes `acc_{hi,mid,lo} ← Xi′·H^n` directly (2 loads, 2 ALU, 3 `pmull`),
   after which **every section is uniform** and folds its own three products
   into the accumulators with three `eor`. Cost of the uniformity: +5 slots in
   the stub and +12 slots at `nblk = 8` versus the eight-body version's paired
   `eor3` folds (232 vs 224 slots — see §2).

### 1.3 Two variants of the cascade, and why the second is the one reported

The naive cascade reloads the whole AES-256 key schedule (**7 `ldp`**) in every
one-block section — 56 `ldp` = 896 B of L1 traffic at `nblk = 8`, i.e. 17
16-byte loads per 6.5 cycles of issue, which exceeds the load ports. Measured
cost: **4.6 ns at `nblk = 8` on V2** (36.06 → 31.67 ns).

So the reported cascade (`casck`, `fused-cascade.patch`) **hoists all fifteen
round keys** into `v2…v15 + v20` before the dispatch, leaving a section with
only three loads (ciphertext, `H^j`, `H^j` k). Register map, 31 of 32 SIMD
registers, nothing spilled:

| role | registers |
|---|---|
| rk0…rk14 (hoisted, loaded once) | `v2…v15`, `v20` |
| AES state | `v0` (even section), `v1` (odd section) |
| ciphertext / GHASH block / mid | `v21` / `v22` / `v23` |
| products (also the MODULO temps) | `v24`, `v25`, `v26` |
| `H^j {l|h}` / `H^j` k (`ldr d`) | `v27` / `v28` |
| accumulators hi/mid/lo | `v17` / `v18` / `v19` |
| `Xi′` then the MODULO constant | `v16` |
| counter / `+1` / scratch | `v29` / `v31` / `v30` |

A control worth recording: the naive cascade gives each of the eight sections
its **own** state register (`v0…v7`) while `casck` alternates just two, and the
key-loads-deleted diagnostic (`cascnk`, §5.3) lands within **0.6 %** of `casck`.
So SIMD register renaming fully hides the reuse — reusing one state register per
section costs nothing, and none of the shortfall below is a false-dependency
artefact.

### 1.4 GHASH front-loading — what survived

In the eight-body version each body has its own tuned split point `K` between
GHASH and MODULO. **A single shared stream cannot have a per-`n` split point**,
so the cascade has only two knobs: `ksec` (the fraction of a section's 14 AES
units over which that section's GHASH is spread) and `k1` (the same for the last
section, whose remaining units carry the MODULO chain, the tag store and the
counter store). Front-loading MODULO into the *last* section's AES rounds is the
one part of the idea that transfers directly, and it is what keeps `nblk = 1`
level with the eight-body version.

Swept `ksec ∈ {0.4,0.7,1.0} × k1 ∈ {0.25,0.35,0.50}` on r8g
(`logs/ksweep.txt`): total spread **1.1–1.2 % at `nblk` = 1, 4 and 8**. The
shipped setting (`ksec = 1.0`, `k1 = 0.35`) is within 0.6 % of the best.
**The cascade's shortfall is therefore not a scheduling artefact.**

---

## 2. The answer: slots, cycles, ratio

Slot counts use the established convention (adjacent `aese`+`aesmc` = 1 slot,
`.inst`-encoded `eor3` counted, loads/stores excluded). `verify_casck.py` /
`verify_casc.py` report **0 adjacency violations** in every variant.

Cascade slots per `nblk` — 6 (common prep) + 5 (entry stub) + 26 per section,
39 for the last section (26 + 13 of MODULO/tag/counter):

| `nblk` | `aese` | cascade slots | floor @4/cyc | eight-body slots | baseline slots |
|---:|---:|---:|---:|---:|---:|
| 1 | 14 | **50** | 12.50 | 44 | 195 |
| 2 | 28 | **76** | 19.00 | 71 | 207 |
| 3 | 42 | **102** | 25.50 | 95 | 217 |
| 4 | 56 | **128** | 32.00 | 122 | 227 |
| 5 | 70 | **154** | 38.50 | 146 | 235 |
| 6 | 84 | **180** | 45.00 | 173 | 243 |
| 7 | 98 | **206** | 51.50 | 197 | 249 |
| 8 | 112 | **232** | 58.00 | 224 | 226 |

Exactly `14n` `aese`: no dead AES. The cascade carries **8 more slots at
`nblk = 8`** than the eight-body version (the uniform 3-`eor` folds instead of
paired `eor3`, +5 for the stub) — a 2-cycle difference, i.e. nothing.

### 2.1 Achieved cycles and achieved/floor, `nblk = 1..8`

`cyc / ratio`, min of 3 processes × 150 reps, `taskset -c 3`.

**GV4 — Neoverse-V2**

| `nblk` | floor | baseline | eight-body | **cascade** |
|---:|---:|---|---|---|
| 1 | 12.50 | 68.6 / 1.41× | 34.4 / 3.12× | **35.1 / 2.81×** |
| 2 | 19.00 | 65.4 / 1.26× | 37.2 / 2.10× | **36.9 / 1.94×** |
| 3 | 25.50 | 67.7 / 1.25× | 38.2 / 1.61× | **42.1 / 1.65×** |
| 4 | 32.00 | 70.1 / 1.24× | 41.5 / 1.36× | **51.2 / 1.60×** |
| 5 | 38.50 | 72.6 / 1.24× | 46.4 / 1.27× | **60.1 / 1.56×** |
| 6 | 45.00 | 75.2 / 1.24× | 52.5 / 1.21× | **69.8 / 1.55×** |
| 7 | 51.50 | 76.7 / 1.23× | 58.2 / 1.18× | **78.9 / 1.53×** |
| 8 | 58.00 | 71.3 / 1.26× | 64.0 / 1.14× | **88.4 / 1.52×** |

**GV3 — Neoverse-V1**

| `nblk` | floor | baseline | eight-body | **cascade** |
|---:|---:|---|---|---|
| 1 | 12.50 | 67.8 / 1.39× | 36.1 / 3.28× | **36.0 / 2.88×** |
| 2 | 19.00 | 68.7 / 1.33× | 38.5 / 2.17× | **39.5 / 2.08×** |
| 3 | 25.50 | 71.8 / 1.32× | 40.1 / 1.69× | **48.1 / 1.89×** |
| 4 | 32.00 | 74.8 / 1.32× | 44.2 / 1.45× | **58.9 / 1.84×** |
| 5 | 38.50 | 77.7 / 1.32× | 49.9 / 1.37× | **69.3 / 1.80×** |
| 6 | 45.00 | 80.1 / 1.32× | 56.4 / 1.30× | **80.7 / 1.79×** |
| 7 | 51.50 | 82.1 / 1.32× | 62.9 / 1.28× | **91.1 / 1.77×** |
| 8 | 58.00 | 78.0 / 1.38× | 70.7 / 1.26× | **102.0 / 1.76×** |

**GV5 — Neoverse-V3**

| `nblk` | floor | baseline | eight-body | **cascade** |
|---:|---:|---|---|---|
| 1 | 12.50 | 64.6 / 1.32× | 34.7 / 3.15× | **34.9 / 2.79×** |
| 2 | 19.00 | 64.6 / 1.25× | 37.4 / 2.11× | **37.1 / 1.95×** |
| 3 | 25.50 | 67.0 / 1.23× | 36.9 / 1.55× | **40.2 / 1.58×** |
| 4 | 32.00 | 68.9 / 1.21× | 40.0 / 1.31× | **48.0 / 1.50×** |
| 5 | 38.50 | 71.1 / 1.21× | 44.8 / 1.23× | **56.2 / 1.46×** |
| 6 | 45.00 | 73.6 / 1.21× | 51.5 / 1.19× | **64.7 / 1.44×** |
| 7 | 51.50 | 75.1 / 1.21× | 57.7 / 1.17× | **73.3 / 1.42×** |
| 8 | 58.00 | 70.6 / 1.25× | 64.9 / 1.16× | **82.0 / 1.41×** |

r8g reproduces GV4 to within 0.2 % at every `nblk`. Full four-host tables in
`logs/tables.txt`.

### 2.2 Reading it

* **At `nblk` = 1 and 2 both designs are the same code in a different order and
  both are latency-bound** (ratio 2.8–3.3×; at `nblk = 1` a 14-round AES chain
  is ~28 cycles against a 12.5-cycle floor). The cascade is *level* here — it
  even has the slightly better ratio, because its 50 slots include no wasted
  work and its MODULO is front-loaded into the single section's AES rounds.
* **From `nblk = 3` the two diverge and the cascade's ratio plateaus at
  1.4–1.8× while the eight-body version's falls towards 1.14×.** The eight-body
  version converges on the slot floor; the cascade does not converge at all.
* The plateau is the diagnostic: the cascade's ratio is **flat in `n`**
  (1.60 → 1.52 on V2 from `nblk` 4 to 8), i.e. its steady-state cost per block
  is a constant well above the floor. That is a throughput deficit, not a
  start-up cost.

### 2.3 Steady-state cost of one extra block (linear fit, `nblk` = 4..8)

| host | floor | baseline | eight-body | **cascade `W=1`** | `W=2` | `W=4` | `W=8` |
|---|---:|---:|---:|---:|---:|---:|---:|
| GV3 (V1) | 6.50 | 1.09 | 6.61 | **10.80** | 10.13 | 8.86 | 6.27 |
| GV4 (V2) | 6.50 | 0.64 | 5.68 | **9.32** | 8.68 | 8.01 | 6.51 |
| GV5 (V3) | 6.50 | 0.74 | 6.28 | **8.52** | 8.50 | 7.73 | 6.61 |
| r8g (V2) | 6.50 | 0.64 | 5.68 | **9.33** | 8.69 | 8.00 | 6.55 |

Two of these slopes are legitimately *below* the 6.50-cycle floor slope and it
is worth being explicit about why: a slope below the floor means the design
started with **latency slack** and is spending it. The baseline (~0.6–1.1) pays
the whole 8-block AES up front and only adds one GHASH fold per extra block,
which is why it is the *slowest* design at small `n` and the least sensitive to
`n`. The eight-body version (5.68 on V2) starts at `nblk = 1` with 34.4 achieved
cycles against an 11.0-cycle floor — 23 cycles of idle issue capacity under the
14-round AES chain — and absorbs the extra blocks into it, arriving at 1.14× the
floor at `nblk = 8`.

The cascade has exactly the same slack at `nblk = 1` (35.1 cycles, 12.5-cycle
floor) **and cannot spend it**: its slope is 1.31–1.66× the floor slope, so the
ratio plateaus instead of converging. `W=8` sits on the floor slope. **This is
the measured answer to the brief's hypothesis.**

---

## 3. Why the window does not cover it

The brief's reasoning was: one block's chain is ~27 instructions, four chains
(~108) saturate 4 slots/cycle, and 108 instructions fit comfortably in the
reorder window — so a fall-through cascade should reach the same floor. The
first two steps are right; the third is the wrong window.

To issue 4 AES-equivalent slots per cycle when each `aese`+`aesmc` pair has the
established 2.00-cycle latency (V2/V3), the machine needs ~8 **independent** AES
chains in flight. What it actually sustains is measured directly: the 28-cycle
per-block chain divided by the steady-state cost per block gives the number of
blocks resident — **28 / 9.32 = 3.0 on V2** and 28 / 8.52 = 3.3 on V3. (V1 is
left out of this arithmetic: its per-pair latency was only ever bounded above at
2.72 cycles, so its chain length is not pinned down. Its measured ratio of 1.76×
stands regardless.)

A fall-through cascade places all ~26 vector µops of one block **contiguously**,
and they are a single dependence chain. The oldest of them drains at one pair
per 2 cycles, so instructions behind them cannot leave the vector issue queues.
Whatever the queues' capacity `Q` is in µops, the number of *independent* chains
resident is `Q / 26`, and 3.0 blocks × 26 ≈ 78 vector µops — far below the ~320
entry reorder buffer, and entirely consistent with the size of the ASIMD issue
queues on these cores. **The reorder buffer is not the binding window; the issue
queues are, and their occupancy is spent on one chain at a time.**

The width sweep is the control. `gen_cascW.py` emits the same design for
`W ∈ {1,2,4,8}` with **identical per-`nblk` slot counts** — the only variable is
how many independent chains sit adjacent in program order:

| `W` | structure | blocks of AES code | `.text` | V2 cyc per extra block | ÷ 6.50 floor slope | V2 ns @128 B |
|---:|---|---:|---:|---:|---:|---:|
| 1 | 8 one-block sections | 8 | 7060 | 11.20¹ | 1.72× | 36.06 |
| 2 | 4 two-block super-sections + 1-block odd prefixes | 12 | 7816 | 8.68 | 1.34× | 30.20 |
| 4 | 2 four-block super-sections + 1/2/3-block prefixes and bodies | 20 | 9336 | 8.01 | 1.23× | 27.29 |
| 8 | 1 eight-block body + standalone 1..7-block bodies | 36 | 12364 | 6.51 | **1.00×** | 24.90 |

¹ `W=1` in this uniform series rotates round keys like the baseline, so it pays
7 `ldp` per block; the key-hoisted `casck` is the fair `W=1` point at
**9.32 cyc/block, 1.43×, 31.67 ns**.

`W=8` *is* the eight-separate-bodies design, re-derived by this generator, and
its marginal cost per block lands exactly on the 6.50-cycle slot floor — so
nothing about the measurement setup prevents the floor from being reached; only
the interleave width decides whether it is. `cw8` is still 8.6 % behind the
shipped eight-body variant at 128 B (24.90 vs 22.93 ns, ratio 1.20× vs 1.14×);
that residual is the shipped variant's per-`n` tuned split points, its paired
`eor3` accumulator folds (224 slots vs 232) and its L1-hot ciphertext reload —
refinements orthogonal to the question asked here.

**Software interleaving is not redundant with the out-of-order engine.** Its job
is to put independent work *next to each other in program order*, and no window
size substitutes for that when a single chain is 26 µops long.

---

## 4. Kernel-level ns/call

Discipline: every variant `objcopy --redefine-sym`'d to a distinct symbol and
linked into **one** binary (8 slots); round-robin with the slot order rotated
every rep; `taskset -c 3`; 200-call warm-up per pass; **best of 150 reps × 3
processes**, absolute figures the min over processes, Δ % the **median of the
per-process best-deltas**. Slot 1 is the baseline object a second time: the
**A/A floor**. Raw logs `logs/cascw_{GV3,GV4,GV5,r8g}.log`.

`base` = our HEAD kernel · `A/A` = the A/A floor · `8body` = the eight-body
fused path (`fused-small-path.patch`) · `casc` = this experiment's cascade
(`fused-cascade.patch`) · `W2`/`W4` = width-2/width-4 cascades.

### 4.1 GV4 — Neoverse-V2, 2.7927 GHz

| bytes | blk | base | A/A | 8body | **casc** | W2 | W4 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 1 | 24.574 | 23.374 | 12.301 | **12.568** | 13.361 | 12.486 |
| 32 | 2 | 23.401 | 23.397 | 13.331 | **13.230** | 13.361 | 13.355 |
| 48 | 3 | 24.249 | 24.256 | 13.678 | **15.087** | 14.992 | 14.114 |
| 64 | 4 | 25.105 | 25.097 | 14.872 | **18.342** | 17.702 | 15.560 |
| 80 | 5 | 25.989 | 25.992 | 16.622 | **21.532** | 22.186 | 19.609 |
| 96 | 6 | 26.931 | 26.874 | 18.791 | **25.002** | 24.150 | 22.068 |
| 112 | 7 | 27.470 | 27.370 | 20.850 | **28.261** | 28.296 | 24.811 |
| 128 | 8 | 25.515 | 25.536 | 22.934 | **31.669** | 30.196 | 27.294 |
| 256 | 16 | 45.432 | 45.348 | 45.343 | 45.340 | 45.308 | 45.317 |
| 512 | 32 | 84.355 | 84.436 | 84.380 | 84.156 | 84.457 | 84.319 |
| 1024 | 64 | 161.349 | 162.090 | 161.933 | 161.722 | 161.903 | 161.995 |
| 4096 | 256 | 628.109 | 628.946 | 628.196 | 628.761 | 628.695 | 628.811 |

### 4.2 GV3 — Neoverse-V1, 2.5914 GHz

| bytes | blk | base | A/A | 8body | **casc** | W2 | W4 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 1 | 26.148 | 26.197 | 13.914 | **13.887** | 13.569 | 13.629 |
| 32 | 2 | 26.516 | 26.552 | 14.859 | **15.262** | 15.104 | 15.105 |
| 48 | 3 | 27.699 | 27.692 | 15.477 | **18.551** | 18.016 | 16.104 |
| 64 | 4 | 28.849 | 28.828 | 17.055 | **22.740** | 21.014 | 19.266 |
| 80 | 5 | 29.990 | 29.983 | 19.251 | **26.761** | 25.539 | 24.812 |
| 96 | 6 | 30.893 | 30.854 | 21.765 | **31.150** | 28.752 | 26.746 |
| 112 | 7 | 31.674 | 31.768 | 24.254 | **35.163** | 34.068 | 29.356 |
| 128 | 8 | 30.117 | 29.939 | 27.299 | **39.368** | 36.300 | 34.097 |
| 256 | 16 | 52.321 | 52.393 | 52.204 | 51.786 | 51.976 | 52.223 |
| 512 | 32 | 94.825 | 95.105 | 94.353 | 94.500 | 94.598 | 94.766 |
| 1024 | 64 | 180.128 | 180.537 | 179.262 | 179.156 | 179.704 | 180.005 |
| 4096 | 256 | 694.722 | 694.165 | 691.025 | 691.198 | 691.016 | 692.285 |

### 4.3 GV5 — Neoverse-V3, 3.2903 GHz (the quiet host: A/A ≤ 0.03 %)

| bytes | blk | base | A/A | 8body | **casc** | W2 | W4 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 1 | 19.620 | 19.619 | 10.539 | **10.615** | 10.607 | 10.607 |
| 32 | 2 | 19.643 | 19.647 | 11.364 | **11.276** | 11.572 | 11.584 |
| 48 | 3 | 20.352 | 20.355 | 11.217 | **12.217** | 12.188 | 11.851 |
| 64 | 4 | 20.954 | 20.952 | 12.157 | **14.584** | 14.020 | 12.943 |
| 80 | 5 | 21.603 | 21.600 | 13.601 | **17.079** | 17.151 | 15.942 |
| 96 | 6 | 22.372 | 22.378 | 15.643 | **19.678** | 19.202 | 18.043 |
| 112 | 7 | 22.839 | 22.843 | 17.525 | **22.287** | 22.510 | 20.436 |
| 128 | 8 | 21.460 | 21.459 | 19.736 | **24.924** | 24.259 | 22.438 |
| 256 | 16 | 38.173 | 38.172 | 38.171 | 38.180 | 38.180 | 38.176 |
| 512 | 32 | 71.110 | 71.125 | 71.134 | 71.137 | 71.080 | 71.141 |
| 1024 | 64 | 138.504 | 138.498 | 138.502 | 138.502 | 138.553 | 138.509 |
| 4096 | 256 | 546.876 | 546.904 | 546.926 | 546.887 | 546.923 | 546.875 |

### 4.4 Δ % vs our HEAD kernel, with the A/A noise floor

| bytes | GV3 A/A | **GV3 casc** | GV4 A/A | **GV4 casc** | GV5 A/A | **GV5 casc** |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | +0.45 | **−46.95** | **−4.21** ⚠ | **−50.35** | −0.03 | **−45.91** |
| 32 | +0.09 | **−42.45** | −0.02 | **−43.47** | +0.01 | **−42.60** |
| 48 | −0.13 | **−33.15** | +0.03 | **−37.75** | −0.01 | **−39.98** |
| 64 | −0.08 | **−21.18** | −0.08 | **−26.95** | +0.00 | **−30.40** |
| 80 | −0.04 | **−10.75** | +0.08 | **−17.14** | −0.01 | **−20.92** |
| 96 | −0.13 | **+0.81** | −0.07 | **−7.14** | +0.03 | **−12.04** |
| 112 | −0.35 | **+10.32** | −0.32 | **+2.89** | +0.02 | **−2.40** |
| 128 | −0.17 | **+30.72** | +0.16 | **+24.10** | −0.01 | **+16.15** |
| 256 | +0.12 | −0.33 | −0.13 | −0.22 | +0.02 | +0.01 |
| 512 | +0.08 | −0.68 | +0.15 | −0.03 | +0.01 | +0.03 |
| 1024 | +0.20 | −0.42 | +0.46 | +0.35 | −0.00 | +0.04 |
| 4096 | +0.01 | −0.51 | +0.13 | +0.11 | +0.01 | +0.01 |

⚠ **GV4's 16 B A/A floor was bad in this run**: the two identical baseline
objects differed by −4.2 % (median) and −7.7 % (worst process); GV3/GV5/r8g were
≤ 0.6 %. The baseline kernel's 16 B time is address-placement sensitive. Every
16 B Δ % on GV4 must therefore be read with a ±8 % floor, so use GV3/GV5/r8g for
that length. The fused variants themselves are stable at 16 B to ±0.03 ns across
processes on every host, and the cascade-vs-eight-body comparison (§4.5) is
unaffected.

**Everything at ≥256 B is inside the floor.** The largest \|Δ\| anywhere in the
≥256 B block, over all six variants and all four hosts, is **0.68 %** (GV3
512 B, where the historical floor is 0.67 %); GV3's 512/1024 B A/A is +0.08/+0.20
here and the 128 B V2 placement bias shows as +0.16. **No claim is made at
≥256 B: it is a measured wash**, exactly as the byte-identical `nblk>8` path
requires.

### 4.5 Δ % of the cascade vs the eight-body version — the head-to-head

| bytes | blk | GV3 | GV4 | GV5 | r8g |
|---:|---:|---:|---:|---:|---:|
| 16 | 1 | **−0.19** | +2.11 | +0.72 | +2.10 |
| 32 | 2 | +2.71 | **−0.77** | **−0.78** | **−0.77** |
| 48 | 3 | +19.86 | +10.37 | +8.92 | +10.33 |
| 64 | 4 | +33.35 | +23.32 | +19.97 | +23.35 |
| 80 | 5 | +39.02 | +29.54 | +25.59 | +29.57 |
| 96 | 6 | +42.33 | +33.09 | +25.77 | +33.18 |
| 112 | 7 | +42.83 | +35.56 | +27.23 | +35.60 |
| 128 | 8 | +44.20 | +38.09 | +26.31 | +38.06 |
| 256–4096 | ≥16 | ≤0.16 | ≤0.11 | ≤0.01 | ≤0.19 |

**Crossover: `nblk = 3`.** At 1 and 2 blocks the two designs are equal to within
the A/A floor (the ±0.8–2.7 % scatter has no consistent sign across hosts). From
3 blocks on the cascade loses monotonically, ending 26–44 % behind.

### 4.6 The hybrids, priced

| design | `.text` | ×base | 48 B | 64 B | 80 B | 96 B | 112 B | 128 B |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| eight-body (`fused-small-path.patch`) | 12376 | 2.49 | **−43.6** | **−40.8** | **−36.0** | **−30.2** | **−24.1** | **−10.1** |
| width-4 cascade | 9336 | 1.88 | −41.8 | −38.1 | −24.6 | −18.0 | −9.7 | **+7.0** |
| width-2 cascade | 7816 | 1.57 | −38.2 | −29.5 | −14.3 | −10.3 | +3.0 | +18.4 |
| **pure cascade** | **6836** | **1.38** | −37.8 | −27.0 | −17.1 | −7.1 | +2.9 | +24.1 |
| baseline (do nothing) | 4968 | 1.00 | 0 | 0 | 0 | 0 | 0 | 0 |

(Δ % vs HEAD, GV4; 16 B and 32 B are −50/−43 for all four fused designs.)

The width-2 row is **non-monotone in `n`** and can be *worse* than the pure
cascade at odd lengths (80 B: −14.3 % vs the pure cascade's −17.1 %): for odd
`n` it enters through a one-block prefix section, which is the pure cascade's
worst case, and only then reaches the two-block super-sections. Width-4 has the
same shape at `n = 5` (one-block prefix, −24.6 % vs eight-body's −36.0 %). Any
production cascade would want its prefix widths tuned per length, at which point
it is drifting back towards eight bodies.

Every cascade width regresses at 128 B, so any cascade-based design must fall
back to the existing path for `nblk = 8` (where the baseline's dedicated
exact-8 drain already runs at 1.26× its floor). With that fallback:

* **pure cascade for `nblk ≤ 6`, existing path for 7–8** — `.text` ≈ ×1.38,
  keeps −50/−43/−38/−27/−17/−7 % at 16–96 B, gives up everything at 112–128 B.
* **width-4 cascade for `nblk ≤ 7`, existing path for 8** — `.text` ≈ ×1.8,
  keeps −50/−43/−42/−38/−25/−18/−10 % at 16–112 B.
* **eight-body** — `.text` ×2.49, keeps −47/−43/−44/−41/−36/−30/−24/−10 %.

The proof cost is unchanged in kind for all three (a set of straight-line fused
paths, plus a provably unchanged `nblk>8` machine code), but the cascade's paths
share code, so the *number* of distinct simulations is smaller while each
section must be proved correct for eight different entry contexts — the accumulator
state at the top of section `j` depends on the entry point. That is a materially
different (not obviously cheaper) proof obligation, and it is worth noting that
the shared stream buys none of the performance.

---

## 5. Correctness evidence

1. **Build fidelity.** `mk.sh` reproduces `arm/Makefile`'s rule verbatim
   (`gcc -E -Iinclude -xassembler-with-cpp | tr ';' '\n' | as -march=armv8.2-a+sha3`);
   `obj/base.o` md5 is `114cedb51f36c584e50843d2838d871e` on GV3, GV4, GV5 and
   r8g — the same object `arm/Makefile` produces in the synced tree. Every
   variant is `.S → .o → **fresh link**`; `arm/aes-gcm/kat` was never touched
   and `make clean` was never run.
2. **Differential KAT, genuine rebuild *and* relink** (`kat.sh` deletes
   `kat/kat_wb_dec` and relinks it from source against the fresh `.o` plus the
   trusted sibling `aesv8_gcm_8x_dec_256.o` on every invocation):
   **35 passed, 0 failed — `KAT GATE: PASS`** for `casc`, `casck`, `casc2`,
   `cw1`, `cw2`, `cw4`, `cw8` on **GV3, GV4, GV5 and r8g**.
3. **In-process byte-compare, run before every timing pass**, over **every
   whole-block length 1..256 blocks (16 B … 4096 B)** — which includes each
   `nblk = 1..8`, i.e. all eight entry labels — of `out`, `Xi`, `ivec` **and the
   return value**, against our HEAD kernel, with a real AES-256 schedule
   (`aes_hw_set_encrypt_key`), a real `H = E_K(0)` and a real `H^1..H^8` table
   (`gcm_init_v8`), plus a non-degeneracy check that `out != in`:
   ```
   SELFCHECK OK (256 whole-block lengths 1..256 blk x 8 variants;
                 out/Xi/ivec/ret byte-identical)
   ```
   on all four hosts, for all eight linked slots.
4. **Per-entry-point liveness probes (8 + 8, and again for `W=2` and `W=4`).**
   `zapN` replaces entry stub `N`'s `Xi′·H^N` seed with zeros — stub `N` is
   reached only for `nblk == N`, so it must break exactly that one length:
   ```
   zap1 {1}  zap2 {2}  zap3 {3}  zap4 {4}  zap5 {5}  zap6 {6}  zap7 {7}  zap8 {8}
   ```
   `zsecJ` zeroes cascade section `J`'s own products — section `J` runs for every
   `nblk >= J`, so it must break exactly `J..8` and nothing else:
   ```
   zsec1 1..8  zsec2 2..8  zsec3 3..8  zsec4 4..8
   zsec5 5..8  zsec6 6..8  zsec7 7..8  zsec8 8..8
   ```
   **32/32 probes exact** (`logs/probes_casck.txt`, `logs/probes_w2_w4.txt`).
   The `zsec` family is the check the brief asked for specifically — it is
   exactly where a fall-through bug hides (entering at `.L_5` while the code
   assumes eight live keystream registers), and it also confirms no probe ever
   perturbs `nblk > 8`.
5. **`aese`/`aesmc` adjacency: 0 violations** in `casc`, `casck`, `cw1`, `cw2`,
   `cw4`, `cw8` (`verify_casc*.py`, whole-file scan).
6. **Frame: 80 bytes, unchanged.** `objdump` shows `stp d8,d9,[sp,#-80]!` and
   `ldp d8,d9,[sp],#80` and **no other `sp` adjustment** in any variant. No new
   callee-saved register is written (the baseline already writes `v0`–`v31` and
   already post-increments `x0`/`x2`), so the exported precondition and
   `MAYCHANGE` footprint are untouched.
7. **`nblk > 8` unchanged, by normalised `objdump`** (`objcmp.py`, addresses and
   branch targets masked):
   ```
   base 1242 instructions, casck 1709 instructions
   first divergence at baseline instruction 14 (base: ld1 | variant: cmp x9,#0x80)
   2 instructions inserted; then 1226 more baseline instructions identical
   baseline tail left: 2 (the .L256_dec_ret stub) -> found verbatim, relocated
   appended after the baseline stream: 465 instructions
   VERDICT: nblk>8 content UNCHANGED
   ```
   Identical verdict for `casc` (+521 appended) and `cw4`; and the same script
   reproduces the eight-body version's +1850.

---

## 6. Verdict

1. **Structure**: eight one-block sections in one stream with eight fall-through
   entry labels, eight tiny entry stubs that seed the accumulator with
   `Xi′·H^n`, post-increment addressing to make block indices `n`-independent, a
   serial `+1` counter chain, and the MODULO reduce/tag/counter stores
   interleaved into the last section's AES rounds. **Frame stayed at 80 bytes.**
   `.text` 4968 → **6836 B (×1.38)** — a real saving over the eight-body
   version's ×2.49, though not the ×1.08 hoped for.
2. **The OoO-window hypothesis is dead.** Achieved/floor at `nblk = 8` is
   **1.76/1.52/1.41×** (V1/V2/V3) and does not improve with `n`; the eight-body
   version reaches **1.26/1.14/1.16×**. Steady state: **10.80/9.32/8.52 cycles
   per extra block against a 6.50-cycle floor** — i.e. only ~3 independent AES
   chains are in flight where ~8 are needed. Confirmed mechanistically by the
   width sweep (identical slot counts, `W=1 → 9.32`, `W=2 → 8.68`,
   `W=4 → 8.01`, `W=8 → 6.51 =` floor on V2) and by ruling out the alternatives:
   placement sweep 1.2 % flat, key-load pressure separated out and removed,
   register reuse shown harmless by an 8-state-register control.
3. **The cascade does not match the eight-body version. Crossover is
   `nblk = 3`** — equal at 16 B and 32 B, then +9…+20 % at 48 B rising to
   +26…+44 % at 128 B.
4. **Against doing nothing**, the cascade is still a large win at small lengths
   (−46…−50 % at 16 B, −42…−43 % at 32 B, −33…−40 % at 48 B, −21…−30 % at 64 B,
   −11…−21 % at 80 B) and becomes a **regression** at `nblk = 6` (V1), `7` (V2),
   `8` (V3), reaching **+16…+31 % at 128 B**. Any shippable cascade therefore
   needs the existing path for the top of the range.
5. **≥256 B is a wash on every host and every variant** (max \|Δ\| 0.68 %, at or
   below each host's own A/A floor), as the instruction-identical `nblk>8` path
   requires.
6. **If code size is the binding constraint**, the honest middle point is the
   **width-4 cascade for `nblk ≤ 7` with the existing path at `nblk = 8`**:
   ×1.88 `.text` for −42/−38/−25/−18/−10 % at 48–112 B, i.e. ~60 % of the
   eight-body win for ~60 % of its code growth. If code size is not the binding
   constraint, **keep the eight-body version**: the shared stream buys 5.5 KB and
   costs 26–44 % of the performance it was meant to preserve.

---

## 7. Artifacts

All under `_docs/fused-cascade/` (gitignored). Live scratch in `/tmp/fsp` on
GV3, GV4, GV5 and r8g; the eight-body harness in `_docs/fused-small-path/` was
reused unchanged (`bench.c`, `clk.c`, `build_bench.sh`, `mk.sh`, `kat.sh`).

| file | contents |
|---|---|
| `gen_casck.py` | **the reported cascade**: eight fall-through sections, 15 hoisted round keys, `--zap N` / `--zapsec J` probes |
| `gen_casc.py` | the naive cascade (round keys reloaded per section; also has the `casc3` paired-`eor3` variant) |
| `gen_casc2.py` | width-2 cascade with hoisted keys |
| `gen_cascW.py` | **one generator for `W ∈ {1,2,4,8}`** with identical per-`nblk` slot counts — the controlled width sweep; `W=8` re-derives the eight-separate-bodies design |
| `fused-cascade.patch` | the reported cascade vs the pristine `.S` |
| `fused-cascade-naive.patch`, `fused-cascade-w2.patch`, `fused-cascade-w4.patch` | the other three |
| `verify_casc.py`, `verify_casck.py`, `verify_casc2.py` | `aese`/`aesmc` adjacency, per-region and per-`nblk` slot counts, register footprint |
| `objcmp.py` | normalised `objdump` comparison of the `nblk>8` path |
| `probe.sh` | the 16 liveness probes |
| `measure_casc.sh` | 8-slot single-binary kernel benchmark driver |
| `analyze_casc.py` | all tables in this report |
| `logs/cascw_{GV3,GV4,GV5,r8g}.log` | the measurement runs, 3 processes × 150 reps × 8 slots |
| `logs/casc_{GV3,GV4,GV5,r8g}.log` | an earlier 5-slot run (base/A/A/eight-body/naive/hoisted), reproduces §4 to 0.3 % |
| `logs/tables.txt` | generated tables (absolute, Δ vs base, Δ vs eight-body, cycles + ratios, steady-state fit) |
| `logs/probes_casck.txt`, `logs/probes_w2_w4.txt` | the 32 liveness probes |
| `logs/verify_casck.txt`, `logs/verify_casc.txt`, `logs/textsizes.txt` | slot tables, adjacency, `.text` sizes |
| `logs/objcmp_casck.txt`, `logs/objcmp_cw4.txt` | `nblk>8` unchanged verdicts |
| `logs/ksweep.txt` | the GHASH/MODULO placement sweep (1.2 % flat) |
| `logs/diagnostics.txt` | `cascnk` (key loads deleted), `casc3` (paired `eor3`), `casc2` vs `cw2` |
