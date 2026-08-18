# `fused-w1-reorder` — instruction ORDERING inside the fixed W=1 four-section fused small path, tuned for Neoverse-V1 — measurement only

Companion to `_docs/fused-mix4s4.md` (which built and shipped the structure),
`_docs/fused-cascade-experiment.md` (the width sweep), `_docs/fused-g4.md` and
`_docs/fused-truncation-curve.md`. Same kernel, same harness, same discipline.

Kernel `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` at local HEAD;
`obj/base.o` md5 `114cedb51f36c584e50843d2838d871e` on all four hosts — the
object `arm/Makefile` produces. **No HOL Light, no `.ml`, no proofs, no gates.**
All work in `/tmp/fsw` (a copy of the g4 experiment's `/tmp/fsp`) and
`/tmp/fsw-mk` for the make-driven KAT on the dev host. **No tracked file was
modified anywhere** — `ec2r8g`'s tree is still at `c2609cf8` with only untracked
files — **`~/clean-gate` and `~/kat-check` were not touched, and no instance was
started, stopped, rebooted or terminated.**

| host | core | part | clock measured on the spot |
|---|---|---|---|
| **GV3 — primary** | Neoverse-V1 | `0xd40` | **2.5914 GHz** |
| GV4 | Neoverse-V2 | `0xd4f` | **2.7916 GHz** |
| GV5 | Neoverse-V3 | `0xd84` | **3.2903 GHz** |
| `ec2r8g` (dev) | Neoverse-V2 | `0xd4f` | 2.7929 GHz (published value; idle throughout, load average 0.00) |

---

## 0. Headline

| | |
|---|---|
| **Is there a win?** | **Yes, and it is a pure reordering.** One ordering, `d5`, beats the shipped `s4h`/W=1 ordering by **−2.16 / −1.91 / −1.92 / −2.12 %** of runtime at **64 B** (V1 / GV4 / r8g / V3) and by **−1.43 / −0.74 / −0.71 / −1.07 %** at 48 B, with **`.text` unchanged at 5980 B**, the same instruction multiset, the same per-`nblk` SIMD slot count (50/76/102/128), the same `aese` counts (14n), the same dispatch, the same stubs and the same 80-byte frame. |
| **What `d5` is** | The shipped ordering with exactly two changes *inside* each of the four sections: (1) the ciphertext `ldr q26,[x0],#16` becomes the section's **first** instruction, ahead of the counter `rev32`; (2) the remaining 11 GHASH-product ops are emitted in **three bursts of four** (after AES units 0, 4 and 9) instead of one op per AES round-pair. Nothing else moves. |
| **Δ% vs HEAD at the target** | 64 B: **−21.93 (V1) / −27.26 (GV4) / −27.25 (r8g) / −31.03 (V3)** against the baseline's −20.20 / −25.84 / −25.83 / −29.54 measured in the same binaries. The brief's target — 64 B on V1 — moves from **−20.0 % to −21.9 %**. |
| **Is the K-split flat on V1?** | **No — this is the round-1 finding.** `ksec` 1.0 → 0.35 alone is worth **−1.50 %** at 64 B and −1.01 % at 48 B on V1, against A/A floors of 0.05–0.25 %. The published "1.2 % flat" verdict came from a coarse 3×3 grid on V2; the V2 numbers are indeed smaller (−0.4 %) but not zero either. **Stop treating the K-split as flat.** It is, however, the *same* lever as `clump`: both make the product ops arrive in fewer, bigger, earlier bursts. |
| **Levers that ARE flat (stop revisiting)** | **Dispatch / taken-branch count** (3 taken branches at `nblk=4` → 0, or → 7): \|Δ\| ≤ 0.34 %. **Physical section layout** reversed with backward branches: −0.34 %. **End-relative static addressing** (both post-index address chains removed): −0.13 %. **Counter chain**: bounded from above at **−0.38 %** by a diagnostic that deletes it entirely. **Round-key placement**: already settled — hoisted wins, and the loads-at-section-head variant is −0.0…−0.3 %. **`fold=late`**: +0.06 %. |
| **Idempotent prefetch across sections** | **Structurally void, and this is a proof, not a null result.** Any duplicated idempotent op must write the same architectural register in both the early (previous-section) and the in-section copy, so the in-section copy is always the later writer and register renaming makes the early copy dead. No consumer can ever see the early value. What the lever was *reaching for* is real — a diagnostic that loads the ciphertext once in the shared prep is worth −2.00 % at 64 B on V1 — and `ct=head` captures most of it legally. |
| **80 B / 4096 B and everything above** | **Free.** `d5` at 80 B: −0.02 / −0.08 / −0.12 / −0.01 % vs the baseline ordering (V1/GV4/r8g/V3); at 4096 B: −0.02 / −0.29 / +0.11 / −0.00 %. Every reading at 80, 96, 112, 128, 256, 512, 1024 and 4096 B is inside that host's A/A floor. `nblk > 8` content is instruction-for-instruction unchanged for every one of the 59 legal-ordering objects. |
| **Correctness** | **KAT 35/35 / `KAT GATE: PASS` for every variant on every host** by genuine relink (binary deleted first), **and** through the real `arm/Makefile` + `arm/aes-gcm/kat/Makefile` on r8g with the make-built object **byte-identical** to the harness object (12/12 `SAME`). In-process byte-compare of `out`/`Xi`/`ivec`/return over **all 256 whole-block lengths**, re-run at the start of every timing process. **26 `brk`/zap probes per host exact** on all four hosts (52 on r8g), 18 guard-page checks clean. **0 adjacency violations.** Frame **80 B**. |
| **Recommendation** | **Ship `d5`.** It is a strictly-better permutation of the instructions already shipped: no new instruction, no new register, no size change, no structural change, and it moves the hardest number in the brief's table by 1.9 points on the core that cares most. `_docs/fused-w1-reorder/w1-to-d5.patch` is the complete diff against the current ordering. |

---

## 1. The structure (fixed) and the control

### 1.1 What is under test

The structure is `_docs/fused-mix4s4.md`'s `s4h` exactly — `gen_mix.py` widths
`1,1,1,1`, round keys hoisted:

```
    cmp  x9, #64                 //[W1] nblk <= 4 ?      <- 2 instructions at the
    b.le .L256_dec_w1_small      //                         entry anchor; NOT taken
                                 //                         for nblk > 4

.L256_dec_w1_small:  common prep: CTR base, Xi', 15 round keys -> v1..v15
                     balanced compare tree over {1,2,3,4}
.L256_dec_w1_stub_r: acc <- Xi' * H^r   (2 loads, 2 ops, 3 pmull), b .L..._g<r>
.L256_dec_w1_g4:     1 block, H^4: 14 AES rounds, its GHASH product,
                     its plaintext eor3 + store                        <- nblk=4
.L256_dec_w1_g3:     1 block, H^3, ditto                    <- fall through
.L256_dec_w1_g2:     1 block, H^2, ditto
.L256_dec_w1_g1:     1 block, H^1, ditto, + MODULO + tag + counter store
.L256_dec_w1_done:   shared epilogue
```

`nblk ∈ {5,6,7}` and `nblk > 8` never leave the baseline path. W = 1 throughout:
exactly one block per section, nothing widened, no per-size duplication, no
masking, frame 80 B.

### 1.2 The control

`_docs/fused-w1-reorder/gen_w1.py` re-emits this region with knobs. **With every
knob at its default it must reproduce `gen_mix.py`'s `s4h` object bit for bit**,
and `provision_w1.sh` refuses to continue otherwise. Checked on all four hosts,
and re-checked after every generator patch:

```
  === CONTROL: gen_w1.py defaults == gen_mix.py s4h, bit for bit ===
    w1=0e66d8c128580380761febca50250ceb s4h=0e66d8c128580380761febca50250ceb  SAME
```

`w1` is therefore the shipped ordering, and every number below that says
"vs `w1`" is a like-for-like comparison against what we ship. Every object in
the run is md5-identical across GV3, GV4, GV5 and r8g (gcc 13.3 / binutils 2.42),
so the static checks are literally the same objects on every core.

### 1.3 Reproduction of the published baseline

`w1`, Δ % vs HEAD, against `_docs/fused-mix4s4.md` §3.1's `s4h` row:

| host | 16 B | 32 B | 48 B | 64 B |
|---|---|---|---|---|
| V1 GV3 measured | −46.97 | −42.18 | −31.27 | −20.01 |
| V1 GV3 published | −47.06 | −42.14 | −31.27 | −20.00 |
| GV4 measured | −46.72 | −43.31 | −37.36 | −25.84 |
| GV4 published | −46.48 | −43.40 | −37.36 | −25.80 |
| r8g measured | −46.43 | −43.29 | −37.36 | −25.83 |
| r8g published | −46.13 | −43.40 | −37.39 | −25.80 |
| V3 GV5 measured | −45.92 | −42.68 | −39.68 | −29.52 |
| V3 GV5 published | −45.94 | −42.58 | −39.69 | −29.52 |

Worst discrepancy **0.30 points** (r8g 16 B, where that host's own A/A floor is
7.8 %). The harness reproduces the published run.

---

## 2. Every ordering tried

All 60 objects come from one generator. `gs` = start of the product window as a
fraction of the 14 AES round-pairs; `ksec` = end of that window in the
non-terminal sections; `k1` = the terminal section's product/MODULO split;
`clump` = number of product ops emitted back-to-back between two AES pairs;
`ct=head` = the ciphertext `ldr` becomes the section's first instruction;
`ldh` = *all three* of the section's loads (ciphertext + the two H^p table reads)
hoisted to the section head; `fold=late` = the three accumulator `eor`s moved
past the last AES round; `pre` = every product op emitted before AES round 0;
`ptr=end` = two integer `add`s in the shared prep (`x14 = x0+x9`, `x13 = x2+x9`)
and then **static** offsets `[x14,#-16r]` / `[x13,#-16r]` — legal because section
`r` always handles the block `r`-th from the *end* of the message; `dsp=f4` =
`nblk=4` falls through the dispatch into `stub_4` and on into `g4`;
`dsp=f4i` = additionally merges `stub_4`'s seed ops into `g4`'s AES rounds
(legal because section 4 runs **iff** `nblk = 4`) and drops its two duplicated
H^4 table loads; `sub=eq` = the sub-dispatch for `{1,2,3}` becomes a linear
ascending `cmp/b.eq` chain; `lay=br` / `lay=rev` = explicit branches between
sections / sections laid out ascending in memory with backward branches.

| name | ordering | `.text` |
|---|---|---:|
| `w1` | **the shipped ordering.** `ksec` 1.0, `k1` 0.35, `clump` 0 (one product op per AES pair), ciphertext `ldr` as the first *product* op (i.e. after AES unit 0), balanced dispatch tree, descending fall-through, post-index addressing | **5980** |
| `s4h` | the same object emitted by `gen_mix.py` — the control | 5980 |
| `ka` `kb` `kc` `kd` | `ksec` = 0.15 / 0.35 / 0.55 / 0.75 | 5980 |
| `k20` `k25` `k30` `k40` `k45` | `ksec` = 0.20 / 0.25 / 0.30 / 0.40 / 0.45 | 5980 |
| `Ka` `Kb` `Kc` `Kd` | `k1` = 0.15 / 0.20 / 0.55 / 0.70 | 5980 |
| `gs30` `gs50` | product window starts at 0.3 / 0.5 of the rounds (products *later*) | 5980 |
| `cl2` `cl3` `cl4` `cl5` `cl6` `cl12` | `clump` = 2 / 3 / 4 / 5 / 6 / 12 | 5980 |
| `cthd` | `ct=head` alone | 5980 |
| `ptre` | `ptr=end` alone | 5988 |
| `f4` | `dsp=f4` | 5976 |
| `f4i` | `dsp=f4i` | 5968 |
| `f4iE` `f4iH` | `f4i` + `ptr=end` / + `ct=head` | 5976 / 5968 |
| `f4ie` | `f4i` + `sub=eq` | 5960 |
| `lbr` `lrev` | `lay=br` / `lay=rev` | 5996 / 5996 |
| `c1` | `ksec` 0.35 + `ct=head` | 5980 |
| `c2` | `ksec` 0.35 + `clump` 3 | 5980 |
| `c3` | `ksec` 0.35 + `ct=head` + `clump` 3 | 5980 |
| `c4` | `ksec` 0.25 + `ct=head` + `clump` 2 | 5980 |
| `c5` | `c3` + `dsp=f4i` + `sub=eq` | 5960 |
| `c6` | `c3` with `k1` 0.25 | 5980 |
| `c7` | `ksec` 0.35 + `ct=head` + `clump` 4 | 5980 |
| `c8` | `c3` + `ptr=end` | 5988 |
| `d1` `d2` `d3` | `ksec` 0.35 + `clump` 4 / `ksec` 0.50 + `clump` 4 / `ksec` 0.35 + `clump` 6 | 5980 |
| `d4` | `ksec` 0.35 + `clump` 4 + `ct=head` | 5980 |
| **`d5`** | **`ksec` 1.0 (unchanged) + `clump` 4 + `ct=head` — THE WINNER** | **5980** |
| `pre1`…`pre6` | `pre=1` alone, + `ct=head`, + `k1` 0.25, + `k1` 0.50, + `f4i`/`sub=eq`, + `ptr=end` | 5980 (5960/5988 for `pre5`/`pre6`) |
| `e1` `e2` `e3` | `c3` + `ldh` / + `fold=late` / + both | 5980 |
| `e4` `e5` `e6` | `ksec` 0.45 `clump` 4 `ct=head` `ldh` / `c3`+`ldh`+`k1` 0.30 / `ksec` 0.35 `clump` 5 `ct=head` `ldh` | 5980 |
| `e7` `e8` | `c3` + `ldh` + `f4i`/`sub=eq` / + `ptr=end` | 5960 / 5988 |
| `dctr` `dct` `dbot` | **DIAGNOSTICS, deliberately wrong output, never shipped.** `ctr=free`: the per-section counter `add` deleted, every section reads the same `v29` — the upper bound on any counter scheme. `ctfree`: the ciphertext loaded once in the prep and never per section — the upper bound on any load-slack/prefetch scheme. `dbot`: both | 5964 / 5968 / 5952 |

### 2.1 What `d5` actually looks like

One section, baseline (left) vs `d5` (right) — 45 lines each, the same 45
instructions:

```
 .L..._g3:                                     .L..._g3:
                                          +      ldr    q26, [x0], #16          //ciphertext
   rev32  v0.16b, v29.16b                        rev32  v0.16b, v29.16b
   add    v29.4s, v29.4s, v31.4s                 add    v29.4s, v29.4s, v31.4s
   aese/aesmc  round 0                           aese/aesmc  round 0
-  ldr    q26, [x0], #16                    +    ldr    q24, [x6, #48]          //h3l|h3h
   aese/aesmc  round 1                       +   ldr    d25, [x6, #64]          //h3k
-  ldr    q24, [x6, #48]                     +   rev64  v20.16b, v26.16b
   aese/aesmc  round 2                       +   ext    v21.16b, v20…, #8
-  ldr    d25, [x6, #64]                          aese/aesmc  round 1
   aese/aesmc  round 3                            aese/aesmc  round 2
-  rev64  v20.16b, v26.16b                        aese/aesmc  round 3
   aese/aesmc  round 4                            aese/aesmc  round 4
-  ext    v21.16b, v20…, #8                  +    eor    v21.8b, v21.8b, v20.8b
   aese/aesmc  round 5                       +    pmull2 v22.1q, v20.2d, v24.2d
-  eor    v21.8b, v21.8b, v20.8b             +    pmull  v23.1q, v20.1d, v24.1d
   aese/aesmc  round 6                       +    pmull  v30.1q, v21.1d, v25.1d
   aese/aesmc  round 7                            aese/aesmc  round 5 … 9
-  pmull2 v22.1q, v20.2d, v24.2d             +    eor    v17.16b, v17.16b, v22.16b
   …                                         +    eor    v19.16b, v19.16b, v23.16b
-  pmull  v23…  -  pmull  v30…               +    eor    v18.16b, v18.16b, v30.16b
-  eor    v17…  -  eor    v19…  -  eor v18…       aese/aesmc  round 10 … 12
   aese  round 13                                 aese  round 13
   .inst eor3 v0, v26, v0, v15                    .inst eor3 v0, v26, v0, v15
   str    q0, [x2], #16                           str    q0, [x2], #16
```

The full diff is `_docs/fused-w1-reorder/w1-to-d5.patch`; the diff against HEAD
is `_docs/fused-w1-reorder/d5.patch`.

### 2.2 Slots, `aese`, size — the reordering is a permutation

`verify_mx.py` (the published convention: adjacent `aese`+`aesmc` = 1 slot,
`.inst`-encoded `eor3` counted, loads/stores excluded) gives **identical**
figures for every legal variant in the table:

| `nblk` | prep | stub | sections | slots | floor @4/cyc | `aese` | want 14n |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 6 | 5 | 39 | 50 | 12.50 | 14 | 14 ✓ |
| 2 | 6 | 5 | 65 | 76 | 19.00 | 28 | 28 ✓ |
| 3 | 6 | 5 | 91 | 102 | 25.50 | 42 | 42 ✓ |
| 4 | 6 | 5 | 117 | 128 | 32.00 | 56 | 56 ✓ |

The only variants that move a slot are the `f4i` family, and they move it
*within* `nblk = 4` (stub 5 → 0, sections 117 → 122, total still 128) and drop
two redundant loads (29 → 27). `d5` is 5980 B — byte-for-byte the same size as
what we ship.

---

## 3. Correctness

| check | result |
|---|---|
| **Control** | `gen_w1.py` defaults == `gen_mix.py` `s4h`, md5 `0e66d8c1…`, on all four hosts, re-verified after every generator change. |
| **Build fidelity** | Every object md5-identical on all four hosts. `obj/base.o` = `114cedb51f36c584e50843d2838d871e`. |
| **KAT, make-driven (r8g)** | In a scratch copy of `arm/` + `include/` (no tracked file touched, `make clean` never run in `arm/aes-gcm/kat`): `make aes-gcm/aesv8_gcm_8x_dec_256_wb.o` with the real `%.o : %.S` rule, then `make -C aes-gcm/kat run` with `kat_wb_dec` **deleted first**. For `base s4h w1 c3 c5 d5 e1 e3 cl4 kb f4i ptre`: **`make-built .o vs mk.sh .o: SAME` ×12** and `35 passed, 0 failed … KAT GATE: PASS` ×12. |
| **KAT, harness relink** | `kat.sh` (binary deleted first) for **every** variant on **every** host: 24 (round 1) + 14 + 14 + 8 = **60/60 `35 passed, 0 failed / KAT GATE: PASS`**. |
| **In-process byte-compare** | 12 slots per binary, `out`/`Xi`/`ivec`/**return value** compared against link slot 0 over **every whole-block length 1..256 blocks**, plus the "nothing written past `16*nblk`" assertion: `SELFCHECK OK` at the start of **every one of the 15 processes of every timing binary on every host** (13 binaries × 15 processes on V1 alone) and of every probe. Non-degeneracy (`out != in`) asserted at every length. |
| **`brk #0` liveness** | `brk #0` planted at section `r` must trap for every `nblk ∈ [r,4]` and survive `nblk < r`, 5, 6, 7, 8, 9, 16, 64. Measured for `w1`, `c3`, `c5`, `d5`, `d4`, `f4i`, `ptre`: `brk@g4 {4}` · `brk@g3 {3,4}` · `brk@g2 {2,3,4}` · `brk@g1 {1,2,3,4}`, **exact, nothing at 5..8 or above, on all four hosts.** That is the required "entry at `nblk` = 1,2,3,4 and non-entry at 5..8" proof, plus the fall-through boundary. |
| **Seed / section zap probes** | `zapN` (entry `N`'s seed zeroed) fails at exactly `{N}`; `zapall` at exactly `{1,2,3,4}`; `zsecP` (section `P`'s block products zeroed) at exactly `{P..4}`. **Exact for every probed variant on every host** — 26 probe results per host per pair of variants, 52 on r8g, **0 mismatches**. |
| **Guard-page memory safety** | in/out buffers flush against a `PROT_NONE` page above (`guard`) and below (`guardlo`), `nblk` 1..8: `base s4h w1 f4i ptre c3 c5 d5 d4` all survive all 16 combinations. This is the check that matters for `ptr=end`, whose static `[x14,#-16r]` offsets are the one variant that could over- or under-read. |
| **Adjacency** | `0 aese/aesmc violations`, whole-file scan, for every object built. No `aese`/`aesmc` pair is ever split. |
| **No dead AES** | `aese` count is exactly `14n` at each of the four entries, for every variant. |
| **Frame** | **80 B**: one `stp d8,d9,[sp,#-80]!`, `1 + 1` matching `ldp d8,d9,[sp],#80`, and **0** `add/sub sp` in source or `objdump`, for every variant. No new callee-saved register is written. |
| **`nblk > 8` content** | Normalised `objdump` (`objcmp.py`, addresses and branch targets masked): **`VERDICT: nblk>8 content UNCHANGED` for all 59 legal-ordering objects.** (The three deliberately-wrong diagnostics are excluded from the KAT/`objcmp` suite; they exist only to bound a lever from above and are never candidates.) |

---

## 4. Measurement

Discipline exactly as published: every variant `objcopy --redefine-sym`'d to a
distinct symbol and linked into **one** 12-slot binary (`bench12g.c`, the
published 12-length harness), timed round-robin with the slot order rotated
every rep, `taskset -c 3`, 200-call warm-up per pass, **best of 300 reps × 5
processes × 3 link orderings = 15 processes per binary per host**, `base` pinned
to link slot 0 in every ordering. Thirteen binaries on V1, four on each of the
other three hosts.

Two reference columns are given because they answer different questions:

* **Δ % vs HEAD** is what the brief's table reports, but `base` sits in link
  slot 0 and carries the placement lottery documented in
  `_docs/fused-t4p8.md` — on V1 it is worth up to 1.2 points at 48 B and on the
  V2 hosts up to 8 % at 16 B.
* **Δ % vs `w1`** compares two non-slot-0 variants in the same binary. Since
  `w1` *is* the shipped object, this is the number that decides whether an
  ordering is worth shipping. The scale of its own noise is visible directly:
  `s4h` and `w1` are **byte-identical objects in different link slots** and read
  −0.15 / +0.01 / −0.02 / +0.01 % at 16/32/48/64 B.

### 4.1 A/A noise floors (worst \|Δ\| between two copies of one object in any single process)

From the final binary `binW`, which carries A/A pairs for `base`, `w1` and both
leading candidates:

| host | pair | 16 | 32 | 48 | 64 | 80 | 128 | 4096 |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| **V1 GV3** | `base` | 0.43 | 0.36 | **1.16** | 0.25 | 0.16 | 0.23 | 0.74 |
| | `w1` | 0.97 | 0.05 | 0.10 | 0.25 | 0.10 | **2.26** | 0.24 |
| | `d5` | **1.68** | 0.68 | 0.36 | **0.08** | 0.12 | 0.24 | 0.24 |
| | `c3` | **1.83** | 0.41 | 0.86 | **0.05** | 0.34 | 0.68 | 0.20 |
| **GV4 V2** | `base` | **7.23** | 0.66 | 0.24 | 0.39 | 0.14 | 0.39 | 0.29 |
| | `w1` | 0.48 | 0.07 | 0.12 | 0.08 | 0.20 | 0.75 | 0.07 |
| | `d5` | 0.78 | 0.05 | 0.17 | 0.08 | 0.13 | 0.17 | 0.36 |
| **r8g V2** | `base` | **7.78** | 0.20 | 0.17 | 0.36 | 0.08 | 0.34 | 0.14 |
| | `w1` | 0.31 | 0.17 | 0.18 | 0.13 | 0.03 | 0.91 | 0.20 |
| | `d5` | 0.49 | 0.06 | 0.10 | 0.07 | 0.14 | 0.14 | 0.11 |
| **GV5 V3** | `base` | 0.08 | 0.05 | 0.03 | 0.04 | 0.02 | 0.06 | 0.01 |
| | `w1` | 0.01 | 0.04 | 0.04 | 0.05 | 0.05 | 0.03 | 0.01 |
| | `d5` | 0.01 | 0.12 | 0.10 | 0.29 | 0.06 | 0.06 | 0.01 |

**Consequences that are respected throughout this report.** At **64 B** — the
target — the floors are 0.05–0.29 %, so a 2 % effect is 7–40× the floor: safe.
At **48 B** the variant floors are ≤ 0.36 % but `base`'s is 1.16 % on V1, which
is why the 48 B column is read against `w1`. At **16 B** the floors are
1.7–1.8 % on V1 and 7–8 % on the V2 hosts: **no 16 B claim is made for V1 or V2**
(the observed 0.5–1.2 % is inside the floor); only V3, whose 16 B floor is
0.01 %, supports the −0.45 % reading there. At 128 B `w1`'s own floor reached
2.26 % on V1 in one binary, so the 128 B column is reported as "inside the
floor" and nothing more.

### 4.2 Round 1 on V1 — the six levers of the brief, measured

Δ % vs `w1` (the shipped ordering), V1 GV3, 15 processes per binary. Negative is
faster. Floors from §4.1.

| ordering | lever | 16 | 32 | 48 | **64** | 80 | 4096 |
|---|---|---:|---:|---:|---:|---:|---:|
| `s4h` | *byte-identical control* | −0.15 | +0.01 | −0.02 | **+0.01** | −0.11 | −0.01 |
| `ka` `ksec` 0.15 | 1 K-split | −0.83 | −0.20 | −0.88 | **−1.31** | +0.02 | +0.06 |
| `kb` `ksec` 0.35 | 1 K-split | −0.17 | +0.08 | −1.01 | **−1.50** | −0.01 | +0.13 |
| `kc` `ksec` 0.55 | 1 K-split | −0.04 | +0.14 | −1.01 | **−1.13** | −0.02 | +0.12 |
| `kd` `ksec` 0.75 | 1 K-split | −0.14 | +0.07 | −0.60 | **−0.73** | +0.02 | +0.04 |
| `Ka` `k1` 0.15 | 1 MODULO split | −1.23 | +0.24 | −0.58 | −0.33 | −0.51 | +0.07 |
| `Kb` `k1` 0.20 | 1 MODULO split | +0.92 | +0.42 | −0.54 | −0.35 | +0.05 | +0.12 |
| `Kc` `k1` 0.55 | 1 MODULO split | −0.31 | +0.59 | +0.87 | **+0.47** | +0.08 | +0.13 |
| `Kd` `k1` 0.70 | 1 MODULO split | +0.32 | +0.95 | +0.78 | **+0.74** | +0.00 | +0.14 |
| `gs30` | 1 products *later* | +0.78 | −0.03 | +1.49 | **+0.77** | +0.01 | +0.01 |
| `gs50` | 1 products *later* | +0.48 | −0.31 | +1.55 | **+0.90** | −0.02 | −0.03 |
| `cl2` | 5 burst size 2 | +0.17 | −0.20 | −0.42 | −0.51 | −0.10 | +0.04 |
| `cl3` | 5 burst size 3 | −0.53 | −0.29 | −1.06 | −0.83 | +0.08 | −0.00 |
| `cl4` | 5 burst size 4 | −0.35 | −0.12 | −1.21 | **−1.79** | −0.01 | −0.04 |
| `cthd` | 2 ciphertext load at head | −0.62 | −0.15 | −0.47 | **−1.02** | +0.02 | −0.03 |
| `ptre` | 3/2 no address chain, static offsets | −0.58 | +0.04 | +0.33 | **−0.13** | −3.39\* | −0.06 |
| `f4` | 6 `nblk=4` falls through (3 taken branches → 0) | +0.58 | +0.08 | +0.12 | **−0.16** | +0.10 | +0.11 |
| `f4i` | 6 + seed merged into section 4 | −0.38 | −0.01 | +0.04 | **+0.03** | −0.01 | −0.03 |
| `f4iH` | 6 + `ct=head` | −0.10 | −0.13 | −0.43 | −1.21 | +0.25 | −0.01 |
| `lbr` | 6 explicit branch between sections (3 → 7 taken) | −0.71 | +0.06 | +0.56 | **−0.19** | +0.30 | +0.14 |
| `lrev` | 6 sections laid out ascending, backward branches | −0.51 | +0.07 | +0.28 | **−0.34** | −0.09 | −0.04 |
| `dctr` | *diagnostic*: counter chain deleted | −0.77 | +0.12 | −0.72 | **−0.38** | +0.25 | +0.05 |
| `dct` | *diagnostic*: ciphertext loaded once in the prep | −0.10 | −0.73 | −1.10 | **−2.00** | +0.08 | −0.07 |
| `dbot` | *diagnostic*: both | +1.90 | −0.20 | −1.27 | **−2.82** | −0.01 | −0.06 |

\* `ptre`'s −3.39 % at 80 B is a link-slot artefact, not a result: `nblk = 5`
executes the byte-identical baseline path, and the reading does not reproduce
(−0.33 %, −0.02 % in later binaries). It is quoted here only because it is in
the raw table.

**The static branch trace behind the `f4` rows** (`branches_w1.py`, simulated
against the emitted assembly, taken branches *inside* the region — every entry
also pays the one `b.le` at the anchor):

```
w1     n=1: 2 taken  | n=2: 2 | n=3: 3 | n=4: 3   sections g4->g3->g2->g1
f4     n=1: 3        | n=2: 3 | n=3: 4 | n=4: 0
f4i    n=1: 3        | n=2: 3 | n=3: 4 | n=4: 0
lbr    n=1: 3        | n=2: 4 | n=3: 6 | n=4: 7
lrev   n=1: 3        | n=2: 4 | n=3: 6 | n=4: 7   sections g4->g3->g2->g1
```

Removing **three** taken branches from the `nblk = 4` path buys −0.16 / +0.03 %,
and *adding four* buys −0.19 %. On V1 the branches in this region are free.

### 4.3 Rounds 2–4 on V1 — the winning direction and its optimum

`ksec` and `clump` turned out to be the *same* lever: `ksec` 0.35 compresses the
12 product ops into the first 5 of 14 round-pairs, which necessarily produces
bursts of 2–3; `clump` produces bursts directly. Rounds 2–4 mapped the surface.
Δ % vs `w1`, V1 GV3 (each column is the mean of the binaries the variant
appeared in; the per-binary spread is ≤ 0.3 points):

| ordering | 16 | 32 | 48 | **64** |
|---|---:|---:|---:|---:|
| `ksec` sweep 0.20 / 0.25 / 0.30 / 0.40 / 0.45 | — | — | −1.15 / −0.97 / −0.95 / −1.33 / −1.31 | −1.55 / −1.26 / −1.26 / −1.45 / −1.45 |
| `clump` sweep 2 / 3 / 4 / 5 / 6 / 12 | — | — | −0.40 / −1.06 / −1.26 / −1.58 / −1.14 / −0.72 | −0.38 / −0.83 / −1.71 / −1.71 / −1.54 / −0.96 |
| `pre1` all products before AES round 0 | −0.28 | −0.21 | −0.29 | **−0.09** |
| `pre2` `pre3` `pre4` `pre5` `pre6` | — | — | −0.13…−0.56 | −0.42…−1.16 |
| `c1` `ksec` 0.35 + `ct=head` | −0.66 | −0.12 | −1.33 | **−2.39** |
| `c2` `ksec` 0.35 + `clump` 3 | −0.56 | −0.18 | −1.01 | −1.30 |
| `c3` `ksec` 0.35 + `ct=head` + `clump` 3 | −0.97 | −0.37 | −1.49 | **−2.26** |
| `c4` `c6` `c7` `c8` | −0.5 | −0.2…−0.7 | −1.3…−1.5 | −1.96…−2.19 |
| `c5` `c3` + `f4i` + `sub=eq` | −0.4 | −0.1 | −1.42 | **−2.50** |
| `d1` `d2` `d3` | +0.5 | −0.15…−0.46 | −1.25…−1.48 | −1.57…−1.94 |
| `d4` `ksec` 0.35 + `clump` 4 + `ct=head` | −1.20 | −0.69 | −1.38 | **−2.20** |
| **`d5` `clump` 4 + `ct=head`** | −1.00 | −0.42 | −1.49 | **−2.33** |
| `e1` `e3` `e5` `e6` `e7` `e8` (`ldh`, `fold=late` on top of `c3`) | −0.5 | −0.5 | −1.2…−1.6 | −1.98…−2.38 |
| `e2` `c3` + `fold=late` | −1.42 | −0.55 | −1.44 | **−2.31** |

Three readings that matter:

1. **The optimum is a plateau.** Every member of `{c1, c3, c5, d4, d5, e2, e7}`
   sits within 0.2 points of −2.3 % at 64 B, i.e. inside each other's noise.
   There is no knife edge to tune.
2. **The mechanism is bursts, not "as early as possible".** `pre1` — *every*
   product op emitted before AES round 0, the extreme of the direction — is
   worth only −0.09 %, far worse than bursts of 4 in the first third of the
   rounds. Pushing the whole product block ahead of the AES chain delays the
   chain that sets the section's length.
3. **The best legal ordering beats the "free ciphertext load" diagnostic.**
   `dct` (−2.00 %) removes the per-section load altogether and produces the wrong
   answer; `d5` (−2.33 %) keeps it and is faster. So the win is not simply load
   latency.

### 4.4 The final head-to-head — Δ % vs HEAD, all four hosts

Binary `binW`: `base baseAA w1 w1AA d5 d5AA c3 c3AA d4 c5 e2 cl4`, 15 processes
per host, absolute-min estimator. **V1 first.**

**V1 GV3 — Neoverse-V1, 2.5914 GHz**

| variant | 16 | 32 | 48 | **64** | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| HEAD | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `baseAA` | −0.05 | +0.01 | −0.37 | −0.11 | +0.01 | −0.27 | −0.25 | −0.02 | +0.55 | +0.45 | −0.50 | −0.56 |
| `w1` *(shipped)* | −46.95 | −42.18 | −31.49 | **−20.20** | +0.22 | −0.32 | −0.24 | −2.02 | +0.38 | −0.69 | −0.32 | −0.52 |
| `w1AA` | −47.09 | −42.19 | −31.48 | **−20.02** | +0.28 | −0.27 | −0.29 | −0.36 | +0.29 | −0.53 | −0.36 | −0.63 |
| **`d5`** | −47.59 | −42.49 | −32.47 | **−21.93** | +0.20 | −0.30 | −0.11 | −0.55 | +0.10 | −0.70 | −0.25 | −0.55 |
| **`d5AA`** | −47.08 | −42.48 | −32.50 | **−21.94** | +0.30 | −0.31 | −0.16 | −0.46 | −0.52 | −0.90 | −0.38 | −0.52 |
| `c3` | −47.01 | −42.43 | −32.46 | −21.88 | +0.19 | −0.29 | −0.10 | −0.81 | +0.37 | −0.89 | −0.16 | −0.47 |
| `c3AA` | −47.60 | −42.42 | −32.40 | −21.89 | +0.16 | −0.49 | −0.10 | −1.32 | +0.16 | −0.44 | −0.28 | −0.52 |
| `d4` | −47.55 | −42.59 | −32.43 | −21.84 | +0.22 | −0.42 | −0.10 | −0.73 | +0.28 | −0.88 | −0.56 | −0.53 |
| `c5` | −47.03 | −42.28 | −32.47 | **−22.11** | +0.30 | −0.71 | −0.08 | −1.18 | −0.33 | −0.44 | −0.52 | −0.54 |
| `e2` | −47.62 | −42.50 | −32.45 | −21.95 | +0.31 | −1.37 | −0.44 | −1.29 | −0.27 | −0.54 | −0.26 | −0.53 |
| `cl4` | −46.77 | −42.26 | −32.29 | −21.44 | +0.30 | −0.34 | −0.09 | −1.15 | −0.24 | −0.49 | −0.32 | −0.51 |

**GV4 — Neoverse-V2, 2.7916 GHz**

| variant | 16 | 32 | 48 | **64** | 80 | 128 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `w1` | −46.85 | −43.31 | −37.35 | **−25.84** | +0.01 | −0.42 | +0.24 |
| `w1AA` | −46.97 | −43.34 | −37.34 | **−25.83** | +0.02 | −0.53 | +0.21 |
| **`d5`** | −47.18 | −43.52 | −37.81 | **−27.26** | −0.07 | +0.23 | −0.04 |
| **`d5AA`** | −47.13 | −43.51 | −37.81 | **−27.26** | +0.04 | +0.18 | +0.27 |
| `c3` / `c3AA` | −47.06 / −47.11 | −43.52 | −37.78 | −27.24 | +0.02 | +0.24 | +0.19 |
| `d4` | −47.12 | −43.61 | −37.73 | −27.32 | +0.03 | +0.18 | +0.22 |
| `c5` | −47.08 | −43.47 | −37.56 | −27.36 | +0.03 | +0.23 | +0.14 |
| `e2` | −47.09 | −43.48 | −37.89 | −27.34 | +0.03 | +0.19 | +0.23 |
| `cl4` | −47.14 | −43.49 | −37.77 | −26.96 | +0.03 | −0.13 | +0.20 |

**`ec2r8g` — Neoverse-V2, 2.7929 GHz** (inter-instance reproduction of GV4)

| variant | 16 | 32 | 48 | **64** | 80 | 4096 |
|---|---:|---:|---:|---:|---:|---:|
| `w1` / `w1AA` | −48.38 / −48.39 | −43.40 / −43.33 | −37.39 | **−25.70 / −25.70** | +0.04 | −0.03 |
| **`d5` / `d5AA`** | −48.62 / −48.56 | −43.54 / −43.54 | −37.84 / −37.82 | **−27.12 / −27.12** | −0.08 | +0.07 |
| `c3` / `c3AA` | −48.51 / −48.55 | −43.56 | −37.82 | −27.13 / −27.12 | +0.02 | +0.09 |
| `d4` | −48.55 | −43.61 | −37.77 | −27.17 | +0.04 | +0.05 |
| `c5` | −48.60 | −43.49 | −37.59 | −27.24 | +0.03 | −0.28 |
| `e2` | −48.55 | −43.50 | −37.88 | −27.20 | +0.05 | +0.05 |
| `cl4` | −48.59 | −43.51 | −37.83 | −26.82 | +0.03 | +0.07 |

(r8g's `base` landed in the 16 B placement lottery — its own A/A floor there is
7.78 % — so the 16 B column on that host is not a result. The 32/48/64 B columns
reproduce GV4 to ≤ 0.15 points.)

**GV5 — Neoverse-V3, 3.2903 GHz** (the quiet host: A/A ≤ 0.12 % everywhere)

| variant | 16 | 32 | 48 | **64** | 80 | 128 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `w1` / `w1AA` | −45.92 / −45.93 | −42.67 | −39.69 | **−29.54** | −0.02 | +0.04 | +0.00 |
| **`d5` / `d5AA`** | −46.17 / −46.17 | −42.91 | −40.33 | **−31.03** | −0.03 | +0.02 | −0.00 |
| `c3` / `c3AA` | −46.13 | −42.91 | −40.23 | −30.77 | −0.06 | +0.05 | +0.01 |
| `d4` | −46.17 | −43.07 | −40.44 | −30.92 | −0.06 | +0.06 | +0.00 |
| `c5` | −46.14 | −42.83 | −40.20 | −30.62 | −0.09 | +0.05 | +0.00 |
| `e2` | −46.13 | −42.92 | −40.07 | −30.81 | −0.05 | +0.05 | +0.00 |
| `cl4` | −46.20 | −42.96 | −40.33 | −31.00 | −0.07 | +0.05 | +0.00 |

### 4.5 The brief's table, updated

Δ % vs HEAD, 16 / 32 / 48 / 64 B, V1 GV3 / V2 GV4 / V3 GV5:

| | 16 B | 32 B | 48 B | 64 B |
|---|---|---|---|---|
| baseline (as given) | −47.1 / −46.3 / −46.0 | −42.2 / −43.4 / −42.6 | −31.3 / −37.3 / −39.7 | **−20.0 / −25.9 / −29.5** |
| **`d5` measured** | −47.6 / −47.2 / −46.2 | −42.5 / −43.5 / −42.9 | −32.5 / −37.8 / −40.3 | **−21.9 / −27.3 / −31.0** |
| gain, vs the shipped object in the same binary | *inside floor* / *inside floor* / −0.45 | −0.54 / −0.38 / −0.41 | −1.43 / −0.74 / −1.07 | **−2.16 / −1.91 / −2.12** |

`d5` helps all three cores, and by the largest margin on V1 — the core the brief
named as the tie-breaker. There is no core and no length at which it loses
outside the noise floor.

### 4.6 Which candidate to ship

`c5` is nominally the best single reading on V1 (−22.11 vs HEAD) but the worst
of the family on V3 (−30.62), and it changes the dispatch and merges the entry
seed into section 4 — a structural change, not a reordering. `d4` is the best at
32 B on the two newer cores but slightly behind at 64 B on V1. **`d5` is the only
candidate that is at or near the top on every core at every length**, and it is
the *smallest possible* change: two ops move within each section, `.text` is
unchanged, the dispatch and stubs are untouched, `ksec`/`k1` keep their published
values.

| 64 B, Δ % vs the shipped ordering | V1 GV3 | GV4 | r8g | GV5 |
|---|---:|---:|---:|---:|
| **`d5`** (and its A/A twin) | **−2.16 / −2.18** | **−1.91 / −1.92** | **−1.92 / −1.91** | **−2.12 / −2.11** |
| `c3` (and twin) | −2.10 / −2.12 | −1.89 / −1.90 | −1.93 / −1.92 | −1.74 / −1.73 |
| `d4` | −2.05 | −1.99 | −1.99 | −1.96 |
| `c5` | −2.39 | −2.05 | −2.08 | −1.53 |
| `e2` | −2.19 | −2.02 | −2.02 | −1.80 |
| `cl4` | −1.55 | −1.51 | −1.51 | −2.07 |

---

## 5. Mechanism: achieved cycles, the ideal-work floor, and where the 1.4 cycles come from

Achieved cycles = min ns/call × the clock measured on that host. The floor is the
4-slots/cycle ideal for exactly `n` blocks of work (§2.2). From `binW`.

### 5.1 Achieved cycles and achieved/floor per `nblk`

| `nblk` | floor | | HEAD | `w1` *(shipped)* | **`d5`** |
|---:|---:|---|---|---|---|
| 1 | 12.50 | V1 | 67.68 / 5.41× | 35.82 / **2.866×** | 35.49 / **2.839×** |
| | | V2 | 65.96 / 5.28× | 34.97 / 2.798× | 34.85 / 2.788× |
| | | V3 | 64.54 / 5.16× | 34.89 / 2.791× | 34.74 / 2.779× |
| 2 | 19.00 | V1 | 68.49 / 3.60× | 39.61 / **2.085×** | 39.40 / **2.073×** |
| | | V2 | 65.17 / 3.43× | 36.92 / 1.943× | 36.81 / 1.937× |
| | | V3 | 64.62 / 3.40× | 37.05 / 1.950× | 36.90 / 1.942× |
| 3 | 25.50 | V1 | 71.09 / 2.79× | 48.88 / **1.917×** | 48.17 / **1.889×** |
| | | V2 | 67.66 / 2.65× | 42.39 / 1.663× | 42.07 / 1.650× |
| | | V3 | 66.97 / 2.63× | 40.39 / 1.584× | 39.95 / 1.567× |
| 4 | 32.00 | V1 | 74.84 / 2.34× | 59.79 / **1.868×** | 58.48 / **1.828×** |
| | | V2 | 69.93 / 2.19× | 51.97 / 1.624× | 50.97 / 1.593× |
| | | V3 | 68.92 / 2.15× | 48.57 / 1.518× | 47.54 / 1.486× |

`w1`'s column reproduces `_docs/fused-mix4s4.md` §4.1's `s4h` figures
(35.8 / 39.6 / 48.9 / 59.9 on V1 and 2.87 / 2.08 / 1.92 / 1.87×) exactly.

### 5.2 Where the gain is — the marginal cost of each additional block

| cycles for block … | | `w1` | **`d5`** | change |
|---|---|---:|---:|---:|
| 2nd | V1 | +3.79 | +3.91 | +0.12 |
| | V2 | +1.95 | +1.96 | +0.01 |
| | V3 | +2.16 | +2.16 | 0.00 |
| 3rd | V1 | +9.27 | +8.77 | **−0.50** |
| | V2 | +5.47 | +5.26 | **−0.21** |
| | V3 | +3.34 | +3.05 | **−0.29** |
| 4th | V1 | +10.91 | +10.31 | **−0.60** |
| | V2 | +9.58 | +8.90 | **−0.68** |
| | V3 | +8.18 | +7.59 | **−0.59** |

**The entire gain is in blocks 3 and 4, on all three cores.** Blocks 1 and 2 are
untouched to within 0.12 cycles. That is exactly the signature the mechanism
predicts:

* At `nblk` = 1 and 2 the region is **latency**-bound and the second section is
  absorbed into the first block's shadow. Where a section's µops sit relative to
  each other cannot matter, and it doesn't.
* From block 3 the slack is gone and the region becomes **issue/occupancy**-bound
  — the plateau that `_docs/fused-cascade-experiment.md` and
  `_docs/fused-mix4s4.md` §4.2 both attributed to the vector issue queue holding
  ~78 µops against a section's 26. There, the order in which a section's µops
  enter the queue decides how soon the *next* section's AES chain can enter it.
* A section's 12 GHASH-product µops are completely independent of every AES chain
  in the region. Spread one per round-pair (the shipped ordering) they are
  interleaved into the AES chain's issue stream for the whole section; delivered
  in three bursts of four in the first two thirds, they issue and retire promptly
  and free their queue entries early. The measured consequence is 0.5–0.7 cycles
  per block once the region is issue-bound, and 0 before that.

Two diagnostics bound the alternatives and confirm which resource is at stake:

| upper bound on … | how | V1, 64 B | verdict |
|---|---|---:|---|
| any counter scheme (`base + k`, prep precomputation, chain-breaking) | `dctr`: the per-section `add v29.4s` **deleted**, wrong output | **−0.38 %** | the counter chain is already fully hidden — it sits at the section head, two cycles deep, and the section is ≥ 28 cycles long. Any real scheme costs slots; the ceiling is 0.38 %. **Dead lever.** |
| any load-slack / prefetch scheme | `dct`: the ciphertext loaded **once** in the shared prep, wrong output | **−2.00 %** | worth something — but `d5` achieves **−2.33 %** while doing the loads properly, so the win is not load latency. |
| both together | `dbot` | −2.82 % | sub-additive with the real orderings. |

### 5.3 Why cross-section software pipelining is impossible, not merely unhelpful

The brief's lever 2 — place the load for block `n−1` at the end of section `n`
*and again* at the top of section `n−1` — cannot help, and the reason is
structural rather than empirical:

* Self-containment forces the in-section copy to exist (entering at `.L_{n−1}`
  must work).
* Both copies write the same architectural register, so the in-section copy is
  the later writer in program order. Register renaming makes every consumer in
  section `n−1` depend on the in-section copy. **The early copy is dead code on
  the fall-through path.**
* The only remaining benefit would be microarchitectural prefetch, and every
  byte here is L1-hot.

The same argument kills the more ambitious version (duplicating the *products*,
which are pure functions of the ciphertext and the H^p table and therefore
idempotent): the duplicate must write the same product registers, so the
in-section copy shadows it. It generalises: **under self-containment, the only
degrees of freedom are (a) the order of instructions within a section, (b) what
can be hoisted into the shared prep, and (c) the dispatch.** (b) is exhausted —
everything entry-independent is already there — and (c) is measured flat
(§4.2). That leaves (a), which is what `d5` exploits, and it also explains why
the plateau in §4.3 is so broad: there is not much left to move.

One genuine exception to (a) is worth recording because it is legal and was
built: **section 4 executes if and only if `nblk = 4`**, so its entry stub's
seed (`acc ← Xi'·H^4`) may be merged into it and interleaved with its AES rounds,
which also removes two duplicated H^4 table loads and three taken branches. That
is `f4i`/`c5`. It is worth −0.03 % on its own and about −0.2 % on top of `c3` on
V1 — real but small, core-dependent (it *loses* 0.2 points on V3), and it is a
structural change rather than a reordering. Recorded, not recommended.

---

## 6. Lever-by-lever verdict

| # | lever from the brief | verdict on V1 | verdict on V2 / V3 |
|---|---|---|---|
| 1 | **K-split sweep (`ksec`, `k1`)** | **NOT flat.** `ksec` 1.0 → 0.35 is −1.50 % at 64 B, −1.01 % at 48 B, against a 0.05–0.25 % floor. The whole band 0.20–0.45 works (−1.26…−1.55 %); above 0.55 the gain decays. `k1` is a one-sided constraint: ≤ 0.35 is fine, 0.55 and 0.70 cost +0.47 / +0.74 %. Moving the window *later* (`gs` 0.3/0.5) costs +0.77 / +0.90 %. | Present but smaller: `ksec` 0.35 gives −0.4 % on both. The published "1.2 % flat" grid was not wrong about V2's magnitude, but it was measured only on V2 and the conclusion does not transfer. |
| 2 | **Idempotent prefetch across sections** | **Structurally void** (§5.3) — no consumer can ever see the duplicated early load. The *goal* is worth at most −2.00 % (`dct` diagnostic), and the legal substitute, `ct=head` (the load becomes the section's first instruction), captures −1.02 % on its own and is part of the winner. | same |
| 3 | **Counter computation** | The chain **is** `add v29.4s,v29.4s,v31.4s` at each section head, and it is already hidden: deleting it entirely (`dctr`) is worth −0.38 %. `base + k` is in any case not directly available — section `r`'s counter is `base + (n − r)` and `n` is not known inside a section — and every construction that recovers it costs 3–5 extra SIMD slots in the shared prep. **Dead lever.** | not re-measured; the V1 upper bound already closes it. |
| 4 | **Round-key placement** | Settled before this run and not re-opened: hoisting all 15 keys into `v1..v15` (the `s4h`/`w1` baseline) beats per-section reloads (`s4`) by 1.8–7.2 points. The remaining freedom — hoisting the section's *other* loads to its head (`ldh`) — is flat: −0.0…−0.3 % on top of `c3`, and slightly negative at 64 B. | flat on V2 and V3 too (`e1`/`e3`/`e5`/`e7`, within ±0.3 of `c3`). |
| 5 | **Placement of ops around `aese`/`aesmc` pairs** | **This is the win.** Never split a pair (0 violations anywhere); but the *number of surrounding ops between consecutive pairs* matters: bursts of 4–5 beat one-per-pair by −1.7 %, bursts of 2 by only −0.5 %, and one giant burst of 12 or everything-before-round-0 (`pre1`) by −0.96 % / −0.09 %. The optimum is 3–5 ops per burst in the first two thirds of the rounds. | same shape, same optimum: `clump` 4 is −1.51 % on V2 and −2.07 % on V3. |
| 6 | **Section order / early-exit** | **Flat.** `nblk = 4` from 3 taken branches to 0 (`f4`, `f4i`): −0.16 / +0.03 %. From 3 to 7 (`lbr`): −0.19 %. Sections laid out ascending with backward branches (`lrev`): −0.34 %. A literal ascending-with-early-exit variant was designed and *not* built, for a structural reason worth recording: sections must keep static H powers and static end-relative addresses, which ascending order allows, but the shared MODULO/tag tail would then have to follow the *highest* executed section, so it could no longer be interleaved into a section's AES rounds — the `k1` sweep shows that placement is worth up to 0.74 % on its own. Ascending order therefore starts from behind. | not re-measured on V2/V3; V1's flatness closes it. |
| — | **`ptr=end`** (extra, not in the brief): both post-index address chains removed, all four loads and stores given static offsets from `x0+x9` / `x2+x9` | **Flat**: −0.13 % alone, −0.00…+0.06 % on top of `c3`. Correct and guard-page clean, but it buys nothing and costs 8 B. | not pursued. |
| — | **`fold=late`** (extra): the three accumulator `eor`s — the only ops on the cross-section GHASH chain — moved past the last AES round | **Flat**: +0.06 % vs `c3` on V1, −0.1…+0.2 % elsewhere. | flat |

---

## 7. Artefacts

Everything is under `_docs/fused-w1-reorder/` and is gitignored.

| file | what |
|---|---|
| `gen_w1.py` | the generator. Imports `fused-cascade/gen_cascW.py`, `fused-truncation/gen_cascWt.py` and `fused-mix4s4/gen_mix.py`; with defaults it reproduces `s4h` bit for bit. |
| `provision_w1.sh` `provision2_w1.sh` `provision3_w1.sh` `provision4_w1.sh` | rounds 1–4: generate, assemble, and run every static check (`.text`, md5, slots, `aese`, adjacency, `objcmp`, KAT, byte-compare). |
| `setup_w1.sh` | stands up `/tmp/fsw` on a host as a copy of the already-provisioned `/tmp/fsp`. |
| `mkbench6.py` `build6.sh` `buildw.sh` `measure_w1.sh` | harness plumbing. `buildw.sh` links the **published** `bench12g.c` (12 lengths); `measure_w1.sh` is the published discipline (300 reps × 5 processes × 3 link orderings, `base` in slot 0). |
| `verify_w1.sh` `probe_w1.sh` `branches_w1.py` `makekat_w1.sh` | the correctness suite: frame/size, dispatch, `objcmp`, slots, byte-compare, KAT; `brk`/zap/guard probes; the static taken-branch trace; the make-driven KAT on the dev host. |
| `analyze_w1.py` `rel_w1.py` | min-estimator Δ % vs HEAD with A/A floors, and Δ % vs the shipped ordering. |
| `d5.patch` | **the winner as a diff against HEAD** (adds the whole fused region). |
| `w1-to-d5.patch` | **the winner as a diff against the current W=1 ordering** — the reordering itself, 4 sections × 12 lines moved. |
| `logs/` | all 20 timing logs (13 on V1), 4 provisioning logs per host, 3 verification logs, 4 probe logs, the make-driven KAT log. |

Reproduce on any of the four hosts:

```
  bash /tmp/setup_w1.sh                       # /tmp/fsw, control must print SAME
  CORE=3 ./provision2_w1.sh && CORE=3 ./provision3_w1.sh
  CORE=3 ./verify_w1.sh && CORE=3 PROBEV="d5 c3" ./probe_w1.sh
  ./measure_w1.sh binW <host> 3 300 5 base baseAA w1 w1AA d5 d5AA c3 c3AA d4 c5 e2 cl4
  python3 analyze_w1.py logs/binW_<host>.log && python3 rel_w1.py logs/binW_<host>.log
```

---

# 8. Addendum — `rejoin`: one `ret` for `nblk >= 1`, and what it costs

Added after `d5` was accepted, to satisfy a ruling from the proof pipeline. This
section is appended; nothing above it was rewritten.

## 8.1 The problem and the ruling

`AESV8_GCM_8X_DEC_256_CORRECT` pins one literal exit address in its
postcondition (`read PC s = word (pc + <core-exit>)`). For `nblk >= 1` the
baseline function has exactly one `ret`, at the end of `.L256_dec_epilogue`
(source line 1518). The fused region's `_done` block **duplicates that
epilogue's six-instruction frame restore and adds a second `ret`**, so for
`nblk = 1..4` the function exits somewhere the theorem does not name. Verified
directly rather than assumed, with `onret_w1.py` on the accepted `d5` object:

```
== 1. static inventory: 3 `ret` in src/w1.S
   line 1521  governed by .L256_dec_epilogue
   line 1992  governed by .L256_dec_mxh_done        <-- the defect
   line 1996  governed by .L256_dec_ret
== 3. dynamic trace: which `ret` line does each nblk reach?
   nblk>8 (via .L256_dec_epilogue) -> ret at line 1521
   nblk=1 -> ret at line 1992   *** DIFFERENT ***
   nblk=2 -> ret at line 1992   *** DIFFERENT ***
   nblk=3 -> ret at line 1992   *** DIFFERENT ***
   nblk=4 -> ret at line 1992   *** DIFFERENT ***
VERDICT: FAILED
```

The ruling — change the code so there is one `ret` — is implemented as the
generator knob `rejoin=1`, doing exactly the two things specified and nothing
else. The **third** `ret`, `.L256_dec_ret`'s `mov w0,#0` + `ret` zero-length /
non-whole-blocks early exit, is pre-existing, correct, discharged one level up
in the subroutine wrapper, and is left byte-identical — `onret_w1.py` asserts
that too.

## 8.2 The change, in full

`d5` → `d5r` is 26 lines of diff (`_docs/fused-w1-reorder/d5-to-d5r.patch`) and
this is all of it:

```diff
@@ -1512,6 +1512,7 @@
        ext     v19.16b, v19.16b, v19.16b, #8
        rev64   v19.16b, v19.16b
        st1     { v19.16b }, [x3]
+.L256_dec_frame_restore:  //[W1] the ONE frame restore; the fused region rejoins here
        mov     x0, x9

        ldp     d10, d11, [sp, #16]
@@ -1983,13 +1984,8 @@
 .inst  0xce003f40  //eor3 v0.16b, v26.16b, v0.16b, v15.16b  //H^1 block - result
        str     q0, [x2], #16

-.L256_dec_w1_done:      //[CASCW] epilogue
-       mov     x0, x9
-       ldp     d10, d11, [sp, #16]
-       ldp     d12, d13, [sp, #32]
-       ldp     d14, d15, [sp, #48]
-       ldp     d8, d9, [sp], #80
-       ret
+.L256_dec_w1_done:      //[W1] rejoin the one epilogue: single `ret` for nblk >= 1
+       b       .L256_dec_frame_restore
```

**The label insertion adds, moves and removes no instruction**, which is why the
`nblk > 8` stream is untouched. Net −5 instructions, −20 B.

### Verified by construction: the label lands after every store on the main path

The generator asserts the anchor `\tmov\tx0, x9` is unique in the kernel (it is —
line 1513) and that no `st`/`str` appears in the six non-blank lines from the
anchor onward (they are `mov x0,x9` + 4 × `ldp` + `ret`). Independently, the
stores in and before the epilogue are:

| store | where | relative to `.L256_dec_frame_restore` |
|---|---|---|
| `str q30, [x16]` — updated counter | lines 1469 / 1696, before the epilogue label | **before** |
| `st1 { v12.16b}, [x2]` — last plaintext block | line 1497, inside the epilogue | **before** |
| `st1 { v19.16b }, [x3]` — the tag | line 1512, inside the epilogue | **before** |
| — | line 1513 onward | *no store* |

So the main path repeats nothing and skips nothing: everything above the new
label still runs exactly once for `nblk > 8`, and the fused path joins only the
frame restore.

### Confirmed: the fused path does its own three stores before branching

It does, today, unchanged by `rejoin`. In the terminal section `g1`:
`str q0, [x2], #16` (its plaintext block, and each of the four sections stores
its own), then in `late_ops`: `st1 { v19.16b }, [x3]` (tag) and
`rev32 v30, v29` + `str q30, [x16]` (counter). `d5r`'s `nblk = 4` load count
drops from 29 to 25 — exactly the four `ldp`s that are no longer duplicated —
and its store count is unchanged.

## 8.3 Validation of `d5r`

| check | result |
|---|---|
| **Control still holds** | with `rejoin=0` (the default) `gen_w1.py` still reproduces `gen_mix.py`'s `s4h` bit for bit: `w1chk2 = s4h = 0e66d8c128580380761febca50250ceb`. The knob is off by default and changes nothing when off. |
| **Exactly one `ret` for `nblk >= 1`** | `onret_w1.py src/d5r.S w5r src/base.S`: static inventory **2 `ret`** (the frame restore at line 1522, and `.L256_dec_ret`) — the same count as `base.S`, whose two are at lines 1518 and 1720; `objdump` `ret` count **2**, matching `base.o`'s 2 (`w1`/`d5` have 3). Dynamic trace: `nblk = 1, 2, 3, 4` **all reach the same `ret` line as `nblk > 8`**. `VERDICT: one exit address for nblk >= 1`. Same for `w1r`. |
| **`.L256_dec_ret` untouched** | `== 2. .L256_dec_ret stub fidelity: UNTOUCHED  ['mov\tw0, #0x0', 'ret']` — compared instruction-for-instruction against `base.S`. |
| **`nblk > 8` content** | `VERDICT: nblk>8 content UNCHANGED` for `d5r` and `w1r` (normalised `objdump`). |
| **KAT, genuine relink** | `d5r`, `w1r`, `w1chk2`: `35 passed, 0 failed … KAT GATE: PASS` on **all four hosts**. |
| **KAT, make-driven (r8g)** | through the real `arm/Makefile` + `arm/aes-gcm/kat/Makefile`, `kat_wb_dec` deleted first: `base`, `d5`, `d5r`, `w1r` → **`make-built .o vs mk.sh .o: SAME` ×4** and `KAT GATE: PASS` ×4. |
| **In-process byte-compare** | 12 slots (`base baseAA w1 w1AA d5 d5AA d5r d5rAA w1r c3 d4 c5`), `out`/`Xi`/`ivec`/return over **all 256 whole-block lengths**, plus the no-write-past-`16*nblk` assertion: `SELFCHECK OK` at the start of all 15 processes of `binR` on every host. |
| **`brk` / zap / zsec probes** | `d5r` on GV3, GV4 and GV5: `brk@g4 {4}` · `brk@g3 {3,4}` · `brk@g2 {2,3,4}` · `brk@g1 {1,2,3,4}`, `zsecP {P..4}`, `zapN {N}`, `zapall {1,2,3,4}` — **13/13 exact per host, nothing at 5..8 or above.** |
| **Guard-page** | `base s4h w1 c3 d5 d5r w1r` × {`guard`,`guardlo`} × `nblk` 1..8 all survive, on all three GV hosts. |
| **Adjacency / `aese` / slots** | `0 violations`; `aese` = 14n; slots **50 / 76 / 102 / 128** — identical to `w1` and `d5`. |
| **Frame** | 80 B: `push80=1 pop80=1`, `src sp-adjust=0`, `objdump sp add/sub=0`. Note `pop80` is now **1**, not 2 — the duplicate frame restore is gone. |
| **`.text`** | **5960 B** (`w1`/`d5` 5980) — 20 B smaller, i.e. the 5 instructions. |
| **Taken branches inside the region** | `d5r`: 3 / 3 / 4 / 4 for `nblk` = 1/2/3/4, one more than `d5`'s 2 / 2 / 3 / 3, as the design implies. |

## 8.4 Measurement — `binR`, all four hosts

`base baseAA w1 w1AA d5 d5AA d5r d5rAA w1r c3 d4 c5` in one binary, 300 reps ×
5 processes × 3 link orderings = 15 processes per host, `base` in slot 0.
`w1r` is the shipped ordering **plus** `rejoin`, so the rejoin cost can be read
off with the ordering held fixed.

### The rejoin cost in isolation (`w1r` vs `w1`, same ordering, same binary)

| Δ % | 16 B | 32 B | 48 B | **64 B** | 80 B | 4096 B |
|---|---:|---:|---:|---:|---:|---:|
| V1 GV3 | −0.78 | +0.01 | +0.00 | **−0.02** | −0.13 | +0.68 |
| GV4 V2 | +0.07 | +0.00 | +0.03 | **−0.04** | +0.00 | +0.09 |
| r8g V2 | +0.02 | +0.00 | +0.03 | **−0.04** | +0.03 | −0.09 |
| GV5 V3 | +0.00 | −0.02 | −0.03 | **−0.03** | +0.00 | +0.00 |

**The extra taken branch is free.** Every reading is ≤ 0.07 % in magnitude and
inside that host's A/A floor (the −0.78 % at 16 B on V1 sits under a 1.6 % floor;
the V3 host, whose floor is 0.02 %, reads −0.00 / −0.02 / −0.03 / −0.03). The
sign is if anything slightly negative — 5 fewer instructions in the I-cache.

### The final design (`d5r`) vs the accepted ordering (`d5`) and the shipped ordering (`w1`)

Δ % vs `w1`, same binary, A/A twins shown as `x / xAA`:

| variant | | 16 B | 32 B | 48 B | **64 B** |
|---|---|---:|---:|---:|---:|
| `d5` | V1 | −1.67 / −0.30 | −0.53 / −0.54 | −1.56 / −1.59 | **−2.39 / −2.40** |
| **`d5r`** | V1 | −1.47 / −1.52 | −0.54 / −0.54 | −1.63 / −1.63 | **−2.37 / −2.38** |
| `d5` | GV4 | −0.61 / −0.45 | −0.37 / −0.37 | −0.69 / −0.67 | **−1.94 / −1.93** |
| **`d5r`** | GV4 | −0.45 / −0.46 | −0.39 / −0.37 | −0.43 / −0.51 | **−1.88 / −1.86** |
| `d5` | r8g | −0.45 / −0.26 | −0.38 / −0.38 | −0.69 / −0.76 | **−1.95 / −1.94** |
| **`d5r`** | r8g | −0.30 / −0.30 | −0.38 / −0.37 | −0.53 / −0.42 | **−1.89 / −1.86** |
| `d5` | GV5 | −0.46 / −0.45 | −0.40 / −0.40 | −1.07 / −1.06 | **−2.16 / −2.17** |
| **`d5r`** | GV5 | −0.45 / −0.46 | −0.39 / −0.40 | −1.06 / −1.06 | **−2.13 / −2.13** |

**Rejoin costs 0.02 / 0.06 / 0.06 / 0.03 points at 64 B** (V1 / GV4 / r8g / GV5)
— an order of magnitude under the ~0.5-point threshold, and at or inside the A/A
floors (0.06 / 0.06 / 0.06 / 0.43 for the `d5`/`d5r` pairs at 64 B). At 48 B it
is 0.0 on V1 (in fact `d5r` reads 0.05 points *better*) and on V3, and ~0.2
points on the two V2 hosts. At 32 B and 16 B it is nil. **The landing is
−1.86…−2.38 %, inside the predicted −1.8…−2.2 % band.**

### Δ % vs HEAD — the final design

| host | 16 B | 32 B | 48 B | **64 B** | 80 B | 128 B | 4096 B |
|---|---:|---:|---:|---:|---:|---:|---:|
| **V1 GV3** `d5r` / `d5rAA` | −47.50 / −47.53 | −42.52 | −32.33 | **−21.92 / −21.93** | +0.28 | −0.15 | −0.40 |
| V1 GV3 `w1` (shipped) | −46.72 | −42.21 | −31.21 | −20.02 | +0.35 | −0.18 | −1.19 |
| **GV4 V2** `d5r` / `d5rAA` | *(floor)* | −43.56 / −43.55 | −37.66 / −37.70 | **−27.23 / −27.22** | −0.01 | +0.28 | −0.02 |
| GV4 V2 `w1` | *(floor)* | −43.34 | −37.39 | −25.84 | +0.01 | −0.49 | −0.05 |
| **r8g V2** `d5r` / `d5rAA` | *(floor)* | −43.54 / −43.54 | −37.70 / −37.63 | **−27.24 / −27.21** | +0.01 | +0.19 | −0.02 |
| r8g V2 `w1` | *(floor)* | −43.33 | −37.37 | −25.84 | −0.00 | −0.55 | +0.05 |
| **GV5 V3** `d5r` / `d5rAA` | −46.17 / −46.17 | −42.89 / −42.90 | −40.31 / −40.31 | **−31.02 / −31.03** | −0.05 | +0.03 | +0.00 |
| GV5 V3 `w1` | −45.92 | −42.67 | −39.67 | −29.53 | −0.02 | +0.00 | +0.00 |

*(floor)* = `base` landed in the 16 B link-slot lottery in this binary on the V2
hosts — its own A/A floor there is 4.38 % (GV4) and 7.55 % (r8g) — so no 16 B
Δ-vs-HEAD is claimed on those two. On V1 the 16 B floor is 1.6 % and on V3 it is
0.02 %.

**The brief's table, final:**

| | 16 B | 32 B | 48 B | 64 B |
|---|---|---|---|---|
| baseline (as given) | −47.1 / −46.3 / −46.0 | −42.2 / −43.4 / −42.6 | −31.3 / −37.3 / −39.7 | **−20.0 / −25.9 / −29.5** |
| `d5` (ordering only) | −47.6 / −47.2 / −46.2 | −42.5 / −43.5 / −42.9 | −32.5 / −37.8 / −40.3 | **−21.9 / −27.3 / −31.0** |
| **`d5r` (final: ordering + rejoin)** | −47.5 / *floor* / −46.2 | −42.5 / −43.6 / −42.9 | −32.3 / −37.7 / −40.3 | **−21.9 / −27.2 / −31.0** |

## 8.5 Achieved cycles and floor ratios, `d5r`

Clocks as measured: V1 2.5914, GV4 2.7916, GV5 3.2903 GHz.

| `nblk` | floor | | `w1` | `d5` | **`d5r`** |
|---:|---:|---|---|---|---|
| 1 | 12.50 | V1 | 35.89 / 2.871× | 35.47 / 2.838× | **35.53 / 2.842×** |
| | | V2 | 35.03 / 2.803× | 34.82 / 2.786× | **34.88 / 2.790×** |
| | | V3 | 34.89 / 2.791× | 34.73 / 2.779× | **34.73 / 2.779×** |
| 2 | 19.00 | V1 | 39.60 / 2.084× | 39.39 / 2.073× | **39.39 / 2.073×** |
| | | V2 | 36.94 / 1.944× | 36.81 / 1.937× | **36.80 / 1.937×** |
| | | V3 | 37.05 / 1.950× | 36.90 / 1.942× | **36.90 / 1.942×** |
| 3 | 25.50 | V1 | 48.90 / 1.918× | 48.12 / 1.887× | **48.10 / 1.886×** |
| | | V2 | 42.38 / 1.662× | 42.09 / 1.651× | **42.17 / 1.654×** |
| | | V3 | 40.38 / 1.584× | 39.96 / 1.567× | **39.96 / 1.567×** |
| 4 | 32.00 | V1 | 59.92 / 1.873× | 58.48 / 1.828× | **58.50 / 1.828×** |
| | | V2 | 51.99 / 1.625× | 50.99 / 1.593× | **51.02 / 1.594×** |
| | | V3 | 48.57 / 1.518× | 47.52 / 1.485× | **47.54 / 1.486×** |

At `nblk = 4` the achieved/floor ratio is **1.828× (V1), 1.594× (V2), 1.486×
(V3)** against the shipped 1.873 / 1.625 / 1.518 — `d5r` keeps the whole of
`d5`'s gain to within 0.001× of the ratio (0.02–0.03 cycles). One extra taken branch, placed after
every store and after the last dependent instruction of the whole region, retires
in the shadow of work already in flight; this is the same result as §4.2's
dispatch experiments (3 taken branches → 0 → 7 all inside 0.34 %), now confirmed
for the one branch we are actually adding.

## 8.6 The final design — how to produce it

One line, from the kernel at HEAD:

```
  python3 gen_w1.py src/base.S src/d5r.S w5r k=1.0 K=0.35 ct=head clump=4 rejoin=1
```

(`w5r` is only the label prefix; `k`/`K` are the published split points, so the
ordering knobs that actually differ from HEAD's fused region are
`ct=head clump=4` and the new `rejoin=1`.)

| patch | from → to |
|---|---|
| `_docs/fused-w1-reorder/d5r.patch` | **HEAD kernel → the FINAL design** (`d5` ordering + rejoin). Apply this one. |
| `_docs/fused-w1-reorder/w1-to-d5r.patch` | current W=1 fused region → final design (ordering + rejoin) |
| `_docs/fused-w1-reorder/d5-to-d5r.patch` | `d5` → final design: the rejoin change alone, 26 lines |
| `_docs/fused-w1-reorder/d5.patch`, `w1-to-d5.patch` | as before, the ordering change without rejoin |

New tooling: `provision5_w1.sh` (round 5: generate, validate, KAT, byte-compare)
and **`onret_w1.py`** (the one-`ret` checker: static inventory with governing
labels, `.L256_dec_ret` stub fidelity against the baseline, and a dynamic trace
proving `nblk` = 1,2,3,4 reach the same `ret` as `nblk > 8`). Logs:
`logs/binR_{gv3,gv4,gv5,r8g}.log`, `logs/prov5_*.txt`, `logs/probe5_*.txt`,
`logs/makekat5_r8g.txt`.

**Verdict: adopt `rejoin`.** It restores the invariant the exported theorem
needs, is 5 instructions and 20 B smaller, and costs 0.02–0.06 points at 64 B —
inside the noise floor on every core.

*(Note on the dev host: `ec2r8g` carried two idle `hol-light-mcp` listener
processes and one defunct `ocaml-hol`; load average was 0.00–0.04 throughout and
no gate or proof was running, so the round-5 work there — provisioning, KAT,
make-driven KAT and one 15-process timing binary — went ahead. The tracked tree
is still at `c2609cf8` with only untracked files.)*
