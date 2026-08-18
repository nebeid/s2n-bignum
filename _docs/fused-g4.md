# `g4` — ONE 4-wide interleaved group, ONE entry, for every `nblk` ≤ 4 — measurement only

Companion to `_docs/fused-small-path-experiment.md` (the eight-body design),
`_docs/fused-truncation-curve.md` (the truncation family `t2…t8`),
`_docs/fused-cascade-experiment.md` (the width sweep),
`_docs/fused-t4p8.md` (separate bodies for `{1,2,3,4,8}`) and
`_docs/fused-mix4s4.md` (one shared mixed-width region). Same kernel, same
harness, same discipline, and every retained body is emitted by the **same
published generators**, so this is a controlled extension of the family.

Kernel `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` at local HEAD `c2609cf8`;
`obj/base.o` md5 `114cedb51f36c584e50843d2838d871e` — the object `arm/Makefile`
produces in the synced tree, **and the object all four hosts built locally**.
**No HOL Light, no `.ml`, no proofs, no gates.** All work in `/tmp/fsp` (and
`/tmp/fst` for the make-driven KAT on the dev host); **no tracked file was
modified, `~/clean-gate` and `~/kat-check` were not touched, and no instance was
started, stopped, rebooted or terminated.**

| host | core | part | clock measured on the spot |
|---|---|---|---|
| GV3 | Neoverse-V1 | `0xd40` | **2.5909 GHz** |
| GV4 | Neoverse-V2 | `0xd4f` | **2.7917 GHz** |
| GV5 | Neoverse-V3 | `0xd84` | **3.2905 GHz** |
| `ec2r8g` | Neoverse-V2 (dev) | `0xd4f` | **2.7926 GHz** |

`r8g` and GV4 are the same microarchitecture and reproduce each other to
**≤ 0.3 points at every length** and to **≤ 0.1 cycles** in the decomposition of
§4. Every object is md5-identical on all four hosts (same gcc 13.3 /
binutils 2.42), so the static checks are literally the same objects on every core.

---

## 0. Headline

| | |
|---|---|
| **Was it built?** | **Yes, and it is correct.** KAT **35/35 / `KAT GATE: PASS`** for all 11 variants on all 4 hosts by genuine relink, **and** through the real `arm/Makefile` + `arm/aes-gcm/kat/Makefile` on r8g with the make-built object **byte-identical** to the harness object (10/10 `SAME`). In-process byte-compare of `out`/`Xi`/`ivec`/return over **all 256 whole-block lengths × 12 slots** on every host, **plus** a check that nothing is written past `16*nblk`. **33/33 liveness, lane-mapping, mis-entry and guard-page probes exact on every host.** `aese` count exactly **56 at every `nblk`** (that is the design). **0 adjacency violations.** Frame **80 B**. `nblk > 8` content **instruction-for-instruction unchanged**. |
| **Structure** | **1 region, 1 entry label, 1 straight-line path**, 2 not-taken dispatch instructions on the fall-through — the same 2 as `dsp0`, i.e. fewer than `t4p8`'s 4. |
| **`.text`** | **5948 B (×1.197)** — the **smallest** member of the family that fuses anything, 1364 B smaller than `t4` and 2884 B smaller than `t4p8`. Hoisted keys: 5964 B (×1.201). |
| **THE PRIMARY RESULT — is the discarded AES free?** | **YES. The standing inference is CONFIRMED, and the margin is large.** Running **4 blocks of AES when 1 is needed costs +1.9 / +1.2 / +0.3 cycles** (V1 / V2 / V3) = **+5.0 / +3.5 / +0.9 %**, and at `nblk` = 2, 3 it is +1.6/+0.5/+0.1 and +1.9/+0.9/+0.8 cycles. At `nblk` = 4 it is **0.0** by construction. Measured with `a4`, a control that differs from `t4` in **exactly one generator parameter** (`n_aes = 4` instead of `n`). |
| **…so why is `g4` slow?** | **Because a single region also forces the GHASH half to be uniform and branch-free, and THAT is what costs.** Decomposed on all four hosts (§4): of `g4`'s **+15.3 cycles** over `t4` at `nblk` = 1 (V2), **+1.2 is the discarded AES**, **+6.4 is the four-lane GHASH that must run whatever `nblk` is**, **+1.1 is the clamped register-offset addressing**, and **+6.6 is the branch-free masking**. The discarded blocks are **8 % of the loss**. |
| **Δ % vs HEAD, 16/32/48/64 B** | **`g4` −24.9/−25.8/−27.7/−29.8 (V1), −23.4/−23.7/−26.5/−29.7 (V2 GV4), −23.4/−23.7/−26.5/−29.0 (V2 r8g), −23.8/−23.9/−26.6/−28.7 (V3)** against `t4`'s −46.7/−43.9/−43.5/−41.3 … −46.3/−42.4/−44.8/−42.0. `g4` gives up **22–24 points at 16 B, 18–19 at 32 B, 16–18 at 48 B, 11–13 at 64 B**. |
| **80–128 B and ≥ 256 B — the fall-back check** | **Free, on every host.** Every `g4` reading at 80/96/112/128/256/512/1024/4096 B is inside that host's own A/A floor: ≤ 0.45 % on V3 (floor 0.03–0.50), ≤ 0.31 % on the V2 hosts, and on V1 the two non-trivial numbers (−1.70 % at 80 B, +0.02 % at 128 B) sit under a 2.31 % floor. **128 B is exactly a wash** (+1.23 / +0.66 / +0.68 / −0.02 % against the `dsp0` control). The 2 dispatch instructions cost nothing measurable. |
| **THE DECIDING COMPARISON — `g4` vs the cascade 4→1** (both one region, both fused, no per-size bodies; `mix4s4`'s `nblk` ≤ 4 rows *are* the cascade, and they were timed in the **same binary and the same processes** here, reproducing the published numbers to ≤ 0.4 points) | **`g4` loses at 16, 32 and 48 B and wins only at 64 B.** Points, +ve = `g4` slower (V1/GV4/r8g/V3): 16 B **+22.1/+22.6/+22.5/+22.2**, 32 B **+16.5/+19.6/+19.6/+18.7**, 48 B **+3.5/+10.8/+10.8/+13.1**, 64 B **−9.8/−3.8/−3.1/+0.9**. The predicted mechanism is real — `g4`'s marginal cost per extra block is **0.0 ± 0.6 cyc** against the cascade's **8.00/5.60/4.60** — but `g4` starts **≈14.5 cycles behind**, and that constant is only repaid by `nblk` = 4, on V1 and V2 only, never on V3 inside the fused range. §3.3 |
| **Does key hoisting pay?** | **No — it is a measured tie-to-slightly-negative, and there is a structural reason.** `g4` has exactly **one** group, so both key modes load the 15 round keys **once** (8 load instructions either way); hoisting cannot save the reloads that made it worth 1.8–7.2 points in `mix4s4`. Rotating keys win by **+0.3 to +1.4 points** at 16–64 B on GV4/r8g/GV5 and by 1.6–3.3 on GV3, paired at both address ranks (−0.2…−1.0 % in mix A). Hoisting also **costs the six spare registers** the mask values want. |
| **Uniform small-traffic value (8 calls)** | `g4` **13.0 / 12.3 / 12.2 / 12.3 %** (V1/GV4/r8g/V3) against `t4`'s 20.7/20.8/20.8/21.0, `t4p8`'s 21.9/22.1/22.1/22.0, `m4s4h`'s 13.5/15.9/15.9/17.1 and **`a4`'s 20.2/20.3/20.3/20.8**. Over `nblk` 1..4 only: `g4` 27.1/25.9/25.7/25.8 % vs `t4` 43.8/43.5/43.6/43.9 and **`a4` 41.9/42.5/42.5/43.4**. |
| **Recommendation** | **Do not build `g4`; of the two one-region shapes, the cascade 4→1 is the better one.** A measured negative — but a productive one, because the premise it was built to test is **right**: over-running the *AES* is nearly free (0.3–1.9 cyc). What is not free is that one entry point also forces the *GHASH* to be uniform and branch-free, and the measurement is unambiguous that the exactly-`nblk` GHASH must be reached by a **branch**. `g4` is 768 B smaller than the cascade at ×1.20 vs ×1.35 and has 1 path instead of 4 — the only terms on which it wins — while giving up 22 points at 16 B, 17–20 at 32 B and 4–13 at 48 B for 3–10 points back at 64 B. |

---

## 1. What was built

### 1.1 The structure, exactly as asked for

Two instructions inserted after `add x10, sp, #64` — the fall-through path pays
exactly what `dsp0` pays, and **no** branch is taken for `nblk > 4`:

```
	cmp	x9, #64				//[G4] nblk <= 4 ?
	b.le	.L256_dec_g4_grp
```

and **one** region, with **one** label, appended before `.L256_dec_ret`:

```
.L256_dec_g4_grp:      Xi', counter base', per-lane clamped offsets + predicates,
                       4 ciphertext loads, 4 CTR blocks
                       56 AES units (4 blocks x 14 rounds, INTERLEAVED 4-wide)
                         with GHASH(4 lanes, H^4,H^3,H^2,H^1) folded into units
                         0..16 and MODULO + tag store + counter store into 17..55
                       4 plaintext eor3 + 4 CLAMPED stores, ascending
.L256_dec_g4_done:     mov x0,x9 / frame pop / ret
```

`nblk` ∈ {1,2,3,4} all enter at `.L256_dec_g4_grp` and all run **four** blocks of
AES; **`nblk` ∈ {5,6,7,8} and `nblk` > 8 all fall back to the existing staggered
path, permanently** — a dedicated `nblk` = 8 body is out of scope, so 128 B is
never accelerated here and the only claim made about it is that the fall-back is
free (§3.2).

> **Out of scope:** a `g4` + dedicated 8-wide body 8 variant (`g4p8`) was built and
> measured before the scope was fixed. Its data stays in `_docs/fused-g4/logs/`
> for the record and it appears in the raw tables below, but **it is excluded from
> every conclusion and recommendation in this report.** For completeness in one
> line: it restores exactly `t4p8`'s 128 B gain (−9.06/−9.85/−9.87/−8.61 % vs
> `dsp0`, within 0.7 points of `t4p8`, since it is `gen.py`'s body 8
> source-identical) at 7468 B, and changes nothing at any other length.

### 1.2 How the group avoids over-writing output for `nblk` < 4

This is the characteristic bug of the design, so the mechanism is spelled out and
then probed four different ways in §2.

Let `d = 4 − nblk`. The **real blocks live in the HIGH lanes**: lane `j` carries
message block `j − d`. Everything follows from that one choice.

* **H powers are fixed.** Lane `j` uses `H^(4−j)`, so the first real lane `j = d`
  uses `H^(4−d) = H^nblk` and the last, lane 3, uses `H^1` — exactly the powers
  an exactly-`nblk` GHASH needs, at **constant Htable offsets**, with no pointer
  arithmetic. (Verified: each of `H^4,H^3,H^2,H^1` appears exactly once.)
* **Addresses are clamped at block 0, never out of bounds.** Lane `j`'s byte
  offset is `max(0, 16*nblk − 16*(4−j))`, which is one `subs` + one `csel` per
  lane (lane 3 needs no clamp). A discarded lane therefore reads and writes
  **block 0** — inside the message — so there is **no overread of `in` and no
  overwrite of `out` beyond `16*nblk`**. `x0`/`x2` are never advanced (0
  post-indexed accesses in the region), so every load uses a register offset.
* **The stores are emitted in ASCENDING lane order.** Every discarded lane
  (`j < d`) writes garbage to `out[0..16)` **before** lane `d` writes the real
  block 0 over it. All four ciphertext loads precede all four stores, so
  in-place decryption (`out == in`) is safe as well.
* **A discarded lane contributes nothing to the tag.** Its GHASH input is ANDed
  with `Z_j = −1 iff nblk ≥ 4−j`, and `0 · H^p = 0`.
* **The partial tag `Xi'` is fed into lane `d` only**, via
  `F_j = −1 iff nblk == 4−j`. Both masks come from the **same `subs`** as the
  offset (`pl` gives `Z`, `eq` gives `F`) and are materialised with
  `dup vS.2d, xN`.
* **The counter is shifted, not corrected.** `base' = base + (nblk − 4)` (a
  `sub`/`lsl`/`movi`/`mov`/`add`), so lane `j` carries `base' + j = base + (j−d)`
  and after four `add v29,v29,v31` the register holds `base' + 4 = base + nblk` —
  precisely the counter the shared epilogue stores. All of it is mod 2^32 inside
  4s lane 3, as in the baseline, so the transiently "negative" counters of the
  discarded lanes are arithmetically irrelevant.

Net: **14 GPR ops** (3 `subs`, 3 `csel`, 6 `csetm`, 2 for `base'`) and **16 SIMD
ops** (6 `dup`, 3 `and` building the masks, 4 `eor` + 3 `and` applying them) on
top of the exact-4 body. Nothing else in the kernel changes.

### 1.3 The group is FUSED, not staggered — verified, not asserted

**What was built is the fused shape**, i.e. the GHASH folds are interleaved
*into* the AES instruction stream, exactly as every measured member of this
family is. It is not "all the AES, then the GHASH" — that is the baseline
kernel's shape and it is what this family exists to beat.

Concretely, the region is emitted by `gen_cascW.place(units, early, late, K)` —
the same K-split interleaver `fused-small-path/gen.py`'s `body()` uses and that
`gen_set.py` / `gen_casck.py` / `gen_cascW.py` inherit — with `U = 56` AES units
(4 blocks × 14 rounds, one `aese`+`aesmc` pair per unit) and
`K = round(0.30 × 56) = 17`: **the four GHASH lanes are front-loaded into AES
units 0..16, and the MODULO reduce, tag store and counter store are spread over
units 17..55.**

Measured instruction mix of the region (`.L256_dec_g4_grp` … `ret`, r8g,
`k1 = 0.30`):

| | count |
|---|---:|
| `aese` | **56** (= 4 blocks × 14 rounds) |
| `aesmc` | **52** (= 4 × 13; round 13 has no `aesmc`, as required) |
| `pmull` / `pmull2` | **10 / 4** — 12 GHASH (4 lanes × hi/lo/mid) + 2 MODULO |
| `eor` / `eor3` / `ext` | 23 / 4 / 9 |
| `rev64` / `rev32` | 6 / 6 |
| `dup` / `and` / `csetm` / `csel` / `subs` | 6 / 6 / 6 / 3 / 3 (the predication) |
| `ldr` / `ldp` / `ld1` | 14 / 7 / 2 |
| `str` / `st1` | 5 / 1 |

and the **position of every non-AES operation, expressed as the index of the AES
unit it is interleaved after** (−1 = the prep, before AES round 0):

```
  GHASH lane loads/rev64   units   0,  4,  8, 13      (one per lane)
  GHASH pmull/pmull2       units   2,2,3   6,6,6   10,10,11   14,15,15
  GHASH accumulate eors    units   1..17 (23 eor total, spread to unit 41)
  MODULO constant ldr d16  unit   17
  MODULO pmull             units  19, 34
  MODULO ext               units  24, 36, 43
  tag store   st1 [x3]     unit   48
  counter store str [x16]  unit   53
  plaintext eor3 + 4 str   unit   55  (after the last aese)
```

So all twelve GHASH multiplies sit **inside the first 15 of 56 AES units**, the
MODULO reduce straddles units 17–43 in the middle of the AES stream, and only the
final plaintext `eor3`s and stores follow the last `aese` — which is forced, since
they consume the AES results. `verify_g4.py` asserts the `aese` count (56), the
`aese`/`aesmc` adjacency (0 violations, whole file), and that `Xi'` in `v16` is
dead before unit 17's `ldr d16` overwrites it with the MODULO constant.

For comparison, the same accounting for `a4`'s bodies (`gen.py body(n, 4, k)`) is
`gen.py`'s own K-split at the published per-`n` `k` values, unchanged.

### 1.4 The generator is a composition, and it self-checks

`_docs/fused-g4/gen_g4.py` **imports** and reuses:

* `fused-cascade/gen_cascW.py` — `HL`/`KD`, `RKREG`/`KEYLOAD`, `common()`,
  `aes_units()` (the 4-wide interleave), `ghash_blk()`'s body, `late_ops()`
  (MODULO + tag + counter store), `place()` (the AES/GHASH interleaver) and
  `epilogue()`;
* `fused-small-path/gen.py` — `body()` for the `a4` control and for `g4p8`'s
  body 8 (`n_aes != n_gh` is `gen.py`'s own `fuse8` idea, here at `n_aes = 4`);
* `fused-truncation/gen_trunc.py` — `tree()` for `a4`'s dispatch;
* `fused-t4p8/gen_set.py` — the design-A "small test first" dispatch.

Three self-checks, run on **all four hosts**:

```
  SELF-CHECK 1  gen_g4.apply_a4 with n_aes=1  ==  gen_trunc.py t4:
     x4=c3f72ffe4679c67064f5439a1d97c712 t4=c3f72ffe4679c67064f5439a1d97c712  SAME
  SELF-CHECK 2  base.o 114cedb51f36c584e50843d2838d871e   (published)
                t4.o   c3f72ffe4679c67064f5439a1d97c712   (published)
                cw4.o  51bbb39cc2c0d89fd3c94804c1ec62bc   (published)
  SELF-CHECK 3  g4p8's body 8 == t4p8's body 8: IDENTICAL (382 lines)
```

i.e. `a4` is `t4` **with one parameter changed**, and `g4p8`'s 128 B path is
`t4p8`'s 128 B path character for character. `t4p8`'s `.text` reproduces the
published 8832 B and `m4s4h`'s the published 6716 B.

### 1.5 The variants, and why each exists

| variant | what | `.text` | × | paths |
|---|---|---:|---:|---:|
| `g4` | **the structure under test**: one region, 4-wide AES always, masked 4-lane GHASH, keys rotating through `v26/v27/v28`, mask values **precomputed** in the six spare registers | 5948 | 1.197 | **1** |
| `g4i` | the same with the masks materialised **inline** (`dup` inside each lane) — matched to what the hoisted map is forced to do | 5948 | 1.197 | 1 |
| `g4h` | the same region with all 15 round keys **hoisted** into `v1..v15`; states move to `v0/v26/v27/v28`, ciphertext becomes transient, **zero** spare registers | 5964 | 1.201 | 1 |
| `g4p8` | `g4` + `gen.py`'s dedicated 8-wide body 8 | 7468 | 1.503 | 2 |
| **`a4`** | **the control that isolates the discarded AES**: four *separate* `gen.py` bodies for `nblk` = 1..4, each doing **4 blocks of AES** and **exactly `nblk`** of GHASH. No predication of any kind. | 8020 | 1.614 | 4 |
| `g4nm` | diagnostic, **correct at `nblk` = 4 only**: `g4` with the masks removed | 5888 | 1.185 | — |
| `g4nn` | diagnostic, **correct at `nblk` = 4 only**: `g4nm` with the clamped offsets and `base'` removed too | 5812 | 1.170 | — |
| `t4`, `t4p8`, `m4s4h`, `cw4`, `dsp0` | the published comparators and the pure-dispatch control | 7312 / 8832 / 6716 / 9336 / 4976 | | |

### 1.6 Slots and the floor

`verify_g4.py`, convention of `fused-cascade-experiment.md` (adjacent
`aese`+`aesmc` = 1 slot, `.inst`-encoded `eor3` counted, loads/stores excluded):

| variant | slots at `nblk` = 1 / 2 / 3 / 4 | `aese` |
|---|---|---|
| `t4` | 44 / 71 / 95 / **122** | 14 / 28 / 42 / 56 |
| `a4` | 94 / 104 / 111 / **122** | **56 at every `nblk`** |
| `g4nn` | 121 (nblk-independent) | 56 |
| `g4nm` | 124 (nblk-independent) | 56 |
| **`g4` / `g4i` / `g4h`** | **139 (nblk-independent)** | **56** |

`a4`'s `nblk` = 4 body is 122 slots — **the same object code as `t4`'s body 4** —
so `a4` and `t4` differ only in bodies 1, 2, 3, and `g4` is `a4`'s body 4 plus
17 slots of predication. `g4`'s own issue floor is a flat **34.75 cycles**.

---

## 2. Correctness

| check | result |
|---|---|
| **Build fidelity** | Every object md5-identical on all 4 hosts. On r8g the object built by the **real `arm/Makefile` `%.o : %.S` rule** (in a scratch copy of `arm/` + `include/`; no tracked file touched, `make clean` never run in `arm/aes-gcm/kat`) is **byte-identical** to the harness object for `base dsp0 g4 g4i g4h g4p8 a4 t4 t4p8 m4s4h` — `make-built .o vs mk.sh .o: SAME` ×10. The tracked tree is still at `c2609cf8` with `arm/` and `include/` clean. |
| **KAT, make-driven** | `make aes-gcm/aesv8_gcm_8x_dec_256_wb.o` then `make -C aes-gcm/kat run`, `kat_wb_dec` **deleted first** so no stale link can be tested: `35 passed, 0 failed … KAT GATE: PASS` for all 10 variants. |
| **KAT, harness relink** | `kat.sh` (`gcc -O2 -o kat/kat_wb_dec kat_wb_dec.c obj/<v>.o obj/ref.o`, binary deleted first): **35/35 PASS for all 11 variants on all four hosts** (44 runs). The KAT sweep covers `nblk` = 1..8 individually, so the fused lengths are exercised directly. |
| **In-process byte-compare** | 12 slots in one binary (`base baseAA dsp0 dsp0AA g4 g4AA g4h a4 g4p8 t4p8 t4 m4s4h`), `out`/`Xi`/`ivec`/**return value** compared over **every whole-block length 1..256 blocks**: `SELFCHECK OK (256 whole-block lengths 1..256 blk x 12 variants; out/Xi/ivec/ret byte-identical, nothing written past 16*nblk)` on all four hosts, **re-run at the start of every one of the 15 per-length and 9 mixed-length timing processes per host** and of every probe. Non-degeneracy (`out != in`) asserted at every length. |
| **The discarded blocks are not observable** | `bench12g.c` (derived from `bench12.c` by `mkbench12g.py`) pre-fills every output buffer with `0xA5` for **64 bytes past the message** and asserts those bytes are untouched afterwards, for **every** variant at **every** one of the 256 lengths. Never triggered. The counter and tag are covered by the `ivec`/`Xi` byte-compare against the reference, which is exact at every length — so the counter advances by exactly `nblk`, not 4. |
| **Lane-mapping probes** | `zlaneJ` zeroes lane `J`'s GHASH products. Lane `J` is real iff `nblk ≥ 4−J`, so the failing set is fixed by the high-lane layout and any error in it moves the boundary. Measured, **both key modes, all four hosts**: `zlane0 {4}` · `zlane1 {3,4}` · `zlane2 {2,3,4}` · `zlane3 {1,2,3,4}` — every one exactly as predicted. This is the direct test that the real blocks sit in the high lanes and that the discarded lanes are genuinely masked out. |
| **Mis-entry probe** | `zapall` (all four lanes zapped): fails at **exactly `nblk` = {1,2,3,4}**, never at 5, 6, 7, 8, never at ≥ 9 — both key modes, all four hosts. |
| **`brk #0` liveness probe** | A `brk #0` at the region's single entry label: the process must die iff the group is entered. Measured at `nblk` = 1..9, 16, 64 on all four hosts: **`TRAPPED` at exactly 1, 2, 3, 4** and **`SURVIVED` at 5, 6, 7, 8, 9, 16, 64** — 11/11 as expected, so the group is entered for every `nblk` ≤ 4 and for no other length. |
| **Guard-page memory safety** | `brkprobe.c` places `in` and `out` flush against a `PROT_NONE` page, **above** (`guard`) and **below** (`guardlo`) the buffer, so any access outside `[buf, buf+16*nblk)` is a hard SIGSEGV. `g4 g4h g4p8 a4 t4 base` × both directions × `nblk` = 1..8 = **96 runs per host, all survived**. This is the hard proof that the clamped lane addresses never leave the message. |
| **Total probes** | **33 per host (132 across the four)**, all exact, with no collateral failure at any other length. |
| **Adjacency** | `0 aese/aesmc violations` in `g4 g4i g4h g4p8 a4 t4 t4p8 m4s4h cw4`, whole-file scan. |
| **No *unintended* dead AES** | `aese` is exactly **56** in the region at every `nblk` — 14×4, the four blocks the design runs on purpose — and exactly 56 in each of `a4`'s four bodies. `t4`'s bodies are 14`n`. |
| **Frame** | **80 B**: one `stp d8,d9,[sp,#-80]!`, `1 + 1` matching `ldp d8,d9,[sp],#80` (`g4p8`: 1 + 2), and **0** `add/sub sp` anywhere in source or `objdump`. No new callee-saved register is written; only `x1,x4,x5,x7,x8,x12,x13,x14,x15,x17` are used, all dead at the insertion point. |
| **`nblk > 8` content** | Normalised `objdump` (`objcmp.py`, addresses and branch targets masked): `g4` = *2 instructions inserted at baseline instruction 14, then the whole baseline stream identical, `.L256_dec_ret` stub found verbatim (relocated), 243 appended* → **VERDICT: nblk>8 content UNCHANGED**. Same verdict for `g4h` (+247), `g4p8` (+621), `a4`, `t4`, `t4p8`, `m4s4h`, `dsp0`. |

---

## 3. Fixed-length measurement

Discipline as established: every variant `objcopy --redefine-sym`'d to a distinct
symbol and linked into **one** 12-slot binary, round-robin with the slot order
rotated every rep, `taskset -c 3`, 200-call warm-up per pass, **best of 300 reps
× 5 processes × 3 link orderings = 15 processes per host**. `base` is pinned to
link slot 0 as in the published runs so the tables are comparable. `baseAA`,
`dsp0AA` and `g4AA` are the same objects again, so `base`, the dispatch control
and the variant under test each have their own placement floor.

**Sanity anchors** against the published runs (r8g/GV4): `t4p8`
−47.09/−42.89/−43.48/−40.90 at 16/32/48/64 B and **−9.99 at 128 B vs `dsp0`**
against the published −47.21/−42.80/−43.48/−40.88 and −10.47; `m4s4h`
−46.03/−43.33/−37.19/−25.90 and +18.00 at 128 B against the published
−46.13/−43.43/−37.34/−25.92/+18.01; `t4` −47.21/−42.92/−43.57/−40.87 against
−47.15/−43.01/−43.56/−40.85. **The harness reproduces both published runs to
≤ 0.6 points**, and `cw4.o`/`t4.o` are md5-identical to the published objects.

### 3.1 Δ % vs HEAD, all 12 lengths, all four hosts (absolute-min estimator)

**GV3 — Neoverse-V1, 2.5909 GHz**

| variant | `.text` | × | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| HEAD | 4968 | 1.00 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `dsp0` ctl | 4976 | 1.00 | +0.44 | −0.41 | +0.86 | −0.36 | +0.31 | −0.40 | −0.34 | −1.20 | −0.43 | −1.00 | −0.40 | −0.25 |
| **`g4`** | 5948 | 1.20 | **−24.86** | **−25.80** | **−27.74** | **−29.79** | −1.70 | −0.18 | −0.02 | +0.02 | −0.10 | −0.79 | −0.37 | −0.25 |
| `g4h` | 5964 | 1.20 | −22.39 | −24.22 | −24.40 | −28.11 | +0.29 | −0.38 | −0.06 | −1.09 | +0.45 | −1.07 | −0.39 | −0.24 |
| **`a4`** | 8020 | 1.61 | **−44.05** | **−41.59** | **−40.94** | **−41.19** | −2.98 | −0.38 | +0.29 | −0.47 | +0.33 | −0.61 | −0.39 | −0.26 |
| `g4p8` | 7468 | 1.50 | −21.80 | −21.94 | −25.46 | −29.29 | +0.05 | +0.12 | −0.73 | **−10.15** | −0.94 | −0.34 | −0.01 | +0.08 |
| `t4p8` | 8832 | 1.78 | −46.83 | −44.00 | −43.55 | −41.37 | −0.05 | +0.13 | +0.41 | **−10.02** | −0.98 | −0.66 | +0.06 | +0.13 |
| `t4` | 7312 | 1.47 | −46.70 | −43.94 | −43.47 | −41.34 | +0.28 | −0.33 | +0.32 | −1.24 | +0.31 | −1.07 | −0.45 | −0.27 |
| `m4s4h` | 6716 | 1.35 | −46.95 | −42.26 | −31.24 | −20.03 | +0.02 | +0.13 | +0.38 | +21.13 | −0.59 | +0.17 | −0.42 | −0.05 |

A/A floors (worst |Δ| of any of the 15 processes): `base` 0.30/0.34/**2.28**/0.15/
0.16/0.42/0.51/0.59/0.89/0.69/0.54/0.35; **`g4` 5.81/5.76/4.84/2.53/2.31**/0.26/
0.56/1.69/1.03/1.04/0.58/0.27; `dsp0` 1.06/0.24/0.22/0.34/0.36/0.30/0.75/1.56/
0.88/1.14/0.39/0.31. **GV3's 16–80 B floors are wide this run** (`g4AA` 2.3–5.8 %),
so the V1 small-length column is quoted but the V1 *conclusions* rest on the
paired controls of §5.2 and on the decomposition of §4, whose V1 numbers are
tight.

**GV4 — Neoverse-V2, 2.7917 GHz**

| variant | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `dsp0` ctl | +0.17 | +0.04 | −0.21 | −0.08 | +0.03 | +0.17 | +0.12 | −0.52 | −0.28 | +0.03 | −0.11 | −0.04 |
| **`g4`** | **−23.37** | **−23.69** | **−26.52** | **−29.71** | +0.03 | +0.23 | −0.15 | +0.14 | −0.26 | −0.04 | −0.29 | +0.05 |
| `g4h` | −22.99 | −23.31 | −26.14 | −28.74 | +0.03 | +0.12 | −0.23 | +0.19 | −0.13 | +0.30 | +0.02 | −0.09 |
| **`a4`** | **−45.16** | **−42.04** | **−42.26** | **−40.85** | +0.01 | +0.22 | −0.20 | −0.58 | −0.11 | +0.20 | −0.16 | +0.04 |
| `g4p8` | −23.46 | −23.76 | −26.58 | −29.15 | +0.07 | +0.15 | +0.17 | **−10.31** | −0.26 | −0.02 | −0.05 | −0.06 |
| `t4p8` | −47.37 | −42.87 | −43.49 | −40.93 | +0.07 | −0.28 | −0.05 | **−10.22** | −0.18 | +0.15 | −0.15 | −0.10 |
| `t4` | −47.01 | −42.91 | −43.57 | −40.90 | +0.03 | +0.06 | −0.20 | −0.57 | −0.18 | +0.09 | −0.36 | +0.03 |
| `m4s4h` | −45.94 | −43.31 | −37.33 | −25.94 | +0.05 | −0.23 | −0.16 | +17.37 | −0.27 | +0.03 | −0.02 | −0.20 |

A/A floors: `base` **5.30**/0.26/0.09/0.15/0.09/0.39/0.35/0.60/0.34/0.34/0.35/
0.11; `g4` 0.14/0.17/0.18/0.98/0.05/0.15/0.46/0.87/0.50/1.31/0.34/0.09; `dsp0`
**4.30**/0.16/0.13/0.18/0.07/0.14/0.14/0.90/0.29/1.32/1.25/0.07. (The documented
16 B placement lottery again: `base` landed slow, so 16 B Δ % on the V2 hosts
carries a ±4–9 % floor. `g4` itself is stable at 16 B to ±0.15 %.)

**`ec2r8g` — Neoverse-V2, 2.7926 GHz** (inter-instance reproduction of GV4)

| variant | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `dsp0` ctl | +0.13 | −0.02 | −0.22 | −0.06 | +0.01 | +0.00 | +0.12 | −0.54 | −0.23 | −0.29 | +0.30 | +0.07 |
| **`g4`** | **−23.41** | **−23.71** | **−26.51** | **−29.04** | +0.00 | +0.10 | −0.16 | +0.13 | −0.30 | −0.23 | +0.28 | +0.07 |
| `g4h` | −23.01 | −23.33 | −26.14 | −28.70 | +0.00 | −0.02 | −0.20 | +0.25 | −0.15 | +0.04 | −0.22 | −0.02 |
| **`a4`** | **−45.17** | **−42.07** | **−42.24** | **−40.80** | +0.02 | −0.08 | −0.21 | −0.53 | −0.14 | −0.10 | +0.35 | −0.01 |
| `g4p8` | −23.46 | −23.77 | −26.57 | −29.10 | +0.05 | +0.01 | +0.19 | **−10.36** | −0.30 | −0.22 | +0.34 | +0.03 |
| `t4p8` | −47.09 | −42.89 | −43.48 | −40.90 | +0.02 | −0.39 | −0.06 | **−10.48** | −0.24 | −0.44 | +0.30 | −0.15 |
| `t4` | −47.21 | −42.92 | −43.57 | −40.87 | +0.01 | +0.03 | −0.15 | −0.55 | −0.19 | +0.15 | +0.34 | +0.01 |
| `m4s4h` | −45.96 | −43.34 | −37.33 | −25.94 | +0.04 | −0.41 | −0.16 | +17.35 | −0.31 | −0.13 | −0.20 | −0.29 |

**GV5 — Neoverse-V3, 3.2905 GHz** (the quiet host: A/A ≤ 0.50 % everywhere,
≤ 0.08 % at 16–64 B — the cleanest confirmation available)

| variant | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `dsp0` ctl | +0.04 | +0.04 | +0.04 | +0.02 | −0.01 | −0.14 | −0.33 | +0.03 | +0.01 | +0.22 | +0.00 | +0.00 |
| **`g4`** | **−23.83** | **−23.91** | **−26.59** | **−28.69** | +0.03 | +0.12 | +0.11 | +0.01 | +0.01 | +0.23 | +0.01 | +0.01 |
| `g4h` | −22.43 | −22.55 | −25.24 | −27.37 | −0.04 | −0.26 | −0.35 | +0.02 | −0.20 | +0.22 | +0.00 | +0.00 |
| **`a4`** | **−45.84** | **−42.30** | **−43.49** | **−42.01** | −0.05 | −0.25 | −0.35 | +0.00 | +0.01 | +0.23 | −0.00 | +0.00 |
| `g4p8` | −23.87 | −23.98 | −26.64 | −28.73 | +0.03 | −0.04 | −0.01 | **−8.58** | +0.02 | +0.11 | +0.01 | +0.00 |
| `t4p8` | −46.33 | −42.42 | −44.90 | −42.00 | +0.01 | −0.04 | −0.01 | **−8.58** | +0.02 | −0.20 | +0.01 | +0.00 |
| `t4` | −46.31 | −42.42 | −44.83 | −42.00 | −0.04 | −0.26 | −0.33 | +0.02 | −0.01 | +0.23 | +0.00 | +0.01 |
| `m4s4h` | −46.02 | −42.56 | −39.71 | −29.54 | +0.02 | −0.05 | +0.03 | +13.26 | +0.04 | −0.16 | +0.01 | +0.01 |

### 3.2 The 128 B column against the `dsp0` control

`base` sits in link slot 0 and carries the documented placement bias, so 128 B is
referenced to the never-taken-dispatch control. Min estimator:

| | V1 GV3 | V2 GV4 | V2 r8g | V3 GV5 |
|---|---:|---:|---:|---:|
| `dsp0AA` vs `dsp0` (the control's own floor) | −0.01 | +0.68 | +0.74 | −0.01 |
| `baseAA` vs `dsp0` | +1.33 | −0.05 | −0.05 | −0.05 |
| **`g4` vs `dsp0`** | **+1.23** | **+0.66** | **+0.68** | **−0.02** |
| `g4h` vs `dsp0` | +0.11 | +0.71 | +0.80 | −0.01 |
| `a4` vs `dsp0` | +0.74 | −0.06 | +0.01 | −0.03 |
| **`g4p8` vs `dsp0`** | **−9.06** | **−9.85** | **−9.87** | **−8.61** |
| `t4p8` vs `dsp0` | −8.93 | −9.76 | −9.99 | −8.61 |
| `m4s4h` vs `dsp0` | +22.60 | +17.98 | +18.00 | +13.23 |

**`g4`'s 128 B is a wash on all four hosts** — inside the control's own floor on
the V2 hosts and on V3, and on V1 inside `g4`'s own 1.69 % placement floor at that
length (`baseAA` itself reads +1.33 against `dsp0` there) — which is what "falls
back" must mean, and **`g4p8` recovers `t4p8`'s full 128 B
gain to within 0.7 / 0.1 / 0.1 / 0.0 points** — as it must, since it runs the
same body 8. Contrast `m4s4h`, whose shared region turns 128 B into a
+13…+23 % regression.

### 3.3 THE DECIDING COMPARISON — `g4` versus the cascade 4→1

The design decision is between exactly two shapes, both **one region**, both
**fused**, both with **no per-size bodies**:

1. **`g4`** — one 4-wide interleaved group, one entry, serving every `nblk` ≤ 4,
   discarding 3/2/1 blocks at 16/32/48 B;
2. **cascade 4→1** — four single-block sections with entries for 4/3/2/1,
   exact-`n`, no dead AES. This is `mix4s4`'s `nblk` ≤ 4 behaviour: its 4-wide
   group is only entered at `nblk` = 8, so at these lengths it is unexecuted and
   `m4s4h` *is* the cascade 4→1.

Both were linked into the **same 12-slot binary and timed in the same processes**
here, so this is a paired comparison, not a cross-run one. The cascade rows
reproduce the published `mix4s4` numbers to **≤ 0.4 points at every length on
every core** (published V1/V2/V3: −47.1/−46.3/−46.0, −42.2/−43.4/−42.6,
−31.3/−37.3/−39.7, −20.0/−25.9/−29.5).

**Δ % vs HEAD, absolute-min estimator, and the head-to-head in percentage points**
(+ve = `g4` slower):

| length | core | **`g4`** | **cascade 4→1 (`m4s4h`)** | **g4 − cascade** |
|---:|---|---:|---:|---:|
| **16 B** | V1 GV3 | −24.86 | −46.95 | **+22.08** |
| | V2 GV4 | −23.37 | −45.94 | **+22.57** |
| | V2 r8g | −23.41 | −45.96 | **+22.54** |
| | V3 GV5 | −23.83 | −46.02 | **+22.18** |
| **32 B** | V1 GV3 | −25.80 | −42.26 | **+16.46** |
| | V2 GV4 | −23.69 | −43.31 | **+19.62** |
| | V2 r8g | −23.71 | −43.34 | **+19.62** |
| | V3 GV5 | −23.91 | −42.56 | **+18.65** |
| **48 B** | V1 GV3 | −27.74 | −31.24 | **+3.51** |
| | V2 GV4 | −26.52 | −37.33 | **+10.81** |
| | V2 r8g | −26.51 | −37.33 | **+10.82** |
| | V3 GV5 | −26.59 | −39.71 | **+13.11** |
| **64 B** | V1 GV3 | **−29.79** | −20.03 | **−9.77** |
| | V2 GV4 | **−29.71** | −25.94 | **−3.78** |
| | V2 r8g | **−29.04** | −25.94 | **−3.09** |
| | V3 GV5 | −28.69 | −29.54 | +0.85 |
| **80–4096 B** | all | wash (§3.1) | wash | ≤ 1.7 points, both inside floor |

**The prediction was: tie at 16/32 B, `g4` wins materially at 48 and 64 B.
Measured: `g4` loses heavily at 16 and 32 B, loses at 48 B, and wins only at
64 B — by 9.8 points on V1, 3.1–3.8 on V2, and not at all on V3.**

The *mechanism* in the prediction is nevertheless correct, and the numbers show
exactly where it stops working. Achieved cycles, and the marginal cost per block
across `nblk` = 1 → 4:

| | V1 GV3 | V2 GV4 | V2 r8g | V3 GV5 |
|---|---|---|---|---|
| cascade 4→1, `nblk` 1/2/3/4 | 35.9 / 39.6 / 48.9 / 59.9 | 35.1 / 36.9 / 42.4 / 51.9 | 35.1 / 37.0 / 42.4 / 51.9 | 34.8 / 37.1 / 40.4 / 48.6 |
| **`g4`, `nblk` 1/2/3/4** | **50.9 / 50.9 / 51.4 / 52.6** | **49.7 / 49.7 / 49.7 / 49.3** | **49.7 / 49.7 / 49.7 / 49.7** | **49.2 / 49.2 / 49.2 / 49.2** |
| cascade marginal cyc/block | **8.00** | **5.60** | 5.60 | **4.60** |
| `g4` marginal cyc/block | **+0.57** | **−0.13** | 0.00 | **0.00** |
| `g4` − cascade, cycles | +15.0 / +11.3 / +2.5 / **−7.3** | +14.6 / +12.8 / +7.3 / **−2.6** | +14.6 / +12.7 / +7.3 / **−2.2** | +14.4 / +12.1 / +8.8 / +0.6 |

* **The slope argument is confirmed.** `g4`'s marginal cost per extra block is
  **0.0 ± 0.6 cycles** — it has already paid for four blocks — against the
  cascade's **8.00 / 5.60 / 4.60** cyc/block, which brackets the published
  sequential-block figures (10.80 / 9.32 / 8.52 hoisted `W = 1`) once the
  latency-shadow absorption of the first sections is taken out. Over `nblk`
  1→4 the cascade adds **24.0 / 16.8 / 13.8 cycles** and `g4` adds **1.7 / −0.4 /
  0.0**. Four-wide really is the cheaper way to add a block.
* **But `g4` starts ~14.5 cycles behind, and the slope only repays that by
  `nblk` = 4 on the two older cores.** The 14.5-cycle constant is the §4
  decomposition: ~6.5 of uniform 4-lane GHASH, ~6.6 of branch-free masking,
  ~1.1 of clamped addressing, ~0.3–1.9 of discarded AES. The cross-over is
  between 48 and 64 B on V1, at ~64 B on V2, and **beyond 64 B on V3** — and
  since `nblk` ≥ 5 falls back, on V3 the cross-over never happens inside the
  fused range at all.
* **Even a predication-free version of the same shape only wins from `nblk` = 3.**
  The diagnostic `g4nn` (correct at `nblk` = 4; uniform 4-lane GHASH, no masks, no
  clamped addressing) costs a flat **42.0 cycles** on V2 against the cascade's
  35.1 / 36.9 / 42.4 / 51.9 — so it would still lose by 6.9 and 5.1 cycles at
  `nblk` = 1 and 2, tie at 3, and win by 9.9 at 4. **The 1- and 2-block losses are
  not a masking artefact; they are the four lanes of GHASH.** No amount of
  cleverness in the predication recovers 16 B and 32 B for a uniform region.
* Uniform-`nblk` value over just the four fused lengths: **`g4` 27.1 / 25.9 /
  25.7 / 25.8 %** against **the cascade's 34.7 / 37.9 / 37.9 / 39.3 %** and `t4`'s
  43.8 / 43.5 / 43.6 / 43.9 %.

### 3.4 Value at fixed lengths

Uniform `nblk` weighting over the eight small lengths (the convention of §3.4 of
the truncation doc; the r8g `base` total 201.78 ns reproduces the published
201.71, and `t4p8` reproduces 22.1 %):

| host | `base`, 8 calls | **`g4`** | `g4h` | `g4p8` | **`a4`** | `t4` | `t4p8` | `m4s4h` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| GV3 V1 | 231.43 ns | **13.0 %** | 11.9 % | 13.0 % | **20.2 %** | 20.7 % | 21.9 % | 13.5 % |
| GV4 V2 | 201.74 ns | **12.3 %** | 12.1 % | 13.5 % | **20.3 %** | 20.8 % | 22.1 % | 15.9 % |
| r8g V2 | 201.78 ns | **12.2 %** | 12.1 % | 13.5 % | **20.3 %** | 20.8 % | 22.1 % | 15.9 % |
| GV5 V3 | 168.79 ns | **12.3 %** | 11.8 % | 13.4 % | **20.8 %** | 21.0 % | 22.0 % | 17.1 % |

Restricted to the four lengths `g4` actually fuses (16–64 B, uniform):

| host | **`g4`** | `g4h` | **`a4`** | `t4` | `t4p8` | `m4s4h` |
|---|---:|---:|---:|---:|---:|---:|
| GV3 V1 | **27.1 %** | 24.9 % | **41.9 %** | 43.8 % | 43.9 % | 34.7 % |
| GV4 V2 | **25.9 %** | 25.4 % | **42.5 %** | 43.5 % | 43.6 % | 37.9 % |
| r8g V2 | **25.7 %** | 25.4 % | **42.5 %** | 43.6 % | 43.5 % | 37.9 % |
| GV5 V3 | **25.8 %** | 24.5 % | **43.4 %** | 43.9 % | 43.9 % | 39.3 % |

**`a4` is within 0.5–1.9 points of `t4`** across all four hosts — the whole
"discard three blocks of AES" idea, costed — while **`g4` gives up 16–18 points**.

---

## 4. THE PRIMARY RESULT — the isolated cost of the discarded blocks

This is the question the experiment was built to answer, and it is answered twice:
once by a control that changes **one generator parameter**, and once by a
four-step decomposition in which every step is a single, named change.

### 4.1 The discarded AES, isolated (`a4` vs `t4`)

`a4` and `t4` are the same four `gen.py` bodies with the same GHASH, the same
interleave schedule and the same `k` split points; the only difference is
`n_aes = 4` instead of `n_aes = n`. So `a4 − t4` **is** the cost of running 4
blocks of AES when `nblk` are needed, with no other change of any kind.

ns/call, min estimator, and the same difference in cycles:

| `nblk` | | `t4` | `a4` | **a4 − t4** |
|---:|---|---:|---:|---:|
| 1 (16 B) | V1 GV3 | 13.926 | 14.617 | **+4.96 % = +1.9 cyc** |
| | V2 GV4 | 12.322 | 12.753 | **+3.50 % = +1.2 cyc** |
| | V2 r8g | 12.277 | 12.751 | **+3.86 % = +1.3 cyc** |
| | V3 GV5 | 10.531 | 10.623 | **+0.87 % = +0.3 cyc** |
| 2 (32 B) | V1 | 14.834 | 15.456 | **+4.19 % = +1.6 cyc** |
| | V2 GV4 | 13.326 | 13.529 | **+1.52 % = +0.5 cyc** |
| | V2 r8g | 13.332 | 13.530 | **+1.49 % = +0.5 cyc** |
| | V3 | 11.308 | 11.331 | **+0.20 % = +0.1 cyc** |
| 3 (48 B) | V1 | 15.510 | 16.203 | **+4.47 % = +1.9 cyc** |
| | V2 GV4 | 13.679 | 13.995 | **+2.31 % = +0.9 cyc** |
| | V2 r8g | 13.680 | 14.001 | **+2.35 % = +0.9 cyc** |
| | V3 | 11.229 | 11.500 | **+2.41 % = +0.8 cyc** |
| 4 (64 B) | V1 | 16.958 | 17.004 | +0.27 % (same code) |
| | V2 GV4 | 14.845 | 14.858 | +0.09 % (same code) |
| | V3 | 12.150 | 12.148 | −0.02 % (same code) |

**The standing inference is confirmed.** Three blocks of AES that are computed
and thrown away cost **1.9 cycles on V1, 1.2–1.3 on V2 and 0.3 on V3** — against
a 14-round chain of ~28 cycles and an issue cost of 3 × 14 = 42 slots
(≈ 10.5 cycles at 4 slots/cycle). At `nblk` = 1 the exact-1 body runs at
**3.13–3.28× its own slot floor** (12.5 cycles of work in 34–36 cycles), so there
is ~22 cycles of latency shadow, and the surplus AES hides in it almost entirely:
**a4's achieved/exact-work ratio at `nblk` = 1 is 1.51–1.62×, i.e. it converts
the shadow into work at essentially no cost in time.** The `nblk` = 4 rows are
the zero-check: identical object code, ≤ 0.27 % apart.

The effect is **strongest on the newest core** (V3: +0.9 %, +0.2 %, +2.4 %),
which is the direction the mechanism predicts — a wider, deeper machine has more
slack to absorb the surplus.

### 4.2 …but `g4` is 15 cycles slower than `t4`, and the discarded blocks are 8 % of it

`g4` at `nblk` = 1..4 is a flat 17.81–17.82 ns (V2), 19.63–20.30 (V1),
14.94 (V3) — nblk-independent, as one region must be:

| `nblk` | | `t4` | **`g4`** | g4 − t4 |
|---:|---|---:|---:|---:|
| 1 | V1 / V2 GV4 / V2 r8g / V3 | 13.93 / 12.32 / 12.28 / 10.53 | **19.63 / 17.82 / 17.81 / 14.94** | **+41.0 / +44.6 / +45.1 / +41.9 %** |
| 2 | | 14.83 / 13.33 / 13.33 / 11.31 | **19.63 / 17.81 / 17.82 / 14.94** | **+32.3 / +33.7 / +33.6 / +32.2 %** |
| 3 | | 15.51 / 13.68 / 13.68 / 11.23 | **19.83 / 17.81 / 17.82 / 14.94** | **+27.8 / +30.2 / +30.2 / +33.1 %** |
| 4 | | 16.96 / 14.85 / 14.85 / 12.15 | **20.30 / 17.66 / 17.82 / 14.94** | **+19.7 / +18.9 / +20.0 / +23.0 %** |

Note the `nblk` = 4 row: **+19–23 % with no discarded work at all.** So the loss
is not the discarding. `measure_aux_g4.sh` decomposes it in four named steps —
`t4` → `a4` (discarded AES) → `g4nn` (uniform 4-lane GHASH) → `g4nm` (clamped
register-offset addressing + `base'`) → `g4` (branch-free masks) — where `g4nn`
and `g4nm` are correct at `nblk` = 4 only and, by construction, have
nblk-independent cost (the tables show this directly, ≤ 0.2 cycles of spread).

**Cycles at `nblk` = 1:**

| step | change | V1 GV3 | V2 GV4 | V2 r8g | V3 GV5 |
|---|---|---:|---:|---:|---:|
| `t4` | exact-`n` AES + exact-`n` GHASH | 36.1 | 34.4 | 34.4 | 34.7 |
| `a4` | **+ 3 discarded blocks of AES** | 38.0 (**+1.9**) | 35.6 (**+1.2**) | 35.6 (**+1.2**) | 35.0 (**+0.3**) |
| `g4nn` | + GHASH always 4 lanes | 45.8 (**+7.8**) | 42.0 (**+6.4**) | 42.0 (**+6.4**) | 41.5 (**+6.5**) |
| `g4nm` | + clamped offsets, `base'` | 47.6 (**+1.8**) | 43.1 (**+1.1**) | 43.2 (**+1.1**) | 42.4 (**+0.9**) |
| **`g4`** | **+ branch-free masks** | **53.1 (+5.4)** | **49.7 (+6.6)** | **49.7 (+6.6)** | **49.2 (+6.8)** |
| | **total g4 − t4** | **+16.9** | **+15.3** | **+15.3** | **+14.5** |

**Reading, and it is the same on all four cores.** Of `g4`'s ~15-cycle deficit at
one block:

* **the discarded AES is 1.9 / 1.2 / 0.3 cycles — 8 % of the loss on V2, 2 % on V3;**
* **the GHASH that must run four lanes whatever `nblk` is costs 6.4–7.8 cycles** —
  and unlike the AES this cannot hide, because 9 extra `pmull` plus their folds
  (~27 slots) land on the tag's serial accumulate chain;
* **the branch-free masking costs another 5.4–6.8 cycles for 16 slots** (1.7× its
  issue cost), because two mask ops sit in front of every lane's `pmull`;
* the clamped addressing (four register-offset `ldr`/`str` instead of two `ldp`/
  `stp`, plus `base'`) is a real but minor 0.9–1.8 cycles.

At `nblk` = 4 the first two steps vanish (0.0 and +0.5…+1.7) and the last two
remain (+7.7 / +7.7 / +7.7 on V2, +8.8 on V1, +7.7 on V3) — which is exactly the
+19–23 % seen with no discarded work.

### 4.3 Per-`nblk` achieved cycles vs the floor

Achieved cycles = min ns/call × the clock measured on that host. Two floors are
useful: the **exact-work floor** (4 slots/cycle for `n` blocks of real work, the
convention of `fused-cascade-experiment.md`) and, for `g4`, **its own** flat
139-slot floor of 34.75 cycles.

| `nblk` | exact-work floor | | `base` | **`g4`** | `g4h` | **`a4`** | `g4p8` | `t4` | `t4p8` | `m4s4h` |
|---:|---:|---|---|---|---|---|---|---|---|---|
| 1 | 12.50 | V1 | 67.7 / 5.42× | **50.9 / 4.07×** | 52.5 / 4.20× | **37.9 / 3.03×** | 52.9 / 4.23× | 36.1 / 2.89× | 36.0 / 2.88× | 35.9 / 2.87× |
| | | V2 | 64.9 / 5.19× | **49.7 / 3.98×** | 50.0 / 4.00× | **35.6 / 2.85×** | 49.7 / 3.97× | 34.4 / 2.75× | 34.2 / 2.73× | 35.1 / 2.81× |
| | | V3 | 64.5 / 5.16× | **49.2 / 3.93×** | 50.1 / 4.01× | **35.0 / 2.80×** | 49.1 / 3.93× | 34.7 / 2.77× | 34.6 / 2.77× | 34.8 / 2.79× |
| 2 | 19.00 | V1 | 68.6 / 3.61× | **50.9 / 2.68×** | 52.0 / 2.73× | **40.0 / 2.11×** | 53.5 / 2.82× | 38.4 / 2.02× | 38.4 / 2.02× | 39.6 / 2.08× |
| | | V2 | 65.2 / 3.43× | **49.7 / 2.62×** | 50.0 / 2.63× | **37.8 / 1.99×** | 49.7 / 2.61× | 37.2 / 1.96× | 37.2 / 1.96× | 36.9 / 1.94× |
| | | V3 | 64.6 / 3.40× | **49.2 / 2.59×** | 50.1 / 2.63× | **37.3 / 1.96×** | 49.1 / 2.59× | 37.2 / 1.96× | 37.2 / 1.96× | 37.1 / 1.95× |
| 3 | 25.50 | V1 | 71.1 / 2.79× | **51.4 / 2.01×** | 53.7 / 2.11× | **42.0 / 1.65×** | 53.0 / 2.08× | 40.2 / 1.58× | 40.1 / 1.57× | 48.9 / 1.92× |
| | | V2 | 67.7 / 2.65× | **49.7 / 1.95×** | 50.0 / 1.96× | **39.1 / 1.53×** | 49.7 / 1.95× | 38.2 / 1.50× | 38.2 / 1.50× | 42.4 / 1.66× |
| | | V3 | 67.0 / 2.63× | **49.2 / 1.93×** | 50.1 / 1.96× | **37.8 / 1.48×** | 49.1 / 1.93× | 36.9 / 1.45× | 36.9 / 1.45× | 40.4 / 1.58× |
| 4 | 32.00 | V1 | 74.9 / 2.34× | **52.6 / 1.64×** | 53.8 / 1.68× | **44.1 / 1.38×** | 53.0 / 1.66× | 43.9 / 1.37× | 43.9 / 1.37× | 59.9 / 1.87× |
| | | V2 | 70.1 / 2.19× | **49.3 / 1.54×** | 50.0 / 1.56× | **41.5 / 1.30×** | 49.7 / 1.55× | 41.4 / 1.30× | 41.4 / 1.29× | 51.9 / 1.62× |
| | | V3 | 68.9 / 2.15× | **49.2 / 1.54×** | 50.1 / 1.56× | **40.0 / 1.25×** | 49.1 / 1.54× | 40.0 / 1.25× | 40.0 / 1.25× | 48.6 / 1.52× |
| 5–7 | | all | the baseline's for every variant, agreeing with it to ≤ 0.5 % | | | | | | | |
| 8 | 58.00 | V1 | 77.7 / 1.34× | 77.7 / 1.34× | 76.9 / 1.33× | 77.4 / 1.33× | **69.8 / 1.20×** | 76.8 / 1.32× | **69.9 / 1.21×** | 94.1 / 1.62× |
| | | V2 | 71.2 / 1.23× | 71.3 / 1.23× | 71.3 / 1.23× | 70.8 / 1.22× | **63.9 / 1.10×** | 70.8 / 1.22× | **63.9 / 1.10×** | 83.6 / 1.44× |
| | | V3 | 70.6 / 1.22× | 70.6 / 1.22× | 70.6 / 1.22× | 70.6 / 1.22× | **64.5 / 1.11×** | 70.6 / 1.22× | **64.5 / 1.11×** | 79.9 / 1.38× |

**Against its own 34.75-cycle floor, `g4` runs at 1.46/1.46/1.48/1.51× (V1),
1.43/1.43/1.43/1.42× (V2), 1.41× flat (V3)** for `nblk` = 1/2/3/4 — i.e. it is a
perfectly ordinary 4-wide body in efficiency terms; it is simply doing 4 blocks'
worth of everything. The published `W = 4` cascade reference `cw4` reaches the
same 4-wide group through a per-`nblk` stub with **no** predication and costs
**35.0/37.3/39.3/43.3 cycles** on V2 — i.e. `g4 − cw4` = **+14.7/+12.4/+10.4/+6.4
cycles**, reproducing the decomposition from a completely different direction.

### 4.4 The mask strategy, and the register-pressure finding

`g4` and `g4i` have **identical `.text` (5948 B) and identical slot counts (139)**
and differ only in where the six mask values are materialised. Precomputing them
in the six registers the rotating-key map leaves spare is worth
**+0.3…+0.6 % (V2), +2.0 % (V3), −0.4…+1.3 % (V1, inside its floor)** — real but
small, and it is the *reason* the hoisted variant cannot win: **hoisting the 15
round keys leaves zero spare SIMD registers**, so `g4h` is forced into the inline
strategy.

---

## 5. Mixed-workload measurement

`bench_mix2.c`, mixes **A–F and R1…R6** bit-identical to the sequences in
`_docs/fused-t4p8.md` and `_docs/fused-mix4s4.md`, so the numbers are directly
comparable with both reports. 12 slots, 3 link orderings, 150 reps × 3 processes
per ordering.

| mix | length distribution |
|---|---|
| **A** | `nblk` uniform 1..8 |
| **B** | `nblk` uniform 1..8, every 4th call `nblk` = 64 |
| **C** | `nblk` uniform 1..16 (straddles the fused set and the `nblk>8` path) |
| **D** | `nblk` uniform {1,2} — isolates dispatch depth from footprint |
| **E** | `nblk` uniform 1..4 — exactly the lengths `g4` fuses |
| **F** | 60 % `nblk` = 8, else uniform 1..4 |
| **R1…R6** | only `nblk` ∈ {5,8}, 128 B : 80 B ratio 1/2/3/4/6 |

### 5.1 Δ % vs HEAD, median of 9 processes

| mix | core | **`g4`** | `g4h` | **`a4`** | `g4p8` | `t4` | `t4p8` | `m4s4h` |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| **A** | V1 GV3 | **−9.58** | −8.71 | **−8.65** | −9.50 | −12.90 | −11.83 | −6.04 |
| | V2 GV4 | **−13.40** | −13.30 | **−12.94** | −14.49 | −15.96 | −15.44 | −13.92 |
| | V2 r8g | **−13.28** | −13.18 | **−13.16** | −14.33 | −15.65 | −15.28 | −13.67 |
| | V3 GV5 | **−9.05** | −9.22 | **−11.07** | −9.52 | −15.23 | −15.26 | −11.66 |
| **B** | V1 | **−3.93** | −3.75 | −3.51 | −3.66 | −4.87 | −3.95 | −2.14 |
| | V2 GV4 | **−4.01** | −3.98 | −3.58 | −3.23 | −5.14 | −4.59 | −4.20 |
| | V3 | **−3.17** | −3.13 | −3.59 | −3.20 | −4.88 | −5.11 | −3.84 |
| **C** | V1 | **−4.02** | −3.59 | −3.91 | −4.36 | −5.49 | −5.46 | −3.90 |
| | V2 GV4 | **−4.36** | −4.64 | −4.53 | −4.52 | −5.39 | −5.56 | −5.12 |
| | V3 | **−4.63** | −4.94 | −5.57 | −5.07 | −7.06 | −7.09 | −6.08 |
| **D** | V1 | **−25.58** | −24.62 | **−37.76** | −26.09 | −48.45 | −48.43 | −46.23 |
| | V2 GV4 | **−25.37** | −24.89 | **−43.31** | −25.32 | −46.20 | −46.17 | −46.03 |
| | V3 | **−25.14** | −23.71 | **−41.53** | −25.07 | −45.31 | −45.32 | −45.10 |
| **E** | V1 | **−30.86** | −30.01 | **−30.87** | −30.70 | −40.05 | −39.11 | −31.05 |
| | V2 GV4 | **−30.76** | −30.32 | **−39.77** | −30.72 | −42.55 | −42.93 | −40.18 |
| | V3 | **−28.86** | −27.53 | **−34.84** | −28.86 | −42.73 | −42.71 | −39.56 |
| **F** | V1 | **−11.57** | −10.49 | −11.00 | **−17.96** | −14.48 | −15.23 | +1.60 |
| | V2 GV4 | **−11.83** | −11.82 | −14.30 | **−19.04** | −17.57 | −23.14 | −6.28 |
| | V3 | **−9.32** | −9.09 | −10.67 | **−15.63** | −14.59 | −18.77 | −5.51 |
| **R1** (1:1) | V2 GV4 | −0.81 | −0.71 | −0.69 | **−4.40** | −0.57 | −4.74 | +5.16 |
| **R6** (6:1) | V2 GV4 | −0.19 | +0.03 | +0.00 | **−7.79** | +0.05 | −8.16 | +17.64 |

Placement floors for these mixes: A 0.30–4.28 %, B 0.13–0.36, C 0.18–0.99,
D 0.05–0.48, E 0.04–0.79, F 0.07–0.94, R 0.05–5.69. **Mix A on GV4/r8g is
noise-limited** (`base` A/A 1.5–4.3 %), so mix A rests on the paired controls of
§5.2. Mix D — pure 1- and 2-block traffic — is where `g4`'s flat cost hurts most:
it returns **25 %** where `t4` returns **46–48 %** and even `a4` returns 38–43 %.

### 5.2 Paired controls, both address ranks (placement cancels)

Two variants interleaved `X Y X Y` and again `Y X Y X`, 4-slot binaries, 2
processes each, so every number appears 8 times at two address ranks. Sign
agreement across both orderings is the acceptance criterion. Ranges span all
readings; **+ve = the first named variant is slower**.

**`a4` vs `t4` — the discarded blocks, paired:**

| core | mix A | mix B | mix C | mix D | mix E* | mix F |
|---|---:|---:|---:|---:|---:|---:|
| V1 GV3 | **+4.4…+5.6** | **+1.2…+1.7** | **+1.4…+2.1** | **+16.7…+20.6** | +9.2 | **+3.5…+4.9** |
| V2 GV4 | −1.9…+3.4 (floor 1.6) | **+1.5…+1.9** | **+1.4…+2.1** | **+4.8…+5.7** | +2.8 | **+2.1…+4.4** |
| V2 r8g | −1.6…+4.9 (floor 4.2) | **+1.5…+1.8** | **+1.4…+2.4** | **+4.8…+5.8** | +3.0 | **+2.4…+4.5** |
| V3 GV5 | **+3.6…+5.2** | **+1.1…+1.6** | **+0.6…+1.9** | **+6.3…+7.2** | +7.9 | **+3.3…+4.6** |

*mix E from the 12-slot run (points of Δ vs base).

So in *mixed* traffic the discarded AES costs a little more than at fixed
length — 1–2 % in B/C, 4.8–7.2 % in the pure-{1,2} mix D — and on V1 markedly
more (+17…+21 % in mix D). That extra is **footprint, not AES**: `a4`'s four
4-wide bodies are 8020 B (×1.61) against `t4`'s 7312, and V1 punishes the larger
mapped region, exactly the "what costs is the amount of code actually touched"
effect the truncation run identified.

**`g4` vs `t4` — the structure, paired:** V1 **+3.6…+5.1** (A), **+0.9…+1.4** (B),
**+1.3…+1.9** (C), **+30.6…+45.7** (D), **+3.3…+4.7** (F), ±1.1 (R1);
V2 GV4 **+2.4…+4.0** / **+0.9…+1.4** / **+0.8…+1.6** / **+27.8…+38.6** /
**+5.7…+7.3** / ±1.1; V2 r8g **+2.5…+3.2** / **+0.9…+1.4** / **+0.8…+1.8** /
**+27.8…+38.7** / **+5.5…+7.2** / ±0.3; V3 **+6.0…+6.8** / **+1.8…+2.0** /
**+1.5…+3.0** / **+26.8…+37.0** / **+5.5…+6.5** / ±0.2. Sign-consistent
everywhere except the R mixes, where both fall back and the answer is correctly
"no difference".

**`g4` vs `a4` — how much of `g4`'s mixed-traffic loss is the predication:**
V1 −0.7…−0.3 (A, i.e. `g4` marginally *faster* — its smaller footprint), **+16.5…+20.1** (D);
V2 GV4 +3.2…+5.6 (A), **+24.1…+31.4** (D), **+3.3…+4.1** (F);
V3 **+1.9…+2.8** (A), **+22.0…+28.3** (D), **+2.0…+2.4** (F).
In small-heavy traffic the branch-free machinery dominates; in mixed traffic with
big records the code-size advantage of one region starts to pay `g4` back.

**`g4` vs `g4h` — what key hoisting is worth:** **negative or a tie on every host
and in every mix** — V1 −1.0…−0.3 (A), −0.4…0.0 (B), −0.3…−0.1 (C), −2.0…−0.7 (D);
GV4 −1.0…−0.2 / −0.3…−0.1 / −0.4…+0.4 / −0.7…−0.6; r8g −0.9…0.0 / −0.4…−0.1 /
−0.8…+0.6 / −0.7…−0.6; V3 −1.0…+0.4 / ±0.2 / −0.7…+0.8 / **−1.9…−1.8**.

**`g4` vs `t4p8`** (the family head-to-head): +1.4…+7.2 (A), +0.2…+0.6 (B),
+0.6…+1.6 (C), +27.8…+38.5 (D), **+12.6…+14.8** (F), **+3.7…+4.1** (R1),
**+6.2…+6.6** (R3) on r8g, with the same signs on GV3/GV4/GV5.

**`g4` vs `m4s4h`** (shared region vs shared region): a **tie in A/B/C on the V2
hosts** (−0.2…+0.9), `g4` **better by 2.8…3.3** on V3 in mix A, `g4` **worse by
+27…+38 in mix D**, and `g4` **better by 5.2…13.5 in F and 5.6…11.3 in R1/R3**
because `m4s4h` regresses 128 B while `g4` does not.

**`g4p8` vs `t4p8`:** +0.8…+7.8 (A), +0.8…+1.3 (B), +0.7…+1.5 (C),
+27.8…+38.7 (D), +3.8…+5.4 (F), ±0.6 (R1/R3) — i.e. `g4p8` matches `t4p8`
wherever only 80/128 B traffic is involved and loses wherever 16–64 B appears,
which is `g4`'s deficit and nothing new.

---

## 6. Verdict on the premise, and on the prediction

| claim under test | verdict |
|---|---|
| **"Running 4 blocks when only 1–3 are needed costs ~nothing, because at 1–3 blocks the kernel is latency-bound, not throughput-bound."** | **CONFIRMED, and by a wide margin.** +1.9 cyc (V1), +1.2–1.3 (V2), +0.3 (V3) at `nblk` = 1; +1.6/+0.5/+0.1 at 2; +1.9/+0.9/+0.8 at 3; 0 at 4. Measured with a one-parameter control (`a4`), paired at both address ranks, on four hosts. The mechanism is confirmed too: the exact-1 body runs at 3.13–3.28× its own slot floor, so the latency shadow exists, and `a4` fills it (1.51–1.62×) without adding time. |
| **The quoted arithmetic** ("exact-1 measures 12.34 ns of which ~10.1 ns is irreducible chain, while 4 blocks issue in ~9.7 ns and should hide under it") | **Essentially right.** Measured exact-1 = 12.32 ns (V2), and 4 blocks of AES + 1 block of GHASH = 12.75 ns, i.e. **0.43 ns of the ~9.7 ns of extra issue survives** — 96 % of it hid, and 99 % on V3. |
| **"If it is right, `g4` gets most of the small-length win from one code region instead of four separate bodies."** | **NOT CONFIRMED — this is the negative.** The premise is right about the AES but does not carry to `g4`, because a single entry point also forces the *GHASH* half to be uniform and branch-free. `g4` keeps **59 / 60 / 59 / 59 %** of `t4`'s uniform-small value and only 59–63 % over the four fused lengths. The cost is 6.4–7.8 cyc of unavoidable 4-lane GHASH plus 5.4–6.8 cyc of masking, against 0.3–1.9 cyc of discarded AES. |
| **"`g4` ties the cascade 4→1 at 16/32 B (both latency-bound) and beats it materially at 48 and 64 B, because 4-wide runs 8.01 cyc/block against sequential's 9.32."** | **HALF CONFIRMED — the mechanism yes, the outcome no.** `g4` does **not** tie at 16/32 B: it loses **22.1–22.6 points at 16 B** and **16.5–19.6 at 32 B**, because at those lengths it runs four GHASH lanes where the cascade runs one or two, and that work cannot hide the way the AES can. At 48 B it still **loses** (+3.5 V1, +10.8 V2, +13.1 V3). It **wins only at 64 B**, by 9.8 points on V1 and 3.1–3.8 on V2, and is a **tie on V3** (+0.9). The *slope* claim is confirmed exactly: `g4`'s marginal cost per extra block is **0.0 ± 0.6 cyc** against the cascade's measured **8.00 / 5.60 / 4.60 cyc/block** — 4-wide is the cheaper way to add a block on every core — but `g4` pays a **≈14.5-cycle constant** for uniformity that the slope only repays at `nblk` = 4, and only on the two older cores. |
| **128 B is not accelerated — intended** | **Confirmed, and the fall-back is free.** 128 B is inside the control's own floor on all four hosts (+1.23 / +0.66 / +0.68 / −0.02 % vs `dsp0`), as are 80/96/112/256/512/1024/4096 B, with only 2 not-taken dispatch instructions. |

---

## 7. Recommendation

**Do not build `g4`. Between the two one-region shapes, the cascade 4→1 is the
better one** — it wins at three of the four fused lengths on every core, and by
much more than `g4` wins at the fourth.

1. **Is `g4` the right shape?** **No, and forgoing 128 B is not what is wrong with
   it.** Forgoing 128 B is free and clean: the fall-back is
   instruction-for-instruction HEAD's and measures inside the noise floor at every
   length ≥ 80 B on four cores, with 2 dispatch instructions (half of `t4p8`'s).
   What is wrong is that **one entry point forces branch-free predication over a
   uniform four-lane GHASH, and that costs 13–14 cycles where the discarded AES
   costs 1**. Summed over the four fused lengths, uniformly weighted:

   | design | `.text` | × | paths | value over `nblk` 1..4 (V1/V2/V3) | 16 B | 32 B | 48 B | 64 B |
   |---|---:|---:|---:|---|---:|---:|---:|---:|
   | **`g4`** | **5948** | **1.20** | **1** | **27.1 / 25.9 / 25.8 %** | −24.9 / −23.4 / −23.8 | −25.8 / −23.7 / −23.9 | −27.7 / −26.5 / −26.6 | **−29.8 / −29.7 / −28.7** |
   | **cascade 4→1** (`m4s4h`, `nblk` ≤ 4) | 6716* | 1.35* | 4 | **34.7 / 37.9 / 39.3 %** | **−47.0 / −45.9 / −46.0** | **−42.3 / −43.3 / −42.6** | **−31.2 / −37.3 / −39.7** | −20.0 / −25.9 / −29.5 |
   | `t4` (four separate bodies) | 7312 | 1.47 | 4 | 43.8 / 43.5 / 43.9 % | −46.7 / −47.0 / −46.3 | −43.9 / −42.9 / −42.4 | −43.5 / −43.6 / −44.8 | −41.3 / −40.9 / −42.0 |
   | `a4` (four bodies, 4-wide AES each) | 8020 | 1.61 | 4 | 41.9 / 42.5 / 43.4 % | −44.1 / −45.2 / −45.8 | −41.6 / −42.0 / −42.3 | −40.9 / −42.3 / −43.5 | −41.2 / −40.9 / −42.0 |

   *`m4s4h`'s 6716 B includes its `nblk` = 8 group, which is dead at these
   lengths; the cascade-only build (`s4h` in `_docs/fused-mix4s4.md`) is **5980 B,
   ×1.20** — i.e. **the same code size as `g4`** (32 B larger) **for 7.6 / 12.0 / 13.5 more
   points of value over the fused range** (V1 / V2 / V3). That is the whole decision in one line.

2. **The two terms on which `g4` wins are code size and path count** — 5948 B
   (×1.197, the smallest thing in the family that fuses anything) and **1**
   straight-line path against the cascade's 4 entry labels and 15
   (group, entry-context) pairs. If a single fused path were worth 8–14 points of
   small-message performance, `g4` would be the choice; on the measured numbers it
   is not, and `s4h` shows the size argument is not even exclusive to `g4`.

3. **Does key hoisting pay? No.** Tie-to-slightly-negative at fixed length
   (rotating keys faster by 0.3–1.4 points on GV4/r8g/GV5, 1.6–3.3 on GV3) and
   negative or a tie in every mix at both address ranks, for 16 B more `.text`.
   The reason is structural and worth recording: **`g4` has exactly one group, so
   both modes load the 15 round keys once** — hoisting cannot save the per-group
   reloads that made it worth 1.8–7.2 points in `mix4s4`'s five-group region — **and
   hoisting consumes the six spare registers the mask values want**, forcing the
   slower inline mask strategy. Hoisting pays when a region has several groups.

4. **What the numbers say about where the idea does apply.** Two facts are worth
   carrying forward, because both are now measured rather than inferred:
   * **Over-running the AES is nearly free** (0.3–1.9 cyc for three surplus
     blocks), so any *future* shape may over-run the AES without hesitation;
   * **a uniform GHASH is not free, and predication is not the way to avoid it.**
     Even the predication-free diagnostic `g4nn` — uniform four-lane GHASH, no
     masks, no clamped addressing, a flat 42.0 cycles on V2 — still loses to the
     cascade by 6.9 and 5.1 cycles at `nblk` = 1 and 2, ties at 3 and wins at 4.
     So the 16 B and 32 B losses are **the four GHASH lanes, not the masking**, and
     no cleverness in the predication recovers them.

   Together those two say the useful lever is "share the AES, reach the exact
   GHASH by a branch". That shape is **not measured here** — the family's gain
   comes from interleaving GHASH *into* the AES rounds (§1.3), and a shared AES
   block followed by a branched tail can only interleave the one GHASH section
   every entry executes, which may well give most of it back. Quantifying that is
   the natural next experiment; nothing in this report predicts its outcome.

---

## 8. What rests on one host, and other limits

* The **make-driven KAT** (real `arm/Makefile` + `arm/aes-gcm/kat/Makefile`, with
  the make-built object byte-compared to the harness object) ran **only on r8g**,
  because the GV hosts have no checkout of the tree. Every object is
  md5-identical on all four hosts, so this is a build-path check, not a
  microarchitectural one.
* **GV3's 16–80 B placement floors are wide this run** (`g4AA` 2.3–5.8 %,
  `base` 2.3 % at 48 B). The V1 fixed-length column is reported as measured, but
  every V1 conclusion is carried by the paired both-rank controls of §5.2 and by
  the decomposition of §4, whose V1 readings are internally consistent to
  ≤ 0.3 cycles.
* **16 B on the V2 hosts** carries the documented placement lottery (`base` A/A
  4.3–8.8 %); the variants themselves are stable to ±0.15 %. V3, whose floor is
  ≤ 0.08 % at 16–64 B, is the arbiter for those lengths.
* **Mix A on GV4/r8g is noise-limited** (`base` A/A 1.5–4.3 %); its conclusions
  rest on §5.2.
* `g4nm`/`g4nn` are **deliberately incorrect** for `nblk` ≠ 4 and exist only to
  attribute cycles at `nblk` = 4; they were run with `ALLOW_MISMATCH`, are never
  quoted as results, and are excluded from every KAT and byte-compare claim.
* The `g4` GHASH/MODULO split point was swept (`k1` ∈ {0.20, 0.25, 0.28, 0.30,
  0.32, 0.35, 0.38, 0.45, 0.60}) on r8g; the spread was 0.5–2.9 % and **0.30**
  was chosen and used on all hosts. `a4` uses `gen.py`'s published per-`n`
  schedule unchanged. A 1 % scheduling gain would not touch any conclusion.
* **`g4p8` was measured but is excluded from every conclusion**, per the fixed
  scope: a dedicated `nblk` = 8 body is not wanted, so `nblk` ∈ {5,6,7,8} and above
  fall back permanently. Its rows remain in the raw tables and in
  `_docs/fused-g4/logs/` only so the run is reproducible; no recommendation rests
  on it, and 128 B is treated purely as a fall-back-is-free check.
* All numbers are single-thread and `taskset`-pinned, and say nothing about SMT
  or multi-tenant I-cache pressure — where `g4`'s 2884 B advantage over `t4p8`
  would, if anything, favour `g4`.

---

## 9. Artefacts

`_docs/fused-g4/`

| file | what |
|---|---|
| `gen_g4.py` | the single-region generator: `g4` / `g4i` / `g4h` / `g4p8`, the `a4` control (`gen.py` `body(n, n_aes, k)` with `n_aes = 4`), the `g4nm`/`g4nn` diagnostics and the `zlaneJ` / `zapall` / `brk` probes. Imports `gen_cascW.py`, `gen.py`, `gen_trunc.py`, `gen_set.py`; self-checks md5-identical to `gen_trunc`'s `t4` at `n_aes = 1` |
| `verify_g4.py` | adjacency, slot/`aese`/load accounting, **the per-region instruction mix and the AES-unit index of every interleaved GHASH/MODULO op (the fusion evidence of §1.3)**, and the structural asserts on the predication (4 clamped loads and 4 ascending clamped stores off the same registers, 0 post-indexed accesses, 3 `subs`/3 `csel`/6 `csetm`/6 `dup`, each of `H^4..H^1` once, `Xi'` dead before the MODULO constant, frame 80 B) |
| `mkbench12g.py`, `build_bench12g.sh` | `bench12.c` → `bench12g.c`: adds the "nothing written past `16*nblk`" assert for every variant at every length |
| `brkprobe.c` | the `brk #0` entry/non-entry probe and the `guard`/`guardlo` PROT_NONE memory-safety probe |
| `provision_g4.sh` | builds `g4 g4i g4h g4nm g4nn g4p8 a4 x4 dsp0 t4 t4p8 m4s4h cw4` + the three self-checks + the `.text`/slots tables |
| `verify_g4.sh` | `.text`/frame, dispatch listing, normalised `objdump`, adjacency+slots, 256-length byte-compare, KAT relink |
| `probe_g4.sh` | the 33 lane-mapping / mis-entry / `brk` / guard-page probes |
| `measure_g4.sh` | 12-slot per-length driver, 3 link orderings × 5 processes × 300 reps |
| `measure_aux_g4.sh` | the 8-slot decomposition driver (§4) |
| `measure_mixg4.sh`, `mixaa_g4.sh` | 12-slot mixed-length driver and the 4-slot placement floors / paired both-rank comparisons |
| `analyze_g4.py`, `analyze_aux_g4.py`, `analyze_mixg4.py` | every table in §3–§5 |
| `runall_g4.sh`, `setup_gv_g4.sh` | per-host driver and fresh-host provisioning |
| `logs/` | every raw log from all four hosts (60 per-length + 36 mixed-length + 16 decomposition processes, controls, probes, verify, clocks, `.text` and slot tables) |

Reused unchanged from the earlier runs: `gen.py`, `gen_cascW.py`, `gen_trunc.py`,
`gen_set.py`, `gen_mix.py`, `bench12.c`, `bench_mix.c`, `mkmix2.py`, `mk.sh`,
`kat.sh`, `makekat_t.sh`, `objcmp.py`, `verify.py`, `clk.c`, and the `dsp0`
control.
