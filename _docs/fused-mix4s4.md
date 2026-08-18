# `mix4s4` — one shared region, a 4-wide group then four sequential single-block sections, entries `{1,2,3,4,8}` — measurement only

Companion to `_docs/fused-cascade-experiment.md` (the width sweep),
`_docs/fused-truncation-curve.md` (the truncation family) and
`_docs/fused-t4p8.md` (separate bodies for the same entry set `{1,2,3,4,8}`).
Same kernel, same harness, same discipline, and every retained body is emitted
by the **same published generators**, so this is a controlled extension of the
family rather than a new experiment.

Kernel `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` at local HEAD;
`obj/base.o` md5 `114cedb51f36c584e50843d2838d871e` — the object `arm/Makefile`
produces in the synced tree, **and the object all four hosts built locally**.
**No HOL Light, no `.ml`, no proofs, no gates.** All work in `/tmp/fsp` (and
`/tmp/fst` for the make-driven KAT on the dev host); **no tracked file was
modified, `~/clean-gate` and `~/kat-check` were not touched, and no instance was
started, stopped, rebooted or terminated.**

| host | core | part | clock measured on the spot |
|---|---|---|---|
| GV3 | Neoverse-V1 | `0xd40` | **2.5910 GHz** |
| GV4 | Neoverse-V2 | `0xd4f` | **2.7932 GHz** |
| GV5 | Neoverse-V3 | `0xd84` | **3.2902 GHz** |
| `ec2r8g` | Neoverse-V2 (dev) | `0xd4f` | **2.7929 GHz** |

`r8g` and GV4 are the same microarchitecture and reproduce each other to
**≤ 0.2 points at every length** below. The dev host was idle throughout
(load average 0.09, no orchestrator activity).

---

## 0. Headline

| | |
|---|---|
| **Was it built?** | **Yes, and it is correct.** KAT **35/35 / `KAT GATE: PASS`** for all 9 variants on all 4 hosts by genuine relink, **and** through the real `arm/Makefile` + `arm/aes-gcm/kat/Makefile` on r8g with the make-built object **byte-identical** to the harness object (9/9 `SAME`). In-process byte-compare of `out`/`Xi`/`ivec`/return over **all 256 whole-block lengths × 12 slots** on every host. **46/46 liveness and mis-entry probes exact.** `aese` count exactly **14n** at every entry (no dead AES). **0 adjacency violations.** Frame **80 B**. `nblk > 8` content **instruction-for-instruction unchanged**. |
| **`.text`** | **6828 B (×1.374)** rotating keys, **6716 B (×1.352)** with the round keys hoisted — the hoisted one is **2116 B smaller than `t4p8`** (8832, ×1.778) at the same entry set. Dropping `nblk = 8`: **6076 / 5980 B (×1.223 / ×1.204)**. |
| **New code paths** | **5 entry labels / 5 distinct straight-line paths**, in **1** shared code region of **12 labelled blocks** (dispatch, 1 tree node, 5 stubs, 5 groups, 1 shared epilogue). |
| **16 B / 32 B** | **Matches separate bodies.** m4s4h −47.1/−46.3/−46.1/−46.0 % at 16 B and −42.2/−43.4/−43.4/−42.6 % at 32 B (V1/GV4/r8g/V3) against `t4p8`'s −46.9/−47.8/−47.3/−46.3 and −43.9/−42.8/−42.8/−42.4. Differences ≤ 1.6 points and **without a consistent sign** across cores. |
| **48 B / 64 B** | **Loses, by less than predicted on the two newer cores.** m4s4h **−31.3 / −37.3 / −37.3 / −39.7 %** at 48 B and **−20.0 / −25.9 / −25.9 / −29.5 %** at 64 B, against `t4p8`'s −43.5 and −41.0. The deficit is **12.3 / 6.2 / 6.1 / 5.2 points** at 48 B and **21.3 / 14.9 / 14.9 / 12.5 points** at 64 B. |
| **80 / 96 / 112 B — the fallback check** | **Free, on every host.** Every reading is inside that host's own A/A floor: ≤ 0.06 % on V3, ≤ 0.55 % on the V2 hosts, and on V1 the only non-trivial numbers (−1.98 % at 80 B, −0.70 % at 112 B) sit under a **2.44 %** and **5.10 %** floor respectively and are shared by `t4p8`. 4 dispatch instructions on the fall-through path cost nothing measurable. |
| **128 B — the headline negative** | **A large regression, on all four hosts.** m4s4h **+20.95 / +18.03 / +18.09 / +13.26 %** vs HEAD (**+21.40 / +17.97 / +18.01 / +13.22 %** against the placement-matched `dsp0` control), where `t4p8` delivers **−9.6 / −9.9 / −9.9 / −8.6 %**. A **22–31 point** swing. Even the two-4-wide-group cascade (`cw4`) is only +5.1/+7.6/+7.5/+4.6 %. |
| **≥ 256 B** | **Wash.** Max \|Δ\| over all variants and hosts is 1.70 % (V1 256 B, floor 2.50 %); on V3 everything is ≤ 0.67 % against a 512 B floor of 0.48 %. |
| **Do the four sequential blocks overlap in hardware?** | **Partially — and this is now settled by measurement.** They are nowhere near serialised: 4 blocks whose dependence chains total ~112 cycles complete in **59.9 / 52.0 / 48.6** cycles (V1/V2/V3), i.e. ~1.9–2.3 blocks resident. But the overlap is **incomplete**: achieved/floor at `nblk = 4` plateaus at **1.87 / 1.62 / 1.52×** where a 4-wide interleaved body reaches **1.37 / 1.30 / 1.25×**, and the identical work interleaved 4-wide (`cw4`'s `ss4`) is **26 / 20 / 14 % faster**. The ~78-µop vector-issue-queue bound of `fused-cascade-experiment.md` reproduces exactly. |
| **Round-key hoisting matters** | The naive composition (gen_cascW's rotating `v26/v27/v28`, 8 key loads per group = 40 for `nblk = 8`) is **1.8–7.2 points worse** at 48/64 B and **3.6–5.7 points worse** at 128 B than the hoisted version. Both were built; all judgements below use the **hoisted** variant, which is the fair representative of the structure. |
| **Head-to-head vs `t4p8`, mixed traffic** | `t4p8` wins everywhere, paired and at both address ranks: mix A **+0.9…+7.4** points, B **+0.0…+1.9**, C **+0.6…+2.1**, D **+0.2…+3.5**, F (128 B-heavy) **+15.1…+21.5**, and an 80/128 stream **+6.5…+22.2**. |
| **Recommendation** | **Do not ship `mix4s4` as specified. If any shared-region variant is shipped, drop `nblk = 8` from the fused set** — `{1,2,3,4}` fused, 5–8 falling back. That is a *strict* improvement, measured, paired, at both address ranks, on all four hosts: it removes the +13…+21 % 128 B regression at zero cost anywhere else, is 736–848 B smaller, and returns **more** uniform-small-traffic value (16.3/18.1/18.0/18.7 % vs 13.9/15.8/15.8/17.1 %). Even then it is 2.6–6.8 points of uniform-small value behind `t4` at 1216 B less code, and behind `t4p8` in every mix. |

---

## 1. What was built

### 1.1 The structure, exactly as asked for

Four instructions inserted after `add x10, sp, #64` — the `gen_set.py` design-A
("small test first") dispatch, so the `nblk > 8` path takes **no** branch:

```
	cmp	x9, #64				//[MIX] nblk <= 4 ?
	b.le	.L256_dec_mxh_small
	cmp	x9, #128			//[MIX] nblk == 8 ?
	b.eq	.L256_dec_mxh_small
```

and **one** region appended before `.L256_dec_ret`:

```
.L256_dec_mxh_small:   common prep (CTR base, Xi', [round-key hoist])
                       cmp x9,#128 / b.eq stub_8      <- the isolated entry
                       balanced compare tree over {1,2,3,4}
.L256_dec_mxh_stub_8 .. _stub_1    acc <- Xi' * H^n (3 pmull), then b .L_g<n>
.L256_dec_mxh_g8:  4 blocks, H^8,H^7,H^6,H^5, INTERLEAVED over rounds  <- nblk=8
.L256_dec_mxh_g4:  1 block, H^4, all 14 rounds                         <- nblk=4
.L256_dec_mxh_g3:  1 block, H^3, all 14 rounds                         <- nblk=3
.L256_dec_mxh_g2:  1 block, H^2, all 14 rounds                         <- nblk=2
.L256_dec_mxh_g1:  1 block, H^1, all 14 rounds, with the MODULO reduce,
                   the tag store and the counter store interleaved into
                   this group's AES rounds
.L256_dec_mxh_done:   mov x0,x9 / frame pop / ret        (shared epilogue)
```

Entering at `.L_g<r>` executes every group with remaining count ≤ `r`, i.e.
exactly `r` blocks: `nblk = 8` runs the 4-wide group and then all four
sequential sections; `nblk ∈ {1,2,3,4}` runs only sequential sections.
`nblk ∈ {5,6,7}` and `nblk > 8` never leave the baseline path.

Two deviations from the diagram in the brief, both forced and both recorded here
rather than silently:

1. **The plaintext stores are per group, not in the shared tail.** Each group's
   AES states are the registers the next group reuses, so a group must store its
   own blocks before falling through. The GHASH *accumulation* is shared (three
   `eor` folds per block into `v17/v18/v19`), and the MODULO reduce, tag store,
   counter store and epilogue are shared, as specified.
2. **The common prep is emitted once and the `nblk == 8` test is repeated
   inside it.** Both outer tests branch to the same `_small` label; `x9` is
   still live, so one `cmp/b.eq` inside routes `nblk = 8` to its stub. The
   alternative (a second copy of the prep) would trade 11 instructions of code
   for 2 dynamic instructions on the fused paths. The fall-through path is
   unaffected either way and remains 4 not-taken instructions, as in `t4p8`.

### 1.2 The generator is a composition, and it self-checks

`_docs/fused-mix4s4/gen_mix.py` **imports** and reuses:

* `fused-cascade/gen_cascW.py` — `common()`, `stub()`, `gen_body()`,
  `ghash_blk()`, `late_ops()`, `place()`, `epilogue()`. In the default
  ("rotate") key mode a group of width *w* is **instruction-for-instruction**
  the code the published width-*w* cascade ships.
* `fused-truncation/gen_cascWt.py` — the balanced compare `tree()` and the
  truncated entry test, verbatim.
* `fused-t4p8/gen_set.py` — the discontiguous design-A dispatch (reproduced for
  the cascade label scheme; the instruction sequence is `gen_set.entry()`'s).

The generalisation is one parameter: a **list of group widths** instead of a
single width `W`. `mix4s4` is `[4,1,1,1,1]`; the "drop `nblk = 8`" variant is
`[1,1,1,1]`.

**The self-check that makes this a controlled extension**, run on all four
hosts: with widths `1,1,1,1,1,1,1,1` and rotating keys the generator must
reproduce `gen_cascW.py`'s `W = 1` object bit for bit:

```
  gc1=fd208e8dd6a8ee0b72ef7cdca82b2b4c cw1=fd208e8dd6a8ee0b72ef7cdca82b2b4c  SAME
```

Every object in this run is md5-identical across GV3, GV4, GV5 and r8g (same
gcc 13.3 / binutils 2.42), so the static checks are literally the same objects
on every core. `obj/t4.o` reproduces the published `c3f72ffe…`, `.text` for
`t4p8` reproduces the published 8832 B, and `cw4` reproduces the cascade run's
`51bbb39c…`.

### 1.3 The two key modes, and why both were measured

A width-4 group needs 4 AES states **and** 4 ciphertext registers, so the 15
round keys cannot be hoisted the way the published `W = 1` cascade (`casck`)
hoists them; `gen_cascW` rotates them through `v26/v27/v28` and pays **8 key
loads per group** — 40 for `nblk = 8`. That is a known ~1.9 cyc/block tax
(published: rotating `W=1` 11.20 vs hoisted `W=1` 9.32 cyc/block on V2) and it
is **not part of the structure under test**, so a hoisted mode was built too:

| | `m4s4` (rotate) | `m4s4h` (hoist) |
|---|---|---|
| round keys | `v26/v27/v28`, reloaded per group | `v1..v15`, loaded **once** (8 instructions) in the common prep |
| 4-wide group states | `v0..v3`, ciphertext held in `v8..v11` | `v0,v26,v27,v28`; ciphertext loaded transiently into `v30` for the GHASH and **reloaded** (2 `ldp`, L1-hot) for the final `eor3` — the trick `gen.py`'s `late_ops` already uses |
| 1-wide section | state `v0`, ciphertext `v8` | state `v0`, ciphertext `v26` |
| load instructions, `nblk = 8` | 71 | **43** |
| load instructions, `nblk = 4` | 53 | **29** |
| SIMD **issue slots**, `nblk` 1/2/3/4/8 | 50 / 76 / 102 / 128 / 232 | **identical** |
| `.text` | 6828 | 6716 |

Because the slot counts are identical, the two modes differ **only** in load
traffic, and the hoisted one is the fair representative of the structure. The
GHASH/MODULO split points are the published cascade settings
(`ksec = 1.0, k1 = 0.35`); the cascade run's sweep of those knobs was 1.1–1.2 %
flat, so none was repeated.

### 1.4 Slots and the floor

Per-`nblk` slot accounting (`verify_mx.py`, convention of
`fused-cascade-experiment.md`: adjacent `aese`+`aesmc` = 1 slot, `.inst`-encoded
`eor3` counted, loads/stores excluded), identical for both key modes:

| region | slots | `aese` |
|---|---:|---:|
| common prep + dispatch | 6 | 0 |
| each entry stub | 5 | 0 |
| `g8` (4 blocks, 4-wide) | **104** | 56 |
| `g4`, `g3`, `g2` (1 block each) | 26 | 14 |
| `g1` (1 block + MODULO/tag/counter) | 39 | 14 |
| shared epilogue | 0 | 0 |

| `nblk` | slots | floor @4/cyc | `aese` | want `14n` |
|---:|---:|---:|---:|---:|
| 1 | 50 | 12.50 | 14 | 14 ✓ |
| 2 | 76 | 19.00 | 28 | 28 ✓ |
| 3 | 102 | 25.50 | 42 | 42 ✓ |
| 4 | 128 | 32.00 | 56 | 56 ✓ |
| 8 | 232 | 58.00 | 112 | 112 ✓ |

`g8`'s 104 slots equal 4 × 26: **the 4-wide group and four sequential sections
are the same slot count**, so the whole experiment is again a controlled
comparison in one variable — how much independent work sits adjacent in program
order.

---

## 2. Correctness

| check | result |
|---|---|
| **Build fidelity** | Every object md5-identical on all 4 hosts; `obj/base.o` = `114cedb51f36c584e50843d2838d871e`. On r8g the object built by the **real `arm/Makefile` `%.o : %.S` rule** (in a scratch copy of `arm/` + `include/`; no tracked file touched, `make clean` never run in `arm/aes-gcm/kat`) is **byte-identical** to the harness object for `base dsp0 t4 t4p8 cw4 m4s4 m4s4h s4 s4h` — `make-built .o vs mk.sh .o: SAME` ×9. |
| **KAT, make-driven** | `make aes-gcm/aesv8_gcm_8x_dec_256_wb.o` then `make -C aes-gcm/kat run`, `kat_wb_dec` **deleted first** so no stale link can be tested: `35 passed, 0 failed … KAT GATE: PASS` for all 9 variants. |
| **KAT, harness relink** | `kat.sh` (`gcc -O2 -o kat/kat_wb_dec kat_wb_dec.c obj/<v>.o obj/ref.o`, binary deleted first): **35/35 PASS for all 9 variants on all four hosts** (36 runs). |
| **In-process byte-compare** | 12 slots in one binary (`base baseAA dsp0 dsp0AA m4s4 m4s4AA m4s4h s4 s4h t4p8 t4 cw4`), `out`/`Xi`/`ivec`/**return value** compared over **every whole-block length 1..256 blocks**: `SELFCHECK OK (256 whole-block lengths 1..256 blk x 12 variants; out/Xi/ivec/ret byte-identical)` on all four hosts, **re-run at the start of every one of the 15 per-length timing processes per host** and of every probe. Non-degeneracy (`out != in`) asserted at every length. |
| **Per-entry liveness probes** | `zapN` (entry stub `N`'s `Xi'·H^N` seed zeroed) for **N = 1,2,3,4,8** in both key modes: each fails at **exactly `nblk = N`** and nowhere else. |
| **Mis-entry boundary probe** | `zapALL` (all five stubs zapped): **fails at exactly `nblk = {1,2,3,4,8}`, never at 5, 6, 7, never at ≥ 9** — both key modes. For the `{1,2,3,4}` variants: exactly `{1,2,3,4}`. |
| **Fall-through-structure probes** | `zsecP` zeroes the products of the block that uses `H^P`, so the failing set is fixed by the fall-through shape and a mis-entry would move the boundary. Measured, both key modes: `zsec1 {1,2,3,4,8}` · `zsec2 {2,3,4,8}` · `zsec3 {3,4,8}` · `zsec4 {4,8}` · `zsec5 = zsec6 = zsec7 = zsec8 {8}` — every one exactly as the structure predicts. This is the direct test of the characteristic bug (entering at `.L_3` while the code assumes 4 live keystream registers): such a bug shows up here as a shifted boundary. It does not. |
| **Total probes** | **46/46 exact**, on all four hosts, with no collateral failure at any other length in any probe. |
| **Adjacency** | `0 aese/aesmc violations` in `m4s4 m4s4h s4 s4h t4 t4p8 cw4`, whole-file scan. |
| **No dead AES** | `aese` count is exactly `14n` at each of the five entries (table §1.4). |
| **Frame** | **80 B**: one `stp d8,d9,[sp,#-80]!`, `1 + 1` matching `ldp d8,d9,[sp],#80` (baseline epilogue + the one shared epilogue), and **0** `add/sub sp` anywhere in source or `objdump`. No new callee-saved register is written. |
| **`nblk > 8` content** | Normalised `objdump` (`objcmp.py`, addresses and branch targets masked): `m4s4` = *4 instructions inserted at baseline instruction 14, then 1226 more baseline instructions identical, `.L256_dec_ret` stub found verbatim (relocated), 461 appended* → **VERDICT: nblk>8 content UNCHANGED**. `m4s4h` +433, `s4`/`s4h` 2 inserted, and the same verdict for `dsp0 t4 t4p8 cw4`. |

---

## 3. Fixed-length measurement

Discipline as established: every variant `objcopy --redefine-sym`'d to a distinct
symbol and linked into **one** 12-slot binary, round-robin with the slot order
rotated every rep, `taskset -c 3`, 200-call warm-up per pass, **best of 300 reps
× 5 processes × 3 link orderings = 15 processes per host**. `base` is pinned to
link slot 0 as in the published runs so the tables are comparable. `baseAA`,
`dsp0AA` and `m4s4AA` are the same objects again, so `base`, the dispatch
control and the variant under test each have their own placement floor.

Sanity anchors, r8g/GV4 vs `_docs/fused-t4p8.md`: `t4p8` −47.25/−42.80/−43.49/
−40.84 at 16/32/48/64 B and −9.92 at 128 B against the published −47.21/−42.80/
−43.48/−40.88 and −9.94; `cw4` −41.94/−38.05/−24.78/−17.97/−9.62/+7.60 at
48…128 B against the cascade run's −41.8/−38.1/−24.6/−18.0/−9.7/+7.0. **The
harness reproduces both published runs to ≤ 0.6 points.**

### 3.1 Δ % vs HEAD, all 12 lengths, all four hosts (absolute-min estimator)

**GV3 — Neoverse-V1, 2.5910 GHz**

| variant | `.text` | × | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| HEAD | 4968 | 1.00 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `dsp0` ctl | 4976 | 1.00 | +0.48 | −0.12 | +0.48 | −0.16 | −0.02 | +0.04 | −0.24 | −0.37 | −0.15 | +0.10 | −0.80 | −0.16 |
| **`m4s4`** | 6828 | 1.37 | **−48.02** | **−42.22** | **−29.44** | **−12.81** | −0.23 | +0.40 | −0.05 | **+26.62** | −0.88 | +0.27 | −0.20 | +0.12 |
| **`m4s4h`** | 6716 | 1.35 | **−47.09** | **−42.23** | **−31.27** | **−20.00** | −1.98 | +0.35 | −0.70 | **+20.95** | −1.70 | +0.78 | +0.01 | +0.14 |
| `s4` | 6076 | 1.22 | −47.86 | −42.19 | −29.40 | −12.79 | +0.55 | +0.04 | −0.17 | −1.30 | −0.59 | −0.41 | −0.37 | −0.15 |
| **`s4h`** | 5980 | 1.20 | **−47.06** | **−42.14** | **−31.27** | **−20.00** | +0.54 | −0.03 | −0.22 | **−0.13** | −0.93 | −0.04 | −0.73 | −0.13 |
| `t4p8` | 8832 | 1.78 | −46.85 | −43.86 | −43.57 | −41.29 | −1.98 | +0.31 | −0.07 | **−9.63** | +0.44 | +0.88 | +0.22 | +0.07 |
| `t4` | 7312 | 1.47 | −46.71 | −43.93 | −43.50 | −41.33 | +0.55 | +0.02 | −0.28 | −0.88 | −0.49 | +0.06 | −0.36 | −0.21 |
| `cw4` | 9336 | 1.88 | −48.06 | −44.63 | −41.37 | −36.72 | −17.57 | −14.11 | −8.73 | +5.07 | +0.09 | −0.56 | −0.13 | −0.04 |

A/A floors (worst \|Δ\| of any of the 15 processes): `base` 0.54/0.39/1.07/0.22/
0.44/0.20/**5.10**/0.63/0.50/1.29/0.45/0.40; `m4s4` 0.43/0.40/0.29/0.71/**2.44**/
0.25/0.76/1.15/**2.50**/1.11/0.77/0.29; `dsp0` 0.91/0.25/1.23/0.25/0.81/0.22/
1.17/0.71/0.60/0.76/0.87/0.19.

**GV4 — Neoverse-V2, 2.7932 GHz**

| variant | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `dsp0` ctl | +0.45 | −0.14 | −0.13 | +0.02 | +0.04 | +0.05 | −0.19 | +0.06 | +0.55 | −1.36 | −0.06 | −0.19 |
| **`m4s4`** | **−46.43** | **−43.19** | **−33.22** | **−21.20** | +0.08 | +0.04 | +0.20 | **+21.64** | +0.38 | −0.88 | −0.27 | +0.02 |
| **`m4s4h`** | **−46.31** | **−43.44** | **−37.33** | **−25.91** | +0.06 | +0.04 | +0.00 | **+18.03** | +0.45 | −0.49 | −0.16 | +0.00 |
| `s4` | −46.43 | −43.18 | −33.29 | −21.00 | +0.02 | +0.12 | +0.03 | +0.78 | +0.57 | −0.91 | −0.28 | −0.21 |
| **`s4h`** | **−46.48** | **−43.40** | **−37.36** | **−25.80** | +0.02 | −0.52 | −0.08 | **+0.86** | +0.53 | −0.12 | −0.20 | +0.03 |
| `t4p8` | −47.76 | −42.77 | −43.48 | −40.82 | +0.07 | −0.34 | +0.01 | **−9.90** | +0.49 | −0.28 | −0.64 | +0.05 |
| `t4` | −47.38 | −42.99 | −43.55 | −40.86 | +0.02 | +0.01 | −0.18 | +0.15 | +0.52 | −0.16 | −0.17 | −0.09 |
| `cw4` | −46.62 | −43.25 | −41.93 | −38.02 | −24.77 | −17.94 | −9.63 | +7.59 | +0.52 | −0.43 | −0.00 | −0.02 |

A/A floors: `base` **4.90**/0.18/0.12/0.16/0.08/0.20/0.35/0.89/0.63/1.16/0.54/
0.10; `m4s4` 0.10/0.17/0.14/0.51/0.09/0.17/0.43/0.10/0.23/0.96/0.41/0.13;
`dsp0` **7.35**/0.12/0.11/0.28/0.08/0.16/0.46/0.85/0.14/1.36/0.18/0.29.
(The 16 B placement lottery documented in `fused-t4p8.md` again; `base` landed
slow, so every 16 B Δ % on the V2 hosts must be read with a ±5–8 % floor. The
variants themselves are stable at 16 B to ±0.10 %.)

**`ec2r8g` — Neoverse-V2, 2.7929 GHz** (inter-instance reproduction of GV4)

| variant | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `dsp0` ctl | −0.15 | −0.11 | −0.16 | +0.01 | +0.01 | +0.04 | −0.19 | +0.07 | −0.29 | −0.79 | −0.04 | −0.05 |
| **`m4s4`** | **−46.24** | **−43.18** | **−33.24** | **−21.21** | +0.08 | +0.02 | +0.20 | **+21.70** | −0.38 | −1.29 | −0.63 | −0.15 |
| **`m4s4h`** | **−46.13** | **−43.43** | **−37.34** | **−25.92** | +0.05 | −0.02 | +0.24 | **+18.09** | −0.38 | −0.27 | −0.08 | −0.27 |
| `s4` | −46.23 | −43.18 | −33.31 | −21.03 | +0.00 | +0.07 | −0.14 | +0.83 | −0.20 | −1.30 | +0.02 | −0.14 |
| **`s4h`** | **−46.13** | **−43.40** | **−37.39** | **−25.80** | +0.02 | −0.50 | −0.10 | **+0.86** | −0.64 | −0.02 | −0.07 | +0.00 |
| `t4p8` | −47.25 | −42.80 | −43.49 | −40.84 | +0.03 | −0.41 | +0.00 | **−9.92** | −0.29 | −0.44 | −0.24 | +0.01 |
| `t4` | −47.23 | −42.99 | −43.52 | −40.87 | +0.01 | +0.05 | −0.15 | +0.19 | −0.31 | −1.12 | −0.48 | −0.00 |
| `cw4` | −46.41 | −43.26 | −41.94 | −38.05 | −24.78 | −17.97 | −9.62 | +7.60 | −0.23 | −0.33 | +0.05 | −0.08 |

**GV5 — Neoverse-V3, 3.2902 GHz** (the quiet host: A/A ≤ 0.09 % everywhere
except 512 B, 0.48 %)

| variant | 16 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `dsp0` ctl | +0.03 | +0.05 | +0.00 | +0.03 | +0.05 | +0.08 | −0.37 | +0.03 | +0.02 | +0.58 | +0.00 | +0.00 |
| **`m4s4`** | **−45.92** | **−42.39** | **−37.40** | **−25.69** | −0.01 | −0.05 | −0.00 | **+16.20** | +0.00 | +0.48 | +0.01 | +0.00 |
| **`m4s4h`** | **−46.02** | **−42.58** | **−39.70** | **−29.51** | +0.04 | −0.04 | −0.05 | **+13.26** | +0.03 | +0.67 | +0.00 | +0.00 |
| `s4` | −45.92 | −42.42 | −37.39 | −25.64 | +0.02 | +0.08 | −0.36 | +0.03 | +0.01 | +0.50 | +0.00 | +0.00 |
| **`s4h`** | **−45.94** | **−42.58** | **−39.69** | **−29.52** | +0.05 | +0.07 | +0.07 | **+0.03** | −0.12 | +0.65 | +0.01 | +0.00 |
| `t4p8` | −46.27 | −42.42 | −44.90 | −42.00 | +0.03 | −0.03 | −0.04 | **−8.58** | +0.04 | +0.51 | +0.01 | +0.00 |
| `t4` | −46.32 | −42.42 | −44.82 | −42.00 | +0.05 | +0.05 | −0.38 | +0.03 | +0.02 | +0.66 | +0.00 | −0.00 |
| `cw4` | −45.92 | −41.13 | −41.78 | −38.23 | −26.13 | −19.35 | −10.52 | +4.62 | +0.00 | +0.52 | +0.01 | +0.00 |

**512 B and 1024 B, measured here for the first time for any fused variant, are
a wash on every host and every variant** — as the byte-identical `nblk>8` path
requires. The largest reading anywhere in the 256 B–4 KB block is 1.70 %
(V1 256 B, floor 2.50 %); on V3 the largest is 0.67 % at 512 B against a 0.48 %
floor.

### 3.2 The 128 B column against a `dsp0`-style control

`base` sits in link slot 0 and carries the placement bias documented in the
truncation run, so the 128 B column is referenced to the never-taken-dispatch
control. Min estimator:

| | V1 GV3 | V2 GV4 | V2 r8g | V3 GV5 |
|---|---:|---:|---:|---:|
| `dsp0AA` vs `dsp0` (the control's own floor) | −0.02 | +0.76 | +0.67 | +0.01 |
| `baseAA` vs `dsp0` | −0.07 | +0.54 | +0.56 | −0.02 |
| **`m4s4h` vs `dsp0`** | **+21.40** | **+17.97** | **+18.01** | **+13.22** |
| `m4s4` vs `dsp0` | +27.09 | +21.57 | +21.62 | +16.16 |
| **`s4h` vs `dsp0`** | **+0.24** | **+0.80** | **+0.79** | **+0.00** |
| `t4p8` vs `dsp0` | −9.30 | −9.95 | −9.98 | −8.61 |
| `cw4` vs `dsp0` | +5.46 | +7.53 | +7.53 | +4.59 |

The regression survives every reference and every core. `s4h`'s 128 B reading is
inside the control's own floor on all four hosts, i.e. **dropping `nblk = 8`
makes 128 B exactly a wash**, which is the point of the recommendation.

### 3.3 Value at fixed lengths — uniform small traffic

Uniform `nblk` weighting over the eight small lengths (the convention of
§3.4 of the truncation doc; the r8g `base` total 201.74 ns reproduces the
published 201.71, and `t4p8` reproduces 22.0 %):

| host | `base`, 8 calls | `m4s4` | **`m4s4h`** | `s4` | **`s4h`** | `t4` | `t4p8` | `cw4` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| GV3 V1 | 231.46 ns | 11.9 % | **13.9 %** | 15.4 % | **16.3 %** | 20.7 % | **22.1 %** | 24.7 % |
| GV4 V2 | 201.81 ns | 14.3 % | **15.8 %** | 16.9 % | **18.1 %** | 20.8 % | **22.1 %** | 26.1 % |
| r8g V2 | 201.74 ns | 14.2 % | **15.8 %** | 16.9 % | **18.0 %** | 20.8 % | **22.0 %** | 26.1 % |
| GV5 V3 | 168.79 ns | 15.9 % | **17.1 %** | 18.0 % | **18.7 %** | 21.0 % | **22.0 %** | 26.6 % |

Two facts to keep: **`s4h` beats `m4s4h` on every core** (by 2.4/2.3/2.2/1.6
points) because the 128 B regression more than eats body 8's contribution; and
**`t4p8` beats `m4s4h` by 8.2/6.3/6.2/4.9 points at 2116 B more code**, while
`t4` beats `s4h` by 4.4/2.7/2.8/2.3 points at 1332 B more code.

---

## 4. The mechanism: achieved cycles, the floor, and the overlap question

Achieved cycles = min ns/call × the clock measured on that host at that moment.
The floor is the 4-slots/cycle ideal **for exactly `n` blocks of work**
(§1.4), which is why `base` — which always does 8 blocks of AES — shows large
ratios at small `n`; that is the design question, not an artefact.

### 4.1 Achieved cycles / ideal-work floor, per `nblk`

| `nblk` | floor | | `base` | **`m4s4h`** | `m4s4` | **`s4h`** | `t4p8` | `t4` | `cw4` |
|---:|---:|---|---|---|---|---|---|---|---|
| 1 | 12.50 | V1 | 67.7 / 5.42× | **35.8 / 2.87×** | 35.2 / 2.81× | 35.8 / 2.87× | 36.0 / 2.88× | 36.1 / 2.89× | 35.2 / 2.81× |
| | | V2 | 65.4 / 5.23× | **35.1 / 2.81×** | 35.0 / 2.80× | 35.0 / 2.80× | 34.2 / 2.73× | 34.4 / 2.75× | 34.9 / 2.79× |
| | | V3 | 64.5 / 5.16× | **34.8 / 2.79×** | 34.9 / 2.79× | 34.9 / 2.79× | 34.7 / 2.77× | 34.6 / 2.77× | 34.9 / 2.79× |
| 2 | 19.00 | V1 | 68.5 / 3.61× | **39.6 / 2.08×** | 39.6 / 2.08× | 39.6 / 2.09× | 38.5 / 2.02× | 38.4 / 2.02× | 37.9 / 2.00× |
| | | V2 | 65.3 / 3.44× | **37.0 / 1.95×** | 37.1 / 1.95× | 37.0 / 1.95× | 37.4 / 1.97× | 37.3 / 1.96× | 37.1 / 1.95× |
| | | V3 | 64.6 / 3.40× | **37.1 / 1.95×** | 37.2 / 1.96× | 37.1 / 1.95× | 37.2 / 1.96× | 37.2 / 1.96× | 38.0 / 2.00× |
| 3 | 25.50 | V1 | 71.1 / 2.79× | **48.9 / 1.92×** | 50.2 / 1.97× | 48.9 / 1.92× | 40.1 / 1.57× | 40.2 / 1.58× | 41.7 / 1.64× |
| | | V2 | 67.7 / 2.65× | **42.4 / 1.66×** | 45.2 / 1.77× | 42.4 / 1.66× | 38.3 / 1.50× | 38.2 / 1.50× | 39.3 / 1.54× |
| | | V3 | 67.0 / 2.63× | **40.4 / 1.58×** | 41.9 / 1.64× | 40.4 / 1.58× | 36.9 / 1.45× | 36.9 / 1.45× | 39.0 / 1.53× |
| 4 | 32.00 | V1 | 74.9 / 2.34× | **59.9 / 1.87×** | 65.3 / 2.04× | 59.9 / 1.87× | 44.0 / 1.37× | 43.9 / 1.37× | 47.4 / 1.48× |
| | | V2 | 70.1 / 2.19× | **51.9 / 1.62×** | 55.2 / 1.73× | 52.0 / 1.63× | 41.5 / 1.30× | 41.5 / 1.30× | 43.5 / 1.36× |
| | | V3 | 68.9 / 2.15× | **48.6 / 1.52×** | 51.2 / 1.60× | 48.6 / 1.52× | 40.0 / 1.25× | 40.0 / 1.25× | 42.6 / 1.33× |
| 8 | 58.00 | V1 | 77.9 / 1.34× | **94.2 / 1.62×** | 98.6 / 1.70× | *77.8 / 1.34×* | 70.4 / 1.21× | *77.2 / 1.33×* | 81.8 / 1.41× |
| | | V2 | 70.8 / 1.22× | **83.6 / 1.44×** | 86.2 / 1.49× | *71.5 / 1.23×* | 63.8 / 1.10× | *70.9 / 1.22×* | 76.2 / 1.31× |
| | | V3 | 70.6 / 1.22× | **79.9 / 1.38×** | 82.0 / 1.41× | *70.6 / 1.22×* | 64.5 / 1.11× | *70.6 / 1.22×* | 73.8 / 1.27× |

*Italic* = that variant falls back at `nblk = 8`, so the number is the
baseline's. `nblk = 5,6,7` (not shown) are the baseline's for every variant
except `cw4`, and agree with it to ≤ 0.5 %.

**Reading.** At `nblk = 1` and 2 every design is latency-bound and identical
(2.8× and 1.95×). From `nblk = 3` the shared sequential region **plateaus**
(1.92 → 1.87 on V1, 1.66 → 1.62 on V2, 1.58 → 1.52 on V3) while the
separate-body design **converges** (1.57 → 1.37, 1.50 → 1.30, 1.45 → 1.25) and
keeps converging to 1.10–1.21× at `nblk = 8`. This is exactly the plateau the
cascade experiment measured; the mixed-width structure inherits it for its
sequential half.

### 4.2 Do the four sequential blocks overlap in hardware? — the answer

Three independent readings, all on the same 4 blocks of work with the same slot
count:

| | V1 GV3 | V2 GV4/r8g | V3 GV5 |
|---|---:|---:|---:|
| 4 blocks, four **sequential** sections (`s4h`, `nblk = 4`) | 59.9 cyc | 52.0 cyc | 48.6 cyc |
| the same 4 blocks **interleaved 4-wide** (`cw4`'s `ss4`) | 47.4 cyc | 43.5 cyc | 42.6 cyc |
| the same 4 blocks as a **separate 4-block body** (`t4`) | 43.9 cyc | 41.5 cyc | 40.0 cyc |
| four **fully serialised** 14-round chains (≈ 28 cyc each) | ≈ 112 | ≈ 112 | ≈ 112 |
| ideal-work floor | 32.0 | 32.0 | 32.0 |

1. **They do overlap, and substantially.** 59.9 / 52.0 / 48.6 cycles for four
   chains that total ~112 cycles of dependence means roughly **1.9–2.3 blocks
   are resident on average** — the reorder machinery is doing real work across the
   section boundaries. Nothing here is serialised, and the marginal cost from
   `nblk = 1` to `nblk = 4` (8.03 / 5.61 / 4.58 cyc/block) is at or **below**
   the 6.50-cycle floor slope on the two newer cores, because the sections are
   absorbed into the first block's latency shadow.
2. **The overlap is incomplete.** Against the *same* work placed adjacently in
   program order the shared sequential region loses **12.5 cyc (+26 %) on V1,
   8.5 cyc (+20 %) on V2 and 6.0 cyc (+14 %) on V3**, and the achieved/floor
   ratio plateaus at 1.87/1.62/1.52× instead of reaching 1.37/1.30/1.25×.
3. **In the no-slack regime it is worse still.** At `nblk = 8` the four
   sequential sections run *after* the 4-wide group, with no latency slack left.
   Decomposing: the 4-wide group's marginal cost is
   **8.56 / 7.92 / 7.83 cyc/block** (V1/V2/V3, reproducing the published
   `W = 4` 8.01 on V2), and `m4s4h(8) − cw4(8)` = 12.4 / 7.4 / 6.1 cycles for
   the four blocks that are sequential rather than 4-wide, i.e.
   **+3.10 / +1.85 / +1.53 cyc/block**, so a sequential block there costs
   **≈ 11.7 / 9.8 / 9.4 cycles** — in line with the published hoisted `W = 1`
   figures of 10.80 / 9.32 / 8.52.

So: the 108 instructions of four one-block sections **are** inside the
out-of-order window in the trivial sense, and the window does recover most of
the *start-up* slack; what it does not recover is throughput. The binding
resource is the vector issue queue's occupancy being spent on one 26-µop chain
at a time, exactly as `fused-cascade-experiment.md` concluded, and no amount of
adjacency-free hardware reordering substitutes for putting independent work next
to each other in program order.

### 4.3 Region average at `nblk = 8`, against the prediction

Averaging the two halves at their measured marginal costs gives
**(8.56 + 11.66)/2 = 10.11 (V1), (7.92 + 9.77)/2 = 8.85 (V2),
(7.83 + 9.36)/2 = 8.60 (V3)** cycles per block for the 8-block path. The
prediction in the brief was **~8.67 cyc/block ≈ 1.33× floor**; the measured V2
and V3 numbers are 8.85 and 8.60, and the measured achieved/floor at `nblk = 8`
is 1.44× (V2) and 1.38× (V3). The arithmetic in the prediction was right; the
consequence — that `t8`/`t4p8`'s −10 % at 128 B is erased — is right too, and
the outcome is worse than "erased".

---

## 5. Mixed-workload measurement

`bench_mix2.c`, mixes **A–D** bit-identical to the sequences in
`_docs/fused-t4p8.md`, so the numbers are directly comparable with that report.

| mix | length distribution |
|---|---|
| **A** | `nblk` uniform 1..8 |
| **B** | `nblk` uniform 1..8, every 4th call `nblk = 64` (small + 1 KB records) |
| **C** | `nblk` uniform 1..16 (straddles the fused set *and* the `nblk>8` path) |
| **D** | `nblk` uniform {1,2} — isolates dispatch depth from footprint |
| **E** | `nblk` uniform 1..4 |
| **F** | 60 % `nblk = 8`, else uniform 1..4 — a 128 B-heavy stream |
| **R1/R2/R3/R4/R6** | only `nblk ∈ {5,8}`, 128 B : 80 B ratio 1/2/3/4/6 |

12 slots, 3 link orderings, 150 reps × 3 processes per ordering.

### 5.1 Δ % vs HEAD, median of 9 processes

| mix | core | **`m4s4h`** | `m4s4` | **`s4h`** | `s4` | `t4p8` | `t4` | `cw4` |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| **A** | V1 GV3 | **−6.47** | −3.43 | **−8.94** | −7.36 | −11.14 | −13.03 | −14.22 |
| | V2 GV4 | **−13.77** | −8.14 | **−14.44** | −11.15 | −14.67 | −15.65 | −19.75 |
| | V3 GV5 | **−11.95** | −9.35 | **−12.90** | −11.51 | −14.89 | −15.21 | −19.50 |
| **B** | V1 GV3 | **−2.26** | −1.35 | **−3.55** | −2.72 | −3.58 | −4.92 | −3.22 |
| | V2 GV4 | **−4.15** | −2.96 | **−4.96** | −4.18 | −4.42 | −4.98 | −4.76 |
| | V3 GV5 | **−3.79** | −2.90 | **−4.19** | −3.69 | −5.08 | −5.00 | −5.76 |
| **C** | V1 GV3 | **−3.96** | −3.11 | **−4.08** | −3.60 | −5.42 | −5.57 | −3.76 |
| | V2 GV4 | **−5.02** | −3.52 | **−5.37** | −4.50 | −5.88 | −5.59 | −2.51 |
| | V3 GV5 | **−6.19** | −4.58 | **−5.99** | −5.02 | −7.45 | −7.00 | −4.64 |
| **D** | V1 GV3 | −46.26 | −45.88 | −46.34 | −45.89 | −48.37 | −48.42 | −47.73 |
| | V2 GV4 | −46.03 | −45.92 | −46.02 | −45.92 | −46.14 | −46.21 | −45.91 |
| | V3 GV5 | −45.09 | −44.98 | −45.09 | −44.99 | −45.31 | −45.32 | −44.62 |
| **F** | V1 GV3 | **+0.23** | +7.44 | **−11.42** | −10.19 | −15.28 | −14.61 | −12.28 |
| | V2 GV4 | **−6.73** | −1.48 | **−15.55** | −13.95 | −22.54 | −17.52 | −14.16 |
| | V3 GV5 | **−5.68** | −2.24 | **−12.47** | −11.63 | −18.07 | −14.73 | −11.65 |
| **R1** (1:1 128 B:80 B) | V1 GV3 | **+8.86** | +13.73 | +0.22 | +0.24 | +1.23 | +1.07 | −5.65 |
| | V2 GV4 | **+5.16** | +8.84 | −0.83 | −0.73 | −4.70 | −0.61 | −11.28 |
| | V3 GV5 | **+7.99** | +11.32 | +0.34 | +0.37 | +0.92 | +0.16 | −9.52 |
| **R6** (6:1) | V1 GV3 | **+18.34** | +24.49 | +0.33 | +0.19 | −6.19 | −0.39 | +1.75 |
| | V2 GV4 | **+16.83** | +18.14 | −0.03 | +0.03 | −8.23 | +0.02 | +1.31 |
| | V3 GV5 | **+12.00** | +15.67 | +0.13 | +0.15 | −5.07 | +0.10 | +0.70 |

Placement floors for these mixes: A 0.33–5.22 %, B 0.15–0.93, C 0.53–1.06,
D 0.04–1.30, F 0.20–1.31, R 0.05–5.58. **Mix A on the V2 hosts is again
noise-limited** (`base` A/A 5.22 %), so mix A rests on the paired controls of
§5.2, not on this table. Mix D shows every variant within 0.3 points on V2/V3
(a 2.5-point spread on V1, against a 1.30 % floor there): neither the extra
dispatch test nor the larger mapped footprint costs anything on the newer cores.

### 5.2 Paired controls, both address ranks (placement cancels)

Two variants interleaved `X Y X Y` and again `Y X Y X`, 4-slot binaries, 2
processes each, so every number appears 8 times at two address ranks. Sign
agreement across both orderings is the acceptance criterion. Ranges below are
over all 8 readings of each ordering.

**`t4p8` vs `m4s4h` — the head-to-head** (+ve = `m4s4h` slower):

| core | mix A | mix B | mix C | mix D | mix F | R1 (1:1) | R3 (3:1) |
|---|---:|---:|---:|---:|---:|---:|---:|
| V1 GV3 | **+4.8…+7.1** | **+1.5…+1.9** | **+1.4…+2.1** | **+3.1…+3.5** | **+15.1…+18.1** | **+6.7…+7.8** | **+16.7…+22.2** |
| V2 GV4 | **+0.8…+7.4** | +0.0…+0.6 | **+0.4…+1.0** | **+0.2…+0.3** | **+16.4…+21.5** | **+9.3…+10.9** | **+15.7…+18.9** |
| V2 r8g | **+0.9…+7.0** | ±0.5 (tie) | **+0.3…+1.1** | **+0.2…+0.3** | **+16.4…+20.9** | **+9.4…+11.1** | **+15.8…+18.9** |
| V3 GV5 | **+3.1…+4.0** | **+1.2…+1.3** | **+0.8…+2.1** | **+0.4…+0.4** | **+13.1…+15.6** | **+6.5…+7.3** | **+11.9…+13.9** |

Sign-consistent in both orderings, on all four hosts, in every mix. **`t4p8`
dominates `mix4s4` in mixed traffic**, marginally in B/C/D and heavily wherever
128 B calls appear.

**`m4s4` vs `m4s4h` — what the round-key hoist is worth** (+ve = rotating keys
slower; every range below spans all 8 readings of both orderings):

| core | mix A | mix B | mix C | mix D | mix F | R1 | R3 |
|---|---:|---:|---:|---:|---:|---:|---:|
| V1 GV3 | **+1.6…+3.8** | **+0.4…+1.5** | −0.1…+1.0 | ±1.6 (tie) | **+4.1…+6.8** | **+3.9…+5.3** | **+4.8…+6.0** |
| V2 GV4 | **+0.9…+6.3** | **+1.1…+1.9** | **+0.6…+1.5** | **+0.1…+0.7** | **+4.4…+5.8** | **+3.2…+3.7** | **+3.9…+4.4** |
| V2 r8g | **+4.4…+6.2** | **+1.2…+1.7** | **+0.5…+1.6** | **+0.0…+0.4** | **+4.5…+5.6** | **+3.2…+3.6** | **+4.0…+4.3** |
| V3 GV5 | **+1.7…+2.8** | **+0.7…+1.1** | **+0.5…+1.5** | **+0.2…+0.3** | **+2.9…+3.6** | **+2.9…+3.3** | **+3.6…+3.8** |

Consistent in sign on every host and in every mix except mix C/D on V1:
hoisting is a genuine gain, and the hoisted variant is the one to judge the
structure by.

**`t4` vs `s4h` — the same comparison with `nblk = 8` dropped** (+ve = `s4h`
slower): V1 **+3.3…+5.1** (A), **+0.9…+1.9** (B), **+1.3…+2.0** (C),
**+3.4…+4.3** (D), **+3.0…+3.8** (F), ±1.2 (R1), unresolved at R3 (its V1 floor
is 2.53 %); V2 **+1.1…+2.1** (A), ±0.3 (B), **+0.4…+1.1** (C), +0.2 (D),
**+1.6…+2.7** (F), ±0.3 (R1/R3); V3 **+1.9…+2.8** (A), **+0.6…+0.8** (B),
**+0.6…+1.7** (C), **+0.4** (D), **+1.9…+2.7** (F), ±0.3 (R). So even without
body 8 the shared region costs 1–5 % against separate bodies in small-mixed
traffic — but **nothing at all** in 80/128 traffic, because both lengths fall
back.

**`m4s4h` vs `s4h` — is keeping `nblk = 8` fused worth anything?** (+ve =
keeping it is slower):

| core | mix A | mix B | mix C | mix D | mix F | R1 | R3 |
|---|---:|---:|---:|---:|---:|---:|---:|
| V1 GV3 | **+1.6…+2.6** | **+0.8…+1.0** | ±0.5 (tie) | ±0.7 (tie) | **+11.8…+13.2** | **+7.9…+9.1** | **+9.2…+14.3** |
| V2 GV4 | **+0.3…+0.9** | **+0.6…+1.1** | ±1.3 (tie) | ±0.03 (tie) | **+9.0…+10.5** | **+5.4…+6.1** | **+10.1…+11.2** |
| V2 r8g | ±0.7 (tie) | **+0.7…+0.9** | ±1.2 (tie) | ±0.05 (tie) | **+9.0…+10.5** | **+5.5…+6.1** | **+10.0…+11.2** |
| V3 GV5 | **+0.5…+1.0** | **+0.4…+0.9** | ±1.2 (tie) | ±0.03 (tie) | **+6.8…+7.0** | ~+6 | ~+11 |

**Keeping `nblk = 8` in the fused set is never better and is often much worse.**
This is the measured basis of the recommendation in §7.

---

## 6. Verdict on each of the four predictions

| prediction | verdict |
|---|---|
| **1. 16 B and 32 B match separate bodies** | **CONFIRMED.** `m4s4h` vs `t4p8`: 16 B −0.2/+1.4/+1.1/+0.2 points, 32 B +1.6/−0.7/−0.6/−0.2 points (V1/GV4/r8g/V3). No consistent sign, and at 16 B the V2 hosts' A/A floor is 4.9–7.8 %. Nothing to interleave at 1–2 blocks, as predicted. |
| **2. 48 B ≈ −33 %, losing ~10 points** | **DIRECTION CONFIRMED, MAGNITUDE ONLY RIGHT ON V1.** Measured `m4s4h` **−31.3 % (V1), −37.3 % (V2, both hosts), −39.7 % (V3)**; deficit vs `t4p8` **12.3 / 6.2 / 6.1 / 5.2 points**. The −33 % figure quoted in the brief is the *V1* pure-cascade number, and on V1 the prediction is almost exact (−31.3 vs −33, deficit 12.3 vs ~10). On V2 and V3 `mix4s4` does **better** than predicted: the newer cores recover more of the sequential region themselves. |
| **3. 64 B ≈ −21 %, losing ~20 points** | **DIRECTION CONFIRMED, AGAIN A V1 PREDICTION.** Measured **−20.0 % (V1) — exact — −25.9 % (V2), −29.5 % (V3)**; deficit **21.3 / 14.9 / 14.9 / 12.5 points** against the predicted ~20. Right on V1; `mix4s4` is 5–8 points better than predicted on V2/V3. |
| **4. 128 B: the −10.4 % gain is erased and probably becomes a regression** | **CONFIRMED, EMPHATICALLY.** Not merely erased: **+20.95 / +18.03 / +18.09 / +13.26 % vs HEAD** (+21.40/+17.97/+18.01/+13.22 against `dsp0`), a **24–31 point** swing away from `t4p8`'s −8.6…−9.9 %. The predicted mechanism is also confirmed numerically: the region averages 8.85 (V2) / 8.60 (V3) cyc/block against the predicted 8.67, at 1.44× / 1.38× the floor against the predicted 1.33×. |

The two magnitude misses both go the same way — the prediction quoted V1
pure-cascade numbers as if they were V2 — and both are in `mix4s4`'s favour.
Nothing measured here contradicts the direction of any of the four.

---

## 7. Recommendation on the body set

**`128 B REGRESSES BADLY: +13 % to +21 % vs HEAD on all four hosts, against the
−8.6…−9.9 % that separate bodies deliver.** It is the single largest number in
this report and it is far outside every noise floor (the `dsp0` control's own
128 B floor is 0.01–0.85 %).

**Yes — the right move is to drop `nblk = 8` from the fused set**, leaving
`{1,2,3,4}` fused and 5–8 falling back to the existing staggered path. That is
`s4h` in the tables, and it is a **strict** improvement over `mix4s4` as
specified:

* 128 B becomes **exactly a wash** (+0.24/+0.80/+0.79/+0.00 % against `dsp0`,
  inside the control's own floor).
* 16/32/48/64 B are **unchanged** (`m4s4h` − `s4h` = −0.03/−0.09/+0.01/−0.01
  points on V1, +0.17/−0.04/+0.03/−0.10 on V2, and ≤ 0.08 on V3): the four
  sequential sections are the same code, entered the same way.
* **More** uniform-small-traffic value: 16.3/18.1/18.0/18.7 % against
  13.9/15.8/15.8/17.1 %.
* Equal or better in **every** mix, paired and at both address ranks (§5.2),
  and 8–13 points better in 128 B-heavy traffic.
* **736 B smaller** (5980 vs 6716 B; ×1.204 vs ×1.352; rotating keys: 752 B,
  6076 vs 6828) and one fewer proof path, since the 4-wide group and its stub
  disappear entirely.

So it costs nothing and removes the only regression. But that is a
recommendation *within* this structure, and it should be read next to the
family:

| design | `.text` | × | paths | uniform-small value (V1/V2/V3) | 128 B |
|---|---:|---:|---:|---|---:|
| `t4p8` (separate bodies `{1,2,3,4,8}`) | 8832 | 1.78 | 5 | 22.1 / 22.1 / 22.0 % | **−9.6 / −9.9 / −8.6 %** |
| `t4` (separate bodies `{1,2,3,4}`) | 7312 | 1.47 | 4 | 20.7 / 20.8 / 21.0 % | wash |
| `cw4` (width-4 cascade, all of 1..8) | 9336 | 1.88 | 8 | 24.7 / 26.1 / 26.6 % | +5.1 / +7.6 / +4.6 % |
| **`mix4s4` = `m4s4h`** | **6716** | **1.35** | **5** | **13.9 / 15.8 / 17.1 %** | **+21.0 / +18.0 / +13.3 %** |
| **`mix4s4` minus `nblk = 8` = `s4h`** | **5980** | **1.20** | **4** | **16.3 / 18.1 / 18.7 %** | **wash** |

If code size is the binding constraint, `s4h` is a real point on the curve:
**×1.20 `.text` for 16–19 % of the uniform small-traffic value**, i.e. ~85 % of
`t4`'s value for 45 % of `t4`'s code growth. If code size is not the binding
constraint, **separate bodies win**: `t4` returns 2.3–4.4 more points at 1332 B
more code, and `t4p8` returns 4.9–8.2 more points and a real 128 B gain.

A caution on the proof side, which is not a performance claim but bears on the
"is the smaller code cheaper?" question. `mix4s4` has 5 entry labels and 5
straight-line paths, but its groups must be correct for **multiple entry
contexts** — `g1` for 5, `g2` for 4, `g3` for 3, `g4` for 2, `g8` for 1 = **15
(group, entry-context) pairs**, because the accumulator state at the top of a
group depends on which stub seeded it. That is a materially different and not
obviously cheaper obligation than `t4p8`'s 5 independent straight-line bodies,
and it is the same caveat the cascade experiment recorded.

---

## 8. What rests on one host, and other limits

* The **make-driven KAT** (real `arm/Makefile` + `arm/aes-gcm/kat/Makefile`,
  with the make-built object byte-compared to the harness object) ran **only on
  r8g**, because the GV hosts have no checkout of the tree. Every object is
  md5-identical on all four hosts, so this is a build-path check, not a
  microarchitectural one.
* **Mix A on the V2 hosts is noise-limited** (`base` A/A 5.2–5.5 %); its
  conclusions are carried by the V1/V3 tables and by the paired controls of
  §5.2, which agree in sign on all four hosts.
* **16 B on the V2 hosts** carries the documented placement lottery (`base` A/A
  4.9–7.8 %). Prediction 1 is therefore judged on V1 and V3, where the floors
  are 0.54 % and 0.03 %.
* The GHASH/MODULO split points were **not** re-swept; the published sweep was
  1.1–1.2 % flat and the cascade's shipped `ksec = 1.0, k1 = 0.35` was used.
  A 1 % scheduling gain would not touch any conclusion here.
* All numbers are single-thread and `taskset`-pinned, and say nothing about SMT
  or multi-tenant I-cache pressure — where a 2116 B code-size difference would,
  if anything, favour the smaller variant, i.e. `s4h`.
* `cw4` fuses `nblk = 5,6,7` as well, so it appears in these tables as a
  *reference* for the 4-wide mechanism, not as a candidate with the same entry
  set.

---

## 9. Artefacts

`_docs/fused-mix4s4/`

| file | what |
|---|---|
| `gen_mix.py` | the mixed-width generator: a group-width **list**; imports `gen_cascW.py`, `gen_cascWt.py`; self-checks md5-identical to `gen_cascW` `W=1` on widths `1×8`; `rotate`/`hoist` key modes; `zapN` / `zapALL` / `zsecP` probes |
| `verify_mx.py` | adjacency, per-region and per-`nblk` slot/`aese`/load accounting, register footprint |
| `provision_mx.sh` | builds `m4s4 m4s4h s4 s4h gc1 cw1 cw4 dsp0 t4 t4p8` + the generator self-check + `.text` table |
| `verify_mx.sh` | `.text`/frame, dispatch listing, normalised `objdump`, adjacency+slots, 256-length byte-compare, KAT relink |
| `probe_mx.sh` | the 46 liveness / mis-entry / fall-through-structure probes |
| `measure_mx.sh` | 12-slot per-length driver, 3 link orderings × 5 processes × 300 reps |
| `measure_mixmx.sh` | 12-slot mixed-length driver, mixes A–F + R1…R6 |
| `mixaa_mx.sh` | 4-slot placement floors and the paired both-rank comparisons |
| `analyze_mx.py`, `analyze_mixmx.py` | every table in §3–§5 |
| `runall_mx.sh`, `setup_gv_mx.sh` | per-host driver and fresh-host provisioning |
| `logs/` | every raw log from all four hosts (60 per-length + 36 mixed-length processes, controls, probes, verify, clocks) plus the generated analyses `an_*.txt`, `anmix_*.txt`, `anaa_*.txt` |

Reused unchanged from the earlier runs: `gen.py`, `gen_cascW.py`,
`gen_cascWt.py`, `gen_trunc.py`, `gen_set.py`, `bench12.c`, `bench_mix.c`,
`mkmix2.py`, `build_bench12.sh`, `mk.sh`, `kat.sh`, `makekat_t.sh`, `objcmp.py`,
`verify.py`, `clk.c`, and the `dsp0` control.
