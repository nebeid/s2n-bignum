# The code-size / performance trade curve for partial adoption of the fused small-message path — measurement only

Companion to `_docs/fused-small-path-experiment.md` (the eight-body version) and
`_docs/fused-cascade-experiment.md` (the shared cascade). Same kernel, same
harness, same discipline.

Kernel `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` at local HEAD, md5
`6de404aca78da9799a911b126727c73f`, **byte-identical to
`ec2r8g:~/whole-proofs/s2n-bignum/arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S`**;
`obj/base.o` md5 `114cedb51f36c584e50843d2838d871e`, the object `arm/Makefile`
produces in the synced tree. **No HOL Light, no `.ml`, no proofs, no gates.**
All work in `/tmp/fsp` and `/tmp/fst` on `ec2r8g` only; **no tracked file was
modified and no instance was started, stopped, rebooted or terminated.**
GV3/GV4/GV5 were left stopped, so **this is a single-core (Neoverse-V2 `0xd4f`,
clock measured on the spot at 2.7927 GHz) result** — a cross-core confirmation
on V1/V3 is still owed if a variant is selected.

---

## 0. Headline

| | |
|---|---|
| **Do the lengths ABOVE the cutoff regress?** | **NO — measurably not.** Against a `dsp0` control (the baseline plus the two dispatch instructions and *nothing else*), every truncation's above-cutoff lengths sit within **−0.04 … +0.08 %**. Against `base` itself they sit within **±0.2 %** at 48–112 B, and the **+0.8 % that appears at 128 B appears identically for two literal copies of the baseline object (+0.55 / +0.65 %)** — it is the known V2 128 B address-placement bias, not a dispatch cost. There is **no 1–2 % fall-through tax**; that risk is dead. |
| **Does truncation perturb the retained gains?** | **NO.** Each retained body is instruction-for-instruction the body the full variant ships (the C=8 object is **md5-identical** to `fused-small-path.patch`'s `tuned.o`), the dispatch tree is *shallower* for smaller `C`, and every retained length lands within **±0.4 percentage points** of the full version's own Δ, with no systematic sign. |
| **So is the curve monotone in `C`?** | **In fixed-length traffic, yes** — truncation costs exactly the lengths it drops and nothing else. The trade is therefore a clean "how many lengths do you want, at one proved path each". |
| **The finding that changes the calculus** | **In length-mixing traffic the curve has an interior optimum and `C = 8` is NOT the best point.** With a random `nblk` stream, full adoption is **1.4–2.6 % slower than `C = 6`/`C = 7`** and **1.5–5.0 % slower than `C = 5`/`C = 6`/`C = 7`** once ≥1 KB records are in the mix — reproduced in both address orders, against a 0.2–1.0 % placement floor. The 8th body is the only one that is a net *loss* in mixed traffic. |
| **Marginal value of the last path** | The 8th proved path buys **1.3 of the 34.0 points** of uniform-small-traffic value (the 7th buys 3.2, the 2nd buys 10.5), costs **1520 B of the 7408 B growth**, and is the body that hurts mixed traffic. |
| **Width-4 cascade hybrid (`nblk ≤ 7` + existing path at 8)** | Built and measured. **Dominated.** At `.text` 8592 B (×1.73) and **7** proved paths it is *bigger* and needs *two more* proofs than `C = 5` (8324 B, 5 paths) while being **worse at 48/64/80 B** (−41.9/−38.2/−25.0 vs −43.5/−40.9/−36.2) and no better in mixed traffic. It does succeed at what it was built for: the +7 % regression the full W=4 cascade had at 128 B becomes **+0.16 %** (a wash) once `nblk = 8` is left on the existing path. |
| **Correctness, all 9 variants** | KAT **35/35 / `KAT GATE: PASS`**, twice: via `kat.sh`'s relink and via the **real `arm/Makefile` + `arm/aes-gcm/kat/Makefile`** in a scratch copy — where the make-built object is **byte-identical** to the harness object for every variant. In-process byte-compare of `out`/`Xi`/`ivec`/return over **all 256 whole-block lengths** × 12 variants. **56/56 liveness and dispatch-boundary probes exact.** |
| **Frame** | **80 bytes in every variant**, `stp d8,d9,[sp,#-80]!` / `ldp d8,d9,[sp],#80`, and **zero** other `sp` adjustments in source or in `objdump`. |
| **`nblk > C` path** | **Instruction-for-instruction unchanged in every variant**: 2 instructions inserted at baseline instruction 14, then **1226 more identical**, and the `.L256_dec_ret` stub found verbatim, relocated. |
| **Recommendation** | **`C = 7`** if you want the whole curve minus its worst point: 7 proved paths, `.text` ×2.19, keeps **−47/−43/−44/−41/−36/−30/−24 %** at 16–112 B, gives up only the **−9.6 % at 128 B**, and is **strictly better than full adoption in every mixed workload measured**. **`C = 5`** if proof cost dominates: 5 paths, ×1.68, **74 %** of the uniform-small-traffic value, and the best or tied-best variant in the two mixes containing ≥1 KB records. **There is no knee that justifies `C = 2`/`C = 3`**, and **full adoption is not the top of the curve.** |

---

## 1. What was built

### 1.1 Family 1 — truncated eight-body (`t2 … t8`)

`_docs/fused-truncation/gen_trunc.py` **imports** `fused-small-path/gen.py` and
reuses its `body()` generator verbatim, with the shipped per-`n` schedule
`k = (0.45, 0.30, 0.45, 0.30, 0.45, 0.45, 0.45, 0.70)`. Only two things change:

```
	cmp	x9, #16*C				//[FUSE] nblk <= C ?
	b.le	.L256_dec_fused_small
```

and a balanced compare tree over `{1..C}` instead of `{1..8}`. `nblk > C`
therefore **never leaves the baseline path**: it runs the untouched
prologue → 8-way tail cascade → exact-8 drain, exactly as HEAD does.

Two properties make this a controlled experiment rather than a re-derivation:

* the tree recursion **reproduces `gen.py`'s hand-written dispatch exactly at
  `C = 8`** — `obj/t8.o` md5 `6578449791d0522b4fe474e2b0950302` is
  **identical to `obj/tuned.o`**, the object measured as variant C in
  `fused-small-path-experiment.md`. So `t8` *is* the full eight-body variant,
  and every `tC` is that variant with bodies removed and nothing else touched;
* per-body slot counts and free-register counts are unchanged
  (`verify.py` on `t4`: bodies 1–4 report **44 / 71 / 95 / 122** slots and
  14 / 11 / 9 / 8 free registers — the §2.3 table of the eight-body doc), and
  **0 `aese`/`aesmc` adjacency violations** in every variant.

The appended region sits at `.L256_dec_ret`, i.e. **after all baseline code**,
so the fall-through path's own layout is byte-for-byte HEAD's, shifted by 8 B.

`.text` growth is exactly the per-body cost the eight-body doc measured:

| C | new path added | bytes added | `.text` | ×base |
|---:|---|---:|---:|---:|
| 1 | — | — | 4968 | 1.00 |
| 2 | bodies 1,2 + tree | +832 | 5800 | 1.17 |
| 3 | body 3 | +672 | 6472 | 1.30 |
| 4 | body 4 | +840 | 7312 | 1.47 |
| 5 | body 5 | +1012 | 8324 | 1.68 |
| 6 | body 6 | +1184 | 9508 | 1.91 |
| 7 | body 7 | +1348 | 10856 | 2.19 |
| 8 | body 8 | +1520 | 12376 | 2.49 |

### 1.2 Family 2 — width-4 cascade hybrid (`cw4t`)

`gen_cascWt.py` imports `fused-cascade/gen_cascW.py` and emits the `W = 4`
cascade for `nblk ≤ 7` only: entry test `cmp x9,#112 / b.le`, a tree over
`{1..7}`, entry stubs 1–7, the four-block super-section `ss4`, the prefix bodies
`pb5`/`pb6`/`pb7` and the standalone bodies `sb1`/`sb2`/`sb3`. The
now-unreachable `ss8` and `stub_8` are dropped, so `nblk = 8` keeps the
baseline's dedicated exact-8 drain — the fix the cascade experiment identified as
mandatory (the full W=4 cascade was +7.0 % against HEAD at 128 B).
`.text` **8592 B (×1.73)**, 16 blocks of AES code (vs the full W=4 cascade's 20).

### 1.3 The pure-dispatch control (`dsp0`)

The single most useful variant in the experiment. Baseline plus

```
	cmp	x9, #0					//[FUSE] never taken (x9 >= 16)
	b.le	.L256_dec_ret
```

— the *same two instructions* every truncation puts on the fall-through path,
the same 8-byte shift of everything after them, and **no appended region at
all**. Normalised `objdump`: 2 inserted, then **1228 more baseline instructions
identical, nothing left over, nothing appended**; `.text` = **4976 B** = 4968 + 8.
KAT `PASS`. This separates "cost of the dispatch test" from "cost of the
appended code" without any inference.

---

## 2. Correctness evidence, per variant

| check | result |
|---|---|
| **Build fidelity** | For all 9 variants the object built by the **real `arm/Makefile` `%.o : %.S` rule** (in a scratch copy of `arm/` + `include/`, so no tracked file is touched) is **byte-identical** (`md5`) to the harness object. `obj/base.o` = `114cedb51f36c584e50843d2838d871e` = the tracked tree's object. |
| **KAT, make-driven** | `make aes-gcm/aesv8_gcm_8x_dec_256_wb.o` then `make -C aes-gcm/kat run`, with `kat_wb_dec` **deleted first** so a stale link cannot be tested: `35 passed, 0 failed … KAT GATE: PASS` for `base t2 t3 t4 t5 t6 t7 t8 cw4t`. `make clean` was never run in `arm/aes-gcm/kat`. |
| **KAT, harness relink** | `kat.sh` (`gcc -O2 -o kat/kat_wb_dec kat_wb_dec.c obj/<v>.o obj/ref.o`) — same 35/35 PASS for all 9 plus `dsp0`. |
| **In-process byte-compare** | 12 variants in one binary (`base baseAA baseAB dsp0 t2..t8 cw4t`), `out`/`Xi`/`ivec`/**return value** compared over **every whole-block length 1..256 blocks**, which includes each `nblk = 1..8` explicitly: `SELFCHECK OK (256 whole-block lengths 1..256 blk x 12 variants; out/Xi/ivec/ret byte-identical)`, **re-run at the start of all 30 timing processes**. Non-degeneracy (`out != in`) asserted at every length. |
| **Per-body liveness probes** | `zapN` (body `N`'s block-0 GHASH products zeroed) for every retained body of every cutoff — **35 probes, each failing at exactly `nblk = N` and nowhere else.** |
| **Dispatch-boundary probes** | `zapALL` (every retained body zeroed) for each cutoff — fails at **exactly `nblk = 1..C`** and **never at `C+1..8`**. This is the direct test that a truncation does not route `nblk = C+1` into a body that no longer exists or into the wrong one. 7/7 exact. |
| **`cw4t` probes** | 7 entry-stub probes (fail exactly `nblk = N`) + 7 section probes (`H^J` is used by every path with `nblk ≥ J`, so must fail exactly `nblk = J..7`). **14/14 exact** — and `sec-zap H^1` failing at `{1..7}` but **not 8** proves `nblk = 8` never enters the cascade. |
| **Adjacency** | `0 aese/aesmc violations` in all 9 variants. |
| **Frame** | 80 B in all 9: one `stp d8,d9,[sp,#-80]!`, `1 + C` matching `ldp d8,d9,[sp],#80` (baseline epilogue + one per fused body), and **0** `add/sub sp` anywhere in source or `objdump`. |
| **`nblk > C` content** | Normalised `objdump` (branch targets and addresses masked) for all 9: *2 instructions inserted at baseline instruction 14, then 1226 more baseline instructions identical, `.L256_dec_ret` stub found verbatim (relocated)* → **VERDICT: nblk>8 content UNCHANGED**. For `dsp0`: 1228 identical, nothing left over, nothing appended. |

**56 probes total, 56 exact. No collateral failure at any other length in any probe.**

---

## 3. The curve — fixed-length measurement

Discipline as established: every variant `objcopy --redefine-sym`'d to a
distinct symbol and linked into **one** binary (12 slots), round-robin with the
slot order rotated every rep, `taskset -c 3`, 200-call warm-up per pass,
best of 300 reps. **30 processes over 6 different link orderings** — every
variant has a different `.text` size, so the link order decides each kernel's
absolute address and the baseline's small-length timing is known to be
address-placement sensitive; permuting re-randomises placement. Two extra slots
(`baseAA`, `baseAB`) are the baseline object again: the **A/A floor, twice**.

### 3.1 Table 1 — the curve

Δ % vs HEAD, from absolute mins over the 30 processes (the estimator that
reproduces the published eight-body table: `t8` lands within 0.4 points of
`fused-small-path-experiment.md`'s r8g row at every length).

| variant | `.text` B | ×growth | new proved paths | 16 B | 32 B | 48 B | 64 B | 80 B | 96 B | 112 B | 128 B | 256 B | 4096 B |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| HEAD | 4968 | 1.00 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `dsp0` control | 4976 | 1.00 | 0 | +0.18 | −0.21 | −0.19 | −0.02 | +0.02 | −0.03 | −0.21 | +0.07 | −0.50 | −0.16 |
| **`t2`** (C=2) | 5800 | 1.17 | **2** | **−47.42** | **−42.92** | −0.20 | +0.02 | +0.05 | −0.06 | −0.14 | +0.06 | −0.28 | −0.25 |
| **`t3`** (C=3) | 6472 | 1.30 | **3** | **−47.27** | **−42.81** | **−43.49** | −0.03 | −0.04 | −0.20 | +0.03 | +0.07 | −0.63 | −0.21 |
| **`t4`** (C=4) | 7312 | 1.47 | **4** | **−47.25** | **−42.76** | **−43.50** | **−40.86** | +0.03 | −0.03 | −0.16 | +0.22 | −0.14 | −0.16 |
| **`t5`** (C=5) | 8324 | 1.68 | **5** | **−47.41** | **−43.30** | **−43.49** | **−40.91** | **−36.20** | +0.04 | −0.12 | +0.75 | −0.21 | −0.03 |
| **`t6`** (C=6) | 9508 | 1.91 | **6** | **−47.54** | **−43.15** | **−43.56** | **−40.89** | **−35.68** | **−30.42** | +0.12 | +0.08 | −0.17 | −0.06 |
| **`t7`** (C=7) | 10856 | 2.19 | **7** | **−47.28** | **−43.10** | **−43.51** | **−40.77** | **−35.94** | **−30.13** | **−24.13** | +0.08 | −0.30 | −0.22 |
| **`t8`** (C=8, full) | 12376 | 2.49 | **8** | **−47.22** | **−43.14** | **−43.63** | **−40.77** | **−35.98** | **−30.16** | **−24.05** | **−10.43** | −0.28 | −0.09 |
| **`cw4t`** (W=4, ≤7) | 8592 | 1.73 | **7** | **−46.20** | **−43.50** | **−41.91** | **−38.18** | **−25.00** | **−18.05** | **−9.78** | +0.16 | −0.20 | −0.05 |

Same table by the median-of-per-process-best-deltas convention, with the A/A
floor. (At 16 B the two conventions disagree — −47 % vs −51 % — because in most
of these 30 processes the baseline object landed at a *slow* address; the 16 B
A/A worst-process |Δ| is **7.76 %**, exactly the ±8 % floor the brief specifies.
Both conventions agree that all eight fused variants are equal at 16 B.)

| variant | 16 B | 32 B | 48 B | 64 B | 80 B | 96 B | 112 B | 128 B | 256 B | 4096 B |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| A/A floor (worst \|Δ\| any process) | 7.76 | 0.77 | 1.01 | 0.72 | 0.15 | 0.29 | 0.64 | 0.92 | 0.83 | 0.19 |
| `dsp0` | +0.30 | −0.17 | −0.19 | −0.03 | +0.02 | −0.03 | +0.13 | +0.78 | −0.24 | −0.05 |
| `t2` | −51.39 | −42.85 | −0.18 | −0.02 | +0.02 | −0.02 | +0.19 | +0.82 | −0.31 | −0.03 |
| `t3` | −51.33 | −42.76 | −43.42 | −0.06 | +0.01 | −0.01 | +0.12 | +0.79 | −0.29 | −0.03 |
| `t4` | −51.27 | −42.75 | −43.39 | −40.90 | +0.01 | +0.01 | +0.18 | +0.81 | −0.20 | −0.05 |
| `t5` | −51.32 | −43.11 | −43.39 | −40.94 | −36.20 | −0.00 | +0.15 | +0.85 | −0.18 | −0.04 |
| `t6` | −51.35 | −43.04 | −43.38 | −40.91 | −35.62 | −30.29 | +0.15 | +0.84 | −0.27 | −0.04 |
| `t7` | −51.25 | −42.90 | −43.53 | −40.81 | −35.95 | −30.21 | −24.15 | +0.81 | −0.21 | −0.03 |
| `t8` | −51.34 | −43.11 | −43.61 | −40.82 | −35.99 | −30.21 | −24.07 | −9.62 | −0.27 | −0.04 |
| `cw4t` | −50.44 | −43.16 | −41.82 | −38.20 | −25.01 | −18.12 | −9.77 | +0.82 | −0.20 | −0.04 |

**≥256 B is a wash for every variant**, as the byte-identical `nblk>8` path
requires: max |Δ| 0.63 %, every value at or inside its own length's A/A floor.

Absolute ns/call (min over 30 processes):

| bytes | base | baseAA | baseAB | dsp0 | t2 | t3 | t4 | t5 | t6 | t7 | t8 | cw4t |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 23.323 | 23.327 | 23.303 | 23.365 | 12.264 | 12.298 | 12.303 | 12.265 | 12.236 | 12.296 | 12.309 | 12.547 |
| 32 | 23.393 | 23.353 | 23.353 | 23.344 | 13.353 | 13.378 | 13.390 | 13.264 | 13.300 | 13.310 | 13.301 | 13.218 |
| 48 | 24.239 | 24.227 | 24.226 | 24.194 | 24.191 | 13.698 | 13.694 | 13.698 | 13.681 | 13.692 | 13.664 | 14.080 |
| 64 | 25.099 | 25.095 | 25.101 | 25.094 | 25.103 | 25.091 | 14.844 | 14.831 | 14.836 | 14.866 | 14.866 | 15.516 |
| 80 | 25.973 | 25.977 | 25.985 | 25.979 | 25.986 | 25.963 | 25.982 | 16.572 | 16.705 | 16.638 | 16.629 | 19.481 |
| 96 | 26.880 | 26.842 | 26.861 | 26.873 | 26.864 | 26.827 | 26.873 | 26.892 | 18.702 | 18.780 | 18.774 | 22.029 |
| 112 | 27.443 | 27.331 | 27.358 | 27.384 | 27.405 | 27.452 | 27.400 | 27.410 | 27.475 | 20.822 | 20.842 | 24.758 |
| 128 | 25.357 | 25.357 | 25.390 | 25.376 | 25.372 | 25.375 | 25.413 | 25.546 | 25.377 | 25.377 | 22.712 | 25.398 |
| 256 | 45.412 | 45.327 | 45.324 | 45.186 | 45.287 | 45.125 | 45.347 | 45.318 | 45.333 | 45.276 | 45.284 | 45.319 |
| 512 | 83.871 | 83.518 | 83.862 | 82.881 | 84.344 | 84.359 | 84.061 | 83.980 | 84.233 | 83.861 | 83.019 | 83.314 |
| 1024 | 161.611 | 161.561 | 161.272 | 161.506 | 161.340 | 161.476 | 161.135 | 161.681 | 160.792 | 161.439 | 161.405 | 160.373 |
| 4096 | 628.566 | 628.197 | 627.630 | 627.529 | 626.992 | 627.277 | 627.564 | 628.398 | 628.170 | 627.181 | 628.001 | 628.280 |

### 3.2 Question 1 — dispatch overhead on the lengths that fall through

**Answer: there is none that can be measured, and the structural reason is that
there is almost nothing to measure.**

The mechanism first. With entry test `cmp x9,#16C / b.le .L256_dec_fused_small`,
a length above the cutoff executes **one `cmp` and one not-taken `b.le`** and
then the untouched kernel — it is *the same two instructions the full eight-body
variant already pays for every `nblk > 8`*, and the eight-body experiment
measured those as a wash at 256 B–4 KB. The appended region is inserted at
`.L256_dec_ret`, i.e. after **all** baseline code, so the fall-through path never
crosses it and its layout is HEAD's, shifted by 8 B. Normalised `objdump`
confirms 1226 identical instructions in every variant.

Now the measurement. Above-cutoff cells only, median of 30 processes:

| variant | cutoff C | 48 B | 64 B | 80 B | 96 B | 112 B | 128 B |
|---|---:|---:|---:|---:|---:|---:|---:|
| A/A floor, median | — | −0.02 | −0.03 | +0.00 | −0.04 | −0.03 | **+0.55** |
| A/A floor, worst process | — | 1.01 | 0.72 | 0.15 | 0.29 | 0.64 | 0.92 |
| `dsp0` (the 2 instructions, nothing else) | 0 | −0.19 | −0.03 | +0.02 | −0.03 | +0.13 | **+0.78** |
| `t2` | 2 | −0.18 | −0.02 | +0.02 | −0.02 | +0.19 | +0.82 |
| `t3` | 3 | — | −0.06 | +0.01 | −0.01 | +0.12 | +0.79 |
| `t4` | 4 | — | — | +0.01 | +0.01 | +0.18 | +0.81 |
| `t5` | 5 | — | — | — | −0.00 | +0.15 | +0.85 |
| `t6` | 6 | — | — | — | — | +0.15 | +0.84 |
| `t7` | 7 | — | — | — | — | — | +0.81 |
| `cw4t` | 7 | — | — | — | — | — | +0.82 |

Two readings, and the second is the important one.

* At 48–112 B every above-cutoff cell is **|Δ| ≤ 0.19 %**, inside that length's
  A/A floor, and indistinguishable from the `dsp0` control. The 2-instruction
  dispatch test costs nothing resolvable — as expected, since it is ~0.25 cycles
  of a 68–77 cycle call.
* At 128 B **every** variant reads +0.78…+0.85 % — and so does **`baseAA`
  (+0.55 %) and `baseAB` (+0.65 %), which are the baseline object itself**.
  That is the documented systematic V2 128 B placement bias (`+0.80/+0.77 %` in
  the eight-body run, `+0.16 %` in the cascade run). Measured against `dsp0`
  instead of `base` — i.e. between two variants that both sit away from the
  first link slot — the column collapses:

| reference | base | baseAA | baseAB | dsp0 | t2 | t3 | t4 | t5 | t6 | t7 | cw4t |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **128 B vs `base`** | 0 | +0.55 | +0.65 | +0.78 | +0.82 | +0.79 | +0.81 | +0.85 | +0.84 | +0.81 | +0.82 |
| **128 B vs `dsp0`** | −0.78 | −0.27 | −0.12 | 0 | **+0.03** | **−0.02** | **−0.02** | **+0.07** | **+0.05** | **−0.04** | **+0.03** |
| **112 B vs `dsp0`** | −0.13 | −0.16 | −0.13 | 0 | **+0.08** | **−0.02** | **+0.02** | **+0.04** | **+0.07** | (fused) | (fused) |

Every one of those variants runs **byte-identical machine code** at 128 B, and
measured against a non-first-slot reference they agree to **±0.07 %**. The
+0.8 % is a property of where `base` was linked, not of any code change.

**Conclusion: a truncation costs its fall-through lengths nothing. Relative to
the A/A floor the residual is ≤ 0.2/0.9 = 0.2 floor-widths at 48–112 B and
0.08 % against a placement-matched reference at 128 B.** The specific risk the
brief flagged — "if a truncation costs 1–2 % on the sizes it does not
accelerate" — **does not occur**, and the worst single-process above-cutoff
reading anywhere in the grid is +1.12 % at 128 B where the A/A floor is 0.92 %.

### 3.3 Question 2 — does truncation perturb the retained gains?

**Answer: no, to within ±0.4 percentage points, with no systematic sign.**

Δ of `tC` minus Δ of `t8` at each retained length (percentage points; negative
means the truncation is the faster one):

| length | blk | t2 | t3 | t4 | t5 | t6 | t7 | t8 | cw4t |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 1 | −0.19 | −0.05 | −0.03 | −0.19 | −0.31 | −0.06 | 0 | +1.02 |
| 32 | 2 | +0.22 | +0.33 | +0.38 | −0.16 | −0.00 | +0.04 | 0 | −0.35 |
| 48 | 3 | — | +0.14 | +0.12 | +0.14 | +0.07 | +0.12 | 0 | +1.72 |
| 64 | 4 | — | — | −0.09 | −0.14 | −0.12 | +0.00 | 0 | +2.59 |
| 80 | 5 | — | — | — | −0.22 | +0.29 | +0.03 | 0 | +10.98 |
| 96 | 6 | — | — | — | — | −0.27 | +0.02 | 0 | +12.11 |
| 112 | 7 | — | — | — | — | — | −0.07 | 0 | +14.27 |

This is what the construction predicts and it is worth stating why it is not a
coincidence: the retained bodies are the *same instructions at the same offsets
from the region start* (the region is appended at the same anchor in every
variant), and the compare tree is **shallower** for smaller `C` — `t2` reaches
body 1 in 2 compares, `t8` in 4 — so if anything a truncation should be a hair
*faster*, which is roughly what the 16 B column shows. There is no drift.

The `cw4t` column is the family-2 shortfall carried over from the cascade
experiment, unchanged by truncation: level at 16/32 B, then +1.7/+2.6/+11/+12/+14
points behind the eight-body shape at 48–112 B.

### 3.4 Value per proved path

Summing over the eight small lengths with `nblk` weighted uniformly (base total
201.71 ns over the eight calls):

| C | `.text` | × | proved paths | ns saved | % of base | **marginal points per new path** |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 5800 | 1.17 | 2 | 21.17 | 10.5 | **+10.5** (for the first two) |
| 3 | 6472 | 1.30 | 3 | 31.62 | 15.7 | +5.2 |
| 4 | 7312 | 1.47 | 4 | 41.81 | 20.7 | +5.0 |
| 5 | 8324 | 1.68 | 5 | 51.23 | 25.4 | +4.7 |
| 6 | 9508 | 1.91 | 6 | 59.39 | 29.4 | +4.0 |
| 7 | 10856 | 2.19 | 7 | 65.93 | 32.7 | +3.2 |
| 8 | 12376 | 2.49 | 8 | 68.61 | 34.0 | **+1.3** |
| cw4t | 8592 | 1.73 | 7 | 54.68 | 27.1 | — |

**The 8th path is a clear outlier: it costs the largest single body (1520 B,
380 instructions) and one proof, and returns 1.3 points — 2.5× less than the
7th and 8× less than the 2nd.** That is the arithmetic reason `C = 7` is a knee
even before the mixed-traffic result below.

---

## 4. The mixed-length result — where the curve stops being monotone

The §3 benchmark calls **one length per pass**, so the dispatch tree is
perfectly predicted and the unexecuted fused bodies never compete for
instruction fetch. That flatters big variants. `bench_mix.c` drives a fixed
pseudorandom length sequence (identical for every variant, 4096 entries):

| mix | length distribution |
|---|---|
| **A** | `nblk` uniform in 1..8 (all-small traffic) |
| **B** | `nblk` uniform in 1..8, every 4th call `nblk = 64` (small + 1 KB records) |
| **C** | `nblk` uniform in 1..16 (straddles the cutoff *and* the `nblk>8` path) |
| **D** | `nblk` uniform in {1,2} — **every** variant with `C ≥ 2` handles both fused, and bodies 1 and 2 sit at identical offsets in every variant, so D isolates **dispatch-tree depth** from footprint |
| **E** | `nblk` uniform in 1..4 (same isolation for `C ≥ 4`); *unreliable — see below* |

Same 12 slots, same three link orderings, 100 reps × 6 processes.

### 4.1 The curve under mixed traffic

Δ % vs HEAD, median of 18 processes; absolute ns/call = min over 18.

| variant | `.text` × | **mix A** ns | Δ% | **mix B** ns | Δ% | **mix C** ns | Δ% |
|---|---:|---:|---:|---:|---:|---:|---:|
| base | 1.00 | 28.109 | 0 | 61.859 | 0 | 37.971 | 0 |
| baseAA | 1.00 | 28.137 | +0.08 | 61.757 | −0.11 | 37.977 | +0.21 |
| baseAB | 1.00 | 28.131 | +0.12 | 61.627 | −0.21 | 38.171 | +0.73 |
| `dsp0` | 1.00 | 28.195 | +1.51 | 61.768 | +0.05 | 38.083 | +0.39 |
| `t2` | 1.17 | 26.117 | −7.81 | 59.524 | −3.54 | 36.541 | −3.36 |
| `t3` | 1.30 | 24.497 | −13.48 | 58.646 | −5.03 | 36.024 | −5.08 |
| `t4` | 1.47 | 23.396 | −16.97 | 58.546 | −5.27 | 35.649 | −5.89 |
| `t5` | 1.68 | 21.539 | −20.40 | 58.357 | **−5.56** | 35.642 | **−6.07** |
| `t6` | 1.91 | 22.011 | −22.25 | 58.408 | −5.40 | 35.817 | −5.50 |
| **`t7`** | 2.19 | 21.621 | **−23.39** | 58.454 | −5.34 | 36.245 | −4.28 |
| **`t8`** (full) | 2.49 | 22.306 | **−21.06** | 59.360 | **−3.86** | 37.383 | **−1.36** |
| `cw4t` | 1.73 | 20.996 | −21.96 | 58.224 | −5.80 | 36.156 | −4.00 |

**`t8` is the worst fused variant in mixes B and C, and third-worst in mix A.**

### 4.2 Is that real? Two controls say yes

**Placement floor.** Four copies of the *same* object in four different link
slots (`mixaa.sh`), spread over the four:

| variant | mix A | mix B | mix C | mix D | mix E |
|---|---:|---:|---:|---:|---:|
| 4 × `base` | 0.43 % | 0.29 % | 1.04 % | 0.37 % | 0.33 % |
| 4 × `t8` | 0.31 % | 0.31 % | 0.62 % | 0.08 % | 0.49 % |
| 4 × `t5` | 1.38 % | 0.25 % | 0.95 % | 0.03 % | **4.24 %** |

Mix E is discarded: 4 identical copies of `t5` spread 4.2 %, so mix E cannot
resolve anything at this scale. Mixes A/B/C have a 0.3–1.4 % floor.

**Paired, both address ranks.** `tC` and `t8` interleaved as
`tC t8 tC t8` and again as `t8 tC t8 tC`, so each is measured at two different
address ranks in each binary and placement cancels (`t8` vs `tC`, %):

| pairing | mix A | mix B | mix C |
|---|---:|---:|---:|
| `t8` vs `t5`, order `t5 t8 t5 t8` | −0.21 / −0.83 | **+1.58 / +1.61** | **+4.74 / +5.04** |
| `t8` vs `t5`, order `t8 t5 t8 t5` | −1.80 / −1.63 | **+1.49 / +1.45** | **+4.27 / +4.22** |
| `t8` vs `t6`, both orders in one binary | **+1.84 / +1.42** | **+1.70 / +1.52** | **+4.04 / +4.12** |
| `t8` vs `t7`, both orders in one binary | **+2.63 / +2.54** | **+1.47 / +1.48** | **+2.57 / +2.69** |

Every sign is consistent across both orders and both processes, and the
magnitudes are 1.5–5× the placement floor. The one cell inside the floor is
`t8` vs `t5` in mix A (`t5`'s own mix-A floor is 1.38 %) — there the two are a
tie, which is itself notable: `t5` is ×1.68 with 5 proofs.

### 4.3 What the mechanism is — and is not

**Not the dispatch tree.** Mix D (`nblk` ∈ {1,2}, random) has every variant
executing the same two bodies at the same offsets, differing only in tree depth
(1 level for `t2`, 3 for `t8`) and in total mapped `.text` (5800 vs 12376 B):

| mix D | t2 | t3 | t4 | t5 | t6 | t7 | t8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Δ % vs base | −46.09 | −46.09 | −45.96 | −46.01 | −46.05 | −46.05 | −46.07 |

**All seven identical to within 0.13 points**, and every paired `t8`-vs-`tC`
comparison in mix D reads |Δ| ≤ 0.23 %. So neither the deeper compare tree nor
the larger *mapped* code costs anything. What costs is the amount of code
**actually touched** by the length stream.

That is visible directly as a "mixing tax" — measured mixed-workload ns/call
minus the length-weighted mean of the same variant's fixed-length ns/call:

| variant | fixed-length mean over `nblk` 1..8 | mix A measured | **mixing tax** |
|---|---:|---:|---:|
| base | 25.21 | 28.11 | **+2.90 ns** |
| `t5` | 18.79 | 21.54 | **+2.75 ns** |
| `t7` | 16.97 | 21.62 | **+4.65 ns** |
| `t8` | 16.64 | 22.31 | **+5.67 ns** |

and for one variant as the stream widens (`t8`: mix D 2 lengths → E 4 → A 8):
**+0.07 ns → +1.52 ns → +5.67 ns**. The tax grows with the number of distinct
fused bodies the stream visits, and by `C = 8` it has grown faster than the
steady-state gain, so the last body is a net loss in mixed traffic.

I did not pin the microarchitectural cause and am not claiming one; the
candidates consistent with mix D (not tree depth, not mapped size, scales with
touched size) are L1I/prefetch behaviour and BTB capacity for the newly-reached
body.

**Honest scope limit on §4.** This is a synthetic uniform-random length stream,
not the production AEAD path. The eight-body experiment established that the
AEAD wrapper costs 85–110 ns/call, which divides kernel-level percentages by
~4–6 at the API level; the 1.5–5 % differences here are 0.3–2 ns/call and would
be 0.3–2 % at the AEAD level at best. No aws-lc builds were made in this
experiment, so nothing here is an AEAD-level claim. What §4 *does* establish is
directional and it is enough for the decision: **the size axis is not free, and
the last body is where it stops paying.**

---

## 5. Family 2 verdict — the width-4 cascade hybrid is dominated

It works and it fixes the thing it was built to fix: leaving `nblk = 8` on the
existing path turns the full W=4 cascade's **+7.0 % regression at 128 B into
+0.16 %** (a wash, inside the A/A floor). But as a point on this curve:

| | `cw4t` | `t5` | `t6` |
|---|---:|---:|---:|
| `.text` | 8592 (×1.73) | **8324 (×1.68)** | 9508 (×1.91) |
| distinct straight-line paths to prove | 7 | **5** | 6 |
| distinct fused bodies / blocks of AES code | 7 / 16 | 5 / 15 | 6 / 21 |
| 48 B | −41.9 | **−43.5** | −43.6 |
| 64 B | −38.2 | **−40.9** | −40.9 |
| 80 B | −25.0 | **−36.2** | −35.7 |
| 96 B | −18.1 | +0.0 | **−30.4** |
| 112 B | −9.8 | −0.1 | +0.1 |
| mix A / B / C | −22.0 / −5.8 / −4.0 | −20.4 / −5.6 / −6.1 | −22.3 / −5.4 / −5.5 |

`cw4t` is **larger than `t5`, needs two more proved paths than `t5`, and is
worse than `t5` at 48/64/80 B**, buying only the weak −18.1/−9.8 % at 96/112 B
in exchange. Its mixed-traffic numbers are a tie with `t5`/`t6`. And its proof
story is worse than the path count suggests: the shared `ss4` super-section has
to be correct for four different entry contexts (different incoming accumulator
seeds and block indices), so 7 paths over 7 bodies is not cheaper than 5 paths
over 5 independent straight-line bodies.

**Family 2 offers no point on the curve that family 1 does not offer more
cheaply.** This is consistent with, and a sharper form of, the cascade
experiment's measured negative.

---

## 6. Recommendation

**Full adoption is not the top of the curve, and there is a real knee. But the
knee is high — `C = 7`, not `C = 3`.**

**Primary recommendation: `C = 7`.** Seven proved paths, `.text` 10856 B
(×2.19). It keeps **−47 / −43 / −44 / −41 / −36 / −30 / −24 %** at 16–112 B,
i.e. **97 % of the uniform-small-traffic value** of full adoption, and gives up
exactly one thing: the **−9.6 % at 128 B**. In exchange it is
**1.4–2.7 % faster than full adoption in every mixed workload measured**, it is
1520 B and 380 instructions smaller, and it is **one whole proof cheaper**. The
argument is that the 8th body is the worst body in the design on every axis at
once: smallest per-length gain by a factor of 2.5, largest single body, and the
only one that is a net negative under length mixing. Note also that `nblk = 8`
is the one length where the baseline is already *good* — its dedicated exact-8
drain runs at 1.26× its slot floor, versus 1.23–1.41× for the generic cascade —
which is precisely why the marginal gain there is small.

**If proof cost dominates: `C = 5`.** Five proved paths, `.text` 8324 B
(×1.68 — **the mid-point of the size axis for 74 % of the value**). Keeps
−47 / −43 / −44 / −41 / −36 % at 16–80 B. This is the aggressive knee, and it
has two independent things going for it beyond the size/proof arithmetic: it is
the **best or tied-best variant in both mixes containing ≥1 KB records**
(−5.6 % mix B, −6.1 % mix C, versus full adoption's −3.9 / −1.4 %), and 16–64 B
is the band that matters most for the production argument — it is where our
HEAD kernel is currently *slower* than the fallback aws-lc already ships, which
is the concrete justification for the `len >= 256` gate. `C = 5` removes that
embarrassment completely.

**Do not choose `C = 2` or `C = 3`.** The first two paths are the cheapest
value on the curve (10.5 points for 832 B), but stopping there leaves 84 % of
the achievable gain and, in mixed traffic, only −7.8 %. The dispatch machinery,
the frame argument, the `nblk>8`-unchanged argument and the harness are the same
work at any `C`, so the fixed cost of doing this at all is already paid.

**What the evidence does *not* support:** it does not support "full adoption or
nothing". Truncation is free on the lengths it drops (§3.2) and lossless on the
lengths it keeps (§3.3), so every cutoff is a legitimate, independently
shippable point, and the marginal proof at each step has a measured price tag
(§3.4). Equally, it does not support a dramatic knee: the value per path decays
smoothly from 10.5 → 5.2 → 5.0 → 4.7 → 4.0 → 3.2 points and then falls off a
cliff to 1.3 at the last step. **The one unambiguous conclusion is that the
8th body should not be built: it is dominated on size, on proof cost, and on
mixed-traffic throughput, and it buys the smallest per-length win in the
design.** Everything below that is a straightforward budget decision about how
many `WBN_MAIN_LOOP`-class proofs are affordable.

**Before shipping any of these:** re-run §3 and §4 on Neoverse-V1 and V3. Every
number here is Neoverse-V2. The eight-body experiment found V1/V3 within ~1.5
points of V2 on the per-length axis, so §3 is very likely to transfer; §4 is a
fetch/prediction effect and is the one that could differ materially by core.

---

## 7. Artifacts

All under `_docs/fused-truncation/` (gitignored). Live scratch in `/tmp/fsp`
(variants, objects, logs) and `/tmp/fst` (the `make`-driven KAT tree copy) on
`ec2r8g`.

| file | contents |
|---|---|
| `gen_trunc.py` | family-1 generator; **imports** `fused-small-path/gen.py` and reuses its bodies verbatim. `C = 0` emits the `dsp0` pure-dispatch control. `zapN` / `zap all` probes. |
| `gen_cascWt.py` | family-2 generator; **imports** `fused-cascade/gen_cascW.py`, adds a `MAXN` cutoff, drops unreachable super-sections, stub/section probes. |
| `provision_t.sh` | generate + assemble `t2..t8`, `cw4t`; asserts `t8.o` md5 = the full variant's `tuned.o` and prints `.text` sizes |
| `verify_t.sh` | `.text` + 80-byte-frame check, normalised `objdump` of the fall-through path, adjacency, 12-variant byte-compare over all 256 lengths, per-variant KAT relink |
| `makekat_t.sh` | KAT through the **real** `arm/Makefile` and `arm/aes-gcm/kat/Makefile` in a scratch tree copy; asserts the make-built object equals the harness object |
| `probe_t.sh` | 35 body-liveness probes + 7 `zapALL` dispatch-boundary probes + 14 `cw4t` stub/section probes |
| `bench12.c`, `build_bench12.sh` | `fused-small-path/bench.c` widened from 8 to 12 slots; everything else unchanged |
| `measure_t.sh`, `measure_t2.sh` | the fixed-length run, 3 link orderings each, 2 A/A slots |
| `bench_mix.c`, `measure_mix.sh`, `mixctl.sh`, `mixaa.sh` | the mixed-length workload (5 mixes), 4-slot controls, and the four-identical-copies placement-floor controls |
| `t2.patch … t8.patch`, `cw4t.patch`, `dsp0.patch` | the measured variants as diffs against the pristine `.S`. **`t8.patch` is line-for-line identical to `fused-small-path/fused-small-path.patch` apart from three dispatch label names, and its object is md5-identical** — the cross-check that the truncation family is that variant with bodies removed and nothing else. |
| `analyze_t.py`, `report_t.py` | table generation |
| `logs/verify_t.txt`, `logs/probe_t.txt`, `logs/makekat_t.txt` | the §2 evidence verbatim (sizes/frame/objdump/adjacency/byte-compare/KAT; 56 probes; make-driven KAT with object-identity assertion) |
| `logs/tables.txt`, `logs/analysis.txt` | generated §3 tables |
| `logs/trunc_r8g.log`, `logs/trunc_r8gB.log`, `logs/trunc_r8g_all.log` | fixed-length, 30 processes over 6 link orderings |
| `logs/mix_r8g.log`, `logs/mixctl_r8g.log`, `logs/mixctl2_r8g.log`, `logs/mixaa_r8g.log` | mixed-length runs and controls |
