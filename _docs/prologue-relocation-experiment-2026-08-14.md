# Relocating the final group's `T`-independent GHASH into the prologue — measurement-only

Follow-on to `_docs/destagger-experiment-2026-08-14.md` and
`_docs/prepretail-fusion-experiment-2026-08-14.md` (§6 "exact next step").
Kernel `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` at HEAD `14f9d9bb`
(md5 `6de404aca78da9799a911b126727c73f`; verified byte-identical to
`ec2r8g:~/whole-proofs/s2n-bignum/arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S`).
No HOL Light, no `.ml`, no proofs. All work in `/tmp/prel` scratch on each host
plus `/tmp/prel` locally; **no tracked file in any repo was modified** (the
Unison-synced tree was only ever *read*, to prove build-pipeline fidelity).

Hosts, clocks measured on the spot (`clk.c`, dependent-add chain):

| label | core | clock |
|---|---|---|
| GV3 | Neoverse-V1 `0xd40` | 2.5911 GHz |
| GV4 | Neoverse-V2 `0xd4f` | 2.7918 GHz |
| GV5 | Neoverse-V3 `0xd84` | 3.2905 GHz |
| r8g | Neoverse-V2 (dev) | 2.7934 GHz |

---

## 0. Headline

| | |
|---|---|
| Built, KAT 35/35 | **`p1_ilv`** — 7/8 of the exact-8 drain's GHASH relocated into the prologue, interleaved one chunk per AES round, 3 unreduced accumulators spilled to a **grown frame (80 → 128 B)** |
| Verdict `p1_ilv` | **REAL but small WIN at 128 B: −3.5 … −3.9 % (≈ −0.8 … −1.0 ns). WASH-to-marginal at 256 B – 4 KB: −0.4 … −1.4 % at 256 B, ≈ 0 at 1 KB/4 KB.** Cascade sizes unaffected (+0.01 … +0.04 %) |
| Did the ≈ −1.7 ns/call prediction hold? | **No — measured ≈ −0.2 … −0.5 ns at ≥ 256 B, i.e. 3–8× smaller.** The prior report's 0.192–0.212 cyc/op "prologue price" was measured with *independent, register-only* dummy ops. The **real** relocated work is load-fed and internally dependent; its measured prologue price is **0.225 (V3) / 0.234 (V2) / 0.312 (V1) cyc/op**, against a drain-removal price of **0.238 / 0.229 / 0.265**. On V1 the arbitrage is *inverted*; on V2/V3 it is ≈ 0.01–0.013 cyc/op |
| Frame growth avoidable? | **Not without losing more than the win.** The zero-frame-growth variant (`p2_ilv`: pre-reduce to one 128-bit value, stash it in the dead `Xi` buffer) was built and is **KAT 35/35 but a REGRESSION: +1.8 … +4.2 % at 256 B** |
| Guard | `tst x9, #127` — *not* placed after `.S:371`. **The brief's premise that the exact-8 drain only runs for `nblk > 8` is wrong**: it also serves `nblk == 8`. Placing the precompute after `:371` broke the 128 B case on the first build |
| Combined with experiment A | expA + `p1_ilv`: **−9.3 % (V2) / −8.6 % (V3) / −8.7 % (V1) at 128 B** (= expA alone; expA's dedicated `nblk==8` path bypasses the relocation) and **−0.5 % (V2) / −1.4 % (V3) / −0.7 % (V1) at 256 B** (≈ expA + relocation, additive) |
| Guard cost on the 7/8 of sizes that take the cascade | **Zero, measured.** 7 taken forward branches at 144/240/272 B cost +0.01 … +0.04 % on V2/V3 |

---

## 1. What was built

### 1.1 The relocation

The exact-8 drain computes
`T_out = reduce((T ⊕ C₀)·H⁸ ⊕ C₁·H⁷ ⊕ … ⊕ C₇·H¹)`.
Only the first term needs the incoming accumulator `T` (fed in at `.S:1537`
`eor v8,v8,v16`). Blocks 1–7 — **21 of the drain's 24 `pmull`, 57 of its 73 SIMD
ALU slots** — are `T`-independent and were moved into the prologue:

* per block: `ldr` ciphertext, `ldr` the `{hXl|hXh}` pair and the k-pair,
  `rev64`, `ext`, `eor`, `pmull2` (high), `pmull` (low), `pmull` (mid)
  = **6 SIMD ALU ops**, instruction-for-instruction the same sequence the drain
  used, with the same `Htable` offsets (H⁷ at `+144/+160`, H⁶ at `+128/+112`ʰⁱ,
  H⁵ at `+96/+112`ˡᵒ, H⁴ at `+80/+64`ʰⁱ, H³ at `+48/+64`ˡᵒ, H² at `+32/+16`ʰⁱ,
  H¹ at `+0/+16`ˡᵒ).
  Where the k value sits in the *high* lane, `eor v11.16b` + `pmull2` replaces
  the drain's `ext`-the-key + `pmull`, saving the 3 key `ext`s.
* accumulation into 3 lanes as a 3-level `eor3` tree over phases {1,2,3},{4,5},{6,7}
  = **9 `eor3`** (register peak 14 of the 17 SIMD registers dead in the prologue).
* **51 SIMD ALU ops + 18 loads** added to the prologue;
  **57 removed** from the drain, **3 `eor`** added there to fold the reloaded
  partials into block 0's products. Net slot change ≈ 0 by construction.

The drain's blocks 1–7 keep only `ldr` ciphertext / `eor3` keystream / `st1`
plaintext. Its SIMD ALU count falls **73 → 19**.

### 1.2 The guard — and the bug in the brief

The brief said to insert after `.S:371 b.ge .L256_dec_tail` because "code past
that branch executes only when `nblk > 8`". That is true, but the *drain* does
**not**: `.L256_dec_exact8_drain` is reached from `.L256_dec_tail`, which
`:371` **branches to for `nblk == 8`**. The first build did exactly what the
brief said and the in-process differential self-check caught it immediately:

```
SELFCHECK FAIL nblk=8 variant p1: out=0 xi=1 ivec=0
```

— the drain ran with an uninitialised spill slot. The relocation is valid for
`nblk == 8` too (there the "last group" *is* the only group), so the correct
guard is simply

```
	tst	x9, #127		// byte_len % 128 == 0  <=>  the exact-8 drain will run
	b.ne	.L256_dec_rel_k		// (once per interleaved chunk)
```

with **no `nblk > 8` term at all**, placed **before** the `b.ge` at `:371`.
`x9` is `byte_len`; `byte_len % 128 == 0` is exactly the condition for the
tail to have 128 bytes left (`x5 = x4 - x0 > 112`), i.e. for the exact-8 drain,
because `x5_main = x0 + 128·⌊(L−1)/128⌋`.

Two further constraints, both enforced mechanically in the generator:

* **NZCV lifetime.** `aese`/`aesmc`/`ldr`/`ldp` and the prologue's
  `and x5, x5, #…` (AND-immediate, not ANDS) do **not** write NZCV, so **one
  `tst` serves all seven interleaved chunks**. But the prologue's own
  `cmp x0, x5` (`.S:348`, feeding the `b.ge`) does — so every chunk anchor must
  precede it. `gen.py` asserts this; the first stride-2 spread violated it and
  was rejected.
* **Address of the last group.** `x15` (dead since `mov v31.d[1], x15` at
  `.S:62`) is loaded with `x0 + x9 − 128` — no new GPR, and `x0` is never
  disturbed.

### 1.3 Placement matters more than anything else

Measured at 256 B on r8g (Δ vs `base` in the same binary):

| placement of the 51-op block | Δ @128 B | Δ @256 B |
|---|---:|---:|
| after `:371` (contiguous, "end", + flag restore) | +4.31 % | +2.16 % |
| after `.S:279` (contiguous, mid-AES) | +0.41 % | +2.09 % |
| after the CTR setup (contiguous, "front") | −1.87 % | +0.05 % |
| **interleaved, 1 chunk per AES round 0…6 (`ilv`)** | **−4.08 %** | **−0.45 %** |
| interleaved, chunks spread over rounds 0…11 (`ilv2`) | −2.36 % | −0.32 % |

Front-loaded interleaving wins, exactly as in experiment A (K=80 plateau).
A contiguous block anywhere is a wash or a regression.

### 1.4 Variants built (all KAT 35/35 unless stated)

| name | what |
|---|---|
| `p1_front` | contiguous guarded block at the front, 3 accumulators → `[sp,#80..127]`, **frame 80→128** |
| **`p1_ilv`** | **the winner**: same, interleaved as 7 chunks over AES rounds 0–6 |
| `p1_mid`, `p1_end`, `p1_ilv2` | placement sweep |
| `p2_front`, `p2_ilv` | pre-reduced partial in `[x3]`, **frame unchanged at 80** |
| `expA_p1_ilv`, `expA_p2_ilv` | the above on top of `_docs/expA-fused8-K80.patch` |
| `p1z_ilv`, `p1z_front` | **liveness probes** — relocated products forced to zero (functionally wrong on purpose); also isolates the drain-side saving |
| `p1k_ilv`, `p1k_ilv2`, `p1k_front` | prologue block added, **drain left intact** — isolates the prologue-side cost; functionally correct, KAT 35/35 |

---

## 2. Correctness evidence

1. **Build-pipeline fidelity.** `mk.sh` reproduces `arm/Makefile`'s rule
   (`gcc -E -I include -xassembler-with-cpp | tr ';' '\n' | as`) and its output
   for the pristine source is **byte-identical** to the object produced by
   running the Makefile's own pipeline on the synced tree
   (`md5 114cedb51f36c584e50843d2838d871e`). Every variant is a full
   `.S` → `.o` → **fresh link** (`gcc -O2 -o kat/kat_wb_dec kat_wb_dec.c
   obj/<v>.o obj/ref.o`; `objcopy --redefine-sym` + fresh `gcc` link for the
   benchmark). The tracked `arm/aes-gcm/kat` tree was never touched and
   `make clean` was never run anywhere.
2. **In-process differential self-check, run before every timing pass**:
   22 sizes — 8, **9, 10, 11, 12, 13, 14, 15**, 16, **17**, **23**, 24, **31**,
   32, **33**, 40, 48, 64, 128, 200, **255**, 256 blocks — comparing `out`,
   `Xi`, `ivec` **and the return value** of all 7 linked variants byte-for-byte.
   `SELFCHECK OK` in every process on every host.
3. **KAT gate**: `base`, `p1_front`, `p1_ilv`, `p2_front`, `p2_ilv`,
   `expA_p1_ilv`, `expA_p2_ilv` → **35 passed, 0 failed, KAT GATE: PASS**.
4. **Liveness / guard-exactness probe** (better than `brk #0`): `p1z_ilv`
   zeroes the relocated products, so the relocated work is provably load-bearing
   iff the KAT breaks on exactly the drain's sizes:
   ```
   nblk = 8,16,24,32,40,48,64,128,200,256  FAIL: Xi differs
   === SUMMARY: 25 passed, 10 failed ===
   ```
   Exactly the ten `nblk % 8 == 0` cases fail and **all 25 others pass** — i.e.
   the relocated code executes on every exact-8-drain call and the guard
   excludes every cascade call.
5. **The cascade is byte-identical.** Normalised `objdump` instruction streams:
   `base[160..1144] == p1_ilv[241..1225]`, i.e. **everything from AES round 7
   through the `ret` — the rest of the prologue, the whole main loop, the
   prepretail, the tail dispatch, the 8-way cascade and the shared epilogue —
   is instruction-for-instruction unchanged.** The only diff hunks are the
   frame `stp`/`ldp`, the 8 prologue insertion points and the drain body.
6. **The cascade is unaffected in time too** (§3.3): 144 / 240 / 272 B move by
   +0.01 … +0.04 % on GV4/GV5/r8g.

---

## 3. Measurements

Discipline: all 7 variants `objcopy --redefine-sym`'d into **one** binary,
measured round-robin with the order rotated every rep, `taskset -c 3`,
200-call warm-up per pass, best-of-150 reps × 3 processes. Absolute figures are
min over the 3 processes; **Δ % are the median of the per-process best-deltas**
(min-of-mins across processes is misleading — see the prior report). Slot 1 is
`base` again: the **A/A noise floor**.

### 3.1 Absolute ns/call (min of 3 processes × 150 reps)

**GV3 — Neoverse-V1, 2.5911 GHz**

| size | base | A/A | p1_front | **p1_ilv** | p2_ilv | expA | expA+p1_ilv |
|---|---:|---:|---:|---:|---:|---:|---:|
| 128 B | 30.113 | 30.032 | 29.969 | **28.963** | 30.423 | 27.312 | 27.523 |
| 256 B | 52.309 | 52.250 | 52.715 | **52.143** | 54.262 | 52.163 | 51.192 |
| 512 B | 94.919 | 95.069 | 95.220 | **94.772** | 96.949 | 94.378 | 94.765 |
| 1024 B | 179.306 | 180.344 | 179.641 | 179.694 | 182.065 | 179.742 | 179.303 |
| 4096 B | 693.630 | 694.023 | 690.192 | 691.138 | 695.646 | 692.253 | 689.549 |

**GV4 — Neoverse-V2, 2.7918 GHz**

| size | base | A/A | p1_front | **p1_ilv** | p2_ilv | expA | expA+p1_ilv |
|---|---:|---:|---:|---:|---:|---:|---:|
| 128 B | 25.372 | 25.536 | 25.044 | **24.482** | 25.406 | 23.021 | 23.002 |
| 256 B | 45.454 | 45.348 | 45.625 | **45.233** | 46.204 | 45.317 | 45.299 |
| 512 B | 84.305 | 84.378 | 84.398 | **83.825** | 85.008 | 84.476 | 84.090 |
| 1024 B | 161.636 | 161.481 | 161.599 | **160.702** | 162.747 | 162.005 | 161.669 |
| 4096 B | 627.758 | 628.225 | 628.479 | 628.124 | 629.365 | 628.588 | 628.339 |

**GV5 — Neoverse-V3, 3.2905 GHz** (A/A floor ±0.02 % — the quiet host)

| size | base | A/A | p1_front | **p1_ilv** | p2_ilv | expA | expA+p1_ilv |
|---|---:|---:|---:|---:|---:|---:|---:|
| 128 B | 21.462 | 21.457 | 20.817 | **20.623** | 21.617 | 19.636 | 19.620 |
| 256 B | 38.179 | 38.177 | 38.196 | **37.654** | 39.011 | 38.179 | 37.650 |
| 512 B | 70.825 | 71.122 | 71.480 | 71.030 | 72.538 | 71.141 | 70.812 |
| 1024 B | 138.501 | 138.501 | 138.857 | 138.528 | 140.262 | 138.500 | 138.496 |
| 4096 B | 546.886 | 546.892 | 547.227 | 547.103 | 548.667 | 546.902 | 546.897 |

**r8g — Neoverse-V2, 2.7934 GHz**

| size | base | A/A | p1_front | **p1_ilv** | p2_ilv | expA | expA+p1_ilv |
|---|---:|---:|---:|---:|---:|---:|---:|
| 128 B | 25.372 | 25.536 | 25.043 | **24.481** | 25.410 | 23.024 | 23.004 |
| 256 B | 45.427 | 45.352 | 45.448 | **45.170** | 46.314 | 45.303 | 45.283 |
| 512 B | 84.098 | 84.417 | 84.426 | **83.766** | 85.108 | 84.471 | 84.157 |
| 1024 B | 161.832 | 160.870 | 161.782 | **161.288** | 162.506 | 162.006 | 161.562 |
| 4096 B | 628.098 | 628.751 | 628.646 | 628.331 | 629.492 | 628.443 | 628.003 |

### 3.2 Δ % (median of per-process best-deltas) and the A/A floor

| size | host | **A/A floor** | p1_front | **p1_ilv** | p2_ilv | expA | expA+p1_ilv |
|---|---|---:|---:|---:|---:|---:|---:|
| **128 B** | GV3 | +0.04 | −0.45 | **−3.79** | +1.02 | −9.29 | −8.73 |
| | GV4 | +0.82 | −1.29 | **−3.50** | +0.14 | −9.28 | −9.33 |
| | GV5 | +0.01 | −3.00 | **−3.90** | +0.72 | −8.49 | −8.58 |
| | r8g | +0.43 | −1.65 | **−3.84** | −0.20 | −9.57 | −9.44 |
| **256 B** | GV3 | +0.21 | +1.37 | **−0.42** | +4.22 | −0.26 | −0.66 |
| | GV4 | −0.15 | +0.45 | **−0.43** | +2.00 | −0.26 | −0.50 |
| | GV5 | +0.02 | +0.04 | **−1.39** | +2.19 | +0.01 | −1.37 |
| | r8g | −0.23 | +0.16 | **−0.41** | +2.04 | −0.21 | −0.26 |
| **512 B** | GV3 | +0.06 | +0.29 | −0.33 | +2.19 | −0.42 | −0.17 |
| | GV4 | +0.23 | +0.07 | −0.45 | +1.20 | +0.31 | −0.09 |
| | GV5 | −0.01 | +0.54 | −0.05 | +1.99 | +0.03 | −0.18 |
| | r8g | +0.06 | −0.04 | −0.46 | +1.20 | −0.01 | −0.19 |
| **1024 B** | GV3 | +0.62 | +0.30 | +0.08 | +1.40 | +0.01 | +0.07 |
| | GV4 | +0.05 | +0.10 | −0.21 | +0.54 | +0.12 | −0.16 |
| | GV5 | −0.01 | +0.27 | +0.07 | +1.26 | +0.01 | −0.01 |
| | r8g | −0.26 | +0.08 | −0.16 | +0.45 | +0.14 | −0.15 |
| **4096 B** | GV3 | +0.11 | −0.46 | −0.31 | +0.48 | −0.30 | −0.51 |
| | GV4 | +0.10 | +0.10 | +0.01 | +0.23 | +0.08 | +0.04 |
| | GV5 | +0.01 | +0.08 | +0.05 | +0.34 | +0.01 | +0.01 |
| | r8g | +0.11 | +0.10 | +0.01 | +0.23 | +0.10 | +0.05 |

### 3.3 Cascade sizes — does the guard cost anything? (no)

Δ %, median of 2 processes × 120 reps. `nblk % 8 ≠ 0` ⇒ the 8-way cascade runs
and the relocation is skipped by 7 taken forward branches.

| size | nblk | host | p1_ilv | p2_ilv |
|---|---:|---|---:|---:|
| 144 B | 9 | GV4 / GV5 / r8g / GV3 | +0.02 / +0.01 / +0.01 / −0.46 | +0.56 / +0.67 / +0.54 / +0.34 |
| 240 B | 15 | GV4 / GV5 / r8g / GV3 | +0.04 / +0.10 / +0.04 / −0.98 | +0.30 / +0.81 / +0.31 / +0.79 |
| 272 B | 17 | GV4 / GV5 / r8g / GV3 | −0.27 / +0.01 / −0.01 / −0.87 | −0.02 / +0.29 / +0.29 / +0.46 |

**`p1_ilv` costs the cascade nothing** — the seven taken skip branches are free
(GV3's negative numbers are inside its noisy floor). `p2_ilv` costs the cascade
+0.3 … +0.8 %, from the extra unconditional `eor` in the shared epilogue.

### 3.4 Why it is small — the cost decomposition (the key result)

Two probes isolate the two halves of the transaction, both real relinks,
256 B, median of 2 processes:

| probe | what it does | GV3 | GV4 | GV5 |
|---|---|---:|---:|---:|
| `p1z_ilv` | **drain-side saving alone** (57 GHASH ops removed, relocated products forced to 0; KAT 25/10 by design) | −10.6 % = **−5.52 ns** | −9.7 % = **−4.41 ns** | −10.2 % = **−3.90 ns** |
| `p1k_ilv` | **prologue-side cost alone** (51-op block interleaved, drain intact; KAT 35/35) | +12.0 % = **+6.25 ns** | +9.4 % = **+4.27 ns** | +9.1 % = **+3.48 ns** |
| `p1k_front` | prologue-side cost, contiguous block | +12.0 % = **+6.25 ns** | +10.7 % = **+4.86 ns** | +10.5 % = **+4.02 ns** |

Per-op marginal prices for the **real** relocated op mix:

| | GV3 (V1) | GV4 (V2) | GV5 (V3) |
|---|---:|---:|---:|
| removal from the drain (54 net ops) | **0.265 cyc/op** | **0.229** | **0.238** |
| addition to the prologue, contiguous (51 ops) | 0.310 | 0.266 | 0.259 |
| addition to the prologue, **interleaved** (51 ops) | **0.318** | **0.234** | **0.225** |
| *(prior report, dummy independent register-only ops)* | *0.212* | *0.192* | *0.202* |

**This is the whole story.** The design rests on buying prologue slots at
0.192–0.212 cyc and selling drain slots at 0.264 cyc. Neither price is what the
real work pays:

* The **prologue price is 0.225–0.318, not 0.192–0.212**, because the real work
  is (a) *load-fed* — 18 extra `ldr`s whose results feed a
  `rev64 → ext → eor → pmull` chain — and (b) *internally dependent*, whereas
  `mixpr`'s 65 injected ops were independent and register-only. On **V1 the
  interleaved price (0.318) exceeds the drain price (0.265)**: the arbitrage is
  inverted there, and indeed `p1_front` *regresses* +1.37 % at 256 B on GV3.
* The **drain price is 0.229–0.265, not 0.264 everywhere**, because probe A
  (`drain0`) also deleted block 0's `(T⊕C₀)·H⁸` chain and thereby shortened the
  critical path into the MODULO reduce. Removing only the seven *independent*
  blocks — which is all the algebra permits — is worth less per op.

Note the two halves are **not additive**: 4.41 − 4.27 = +0.14 ns predicted for
GV4 versus −0.20 ns measured end-to-end, and on GV3 the parts predict +0.73 ns
while the composite measures −0.22 ns. `p1k` keeps *both* the prologue block and
the full drain, so it exposes a longer drain critical path than either endpoint;
the direct A/B of the real variant is the number to trust.

Why 128 B does better (−3.5 … −3.9 % ≈ −0.9 ns) than 256 B (−0.4 … −1.4 %
≈ −0.2 … −0.5 ns): at 128 B there is no main loop and no prepretail, so the
prologue's AES chain *is* the call and has the most exposed latency for the
relocated ops to hide in (the destagger report measured the 128 B call at 79 %
of its slot floor). From 256 B up, the block competes with saturated code.

---

## 4. The stack-frame question

### 4.1 The frame grows 80 → **128**, not 80 → 112

The brief assumed 16 spare bytes at `[sp,#64..79]`. Only **8** are spare:
`stp x5, xzr, [sp,#64]` puts the `0xc200000000000000` MODULO constant at
`[sp,#64..71]` and `x10 = sp+64` is dereferenced later by
`ldr d16, [x10]`; only `[sp,#72..79]` (the `xzr` half) is dead. Three 128-bit
accumulators need 48 bytes, so the frame must go **80 → 128**
(`stp d8,d9,[sp,#-128]!` / `ldp d8,d9,[sp],#128`, spills at
`[sp,#80]`, `[sp,#96]`, `[sp,#112]`). For the expA-combined variants expA's own
fused-path epilogue pop is widened to `#128` as well.

### 4.2 Was it avoidable? Yes technically — but every route costs more than the win

| route | storage | extra cost | outcome |
|---|---|---|---|
| **pre-reduce to ONE 128-bit value, stash in the dead `Xi` buffer `[x3]`** (`p2_ilv`) | 16 B, **frame unchanged at 80, no new register, no new MAYCHANGE footprint** — `Xi` is already written by the function | +10 prologue ops (the Barrett fold, which is GF(2)-linear, so `reduce(A⊕B) = reduce(A)⊕reduce(B)` and the drain may XOR the pre-reduced partial in after its own reduce), +1 `eor` in the **shared** epilogue, +1 `stp xzr,xzr,[x3]` to make that fold a no-op on all other paths | **BUILT, KAT 35/35, REGRESSION: +2.0 % (V2) / +2.2 % (V3) / +4.2 % (V1) at 256 B, +0.2 … +0.5 % at 4 KB, +0.3 … +0.8 % on cascade sizes** |
| spill to GPRs | 48 B; `x7, x8, x12, x13, x14, x17` are **completely unused** by the kernel, so 6 pairs are free with zero frame growth | 6 `UMOV` + 6 `INS` ≈ 12 extra SIMD-port ops ≈ **+0.9 ns** | not built — arithmetic is conclusive, it exceeds the entire win |
| hybrid (`Xi` + 4 GPRs) | 48 B, frame unchanged | 8 moves ≈ +0.6 ns | not built, same reason |
| partial reduce to 2 values | 32 B (still > `Xi`'s 16 + 8 spare stack bytes) | +6 prologue ops, +2 drain `eor` | needs frame 80→96 anyway |
| drop the stack MODULO constant (`movz x?, #0xc200, lsl #48` + `fmov`) | frees 16 B | 1 extra op per use | changes the exported statement *anyway* (frame shrinks, the stores disappear) |

**Answer: no, there is no version that wins without growing the frame.** The
16-byte-storage form is the only one that is truly free of frame growth and
register-footprint change, and it is a measured regression: its 10-op prologue
reduce plus 1 epilogue `eor` cost more than the 2 drain `eor`s it saves, at the
0.23 cyc/op prices measured in §3.4.

---

## 5. Verdicts

| variant | verdict |
|---|---|
| **`p1_ilv`** (interleaved, frame 80→128) | **REAL WIN at 128 B: −3.79 % (V1), −3.50 % (V2), −3.90 % (V3), −3.84 % (r8g) — ≈ −0.8 … −1.0 ns, well outside every A/A floor.** **WASH-to-marginal-win at 256 B – 4 KB**: −0.41 … −1.39 % at 256 B (only GV5's −1.39 % is unambiguous, its floor being ±0.02 %), −0.05 … −0.46 % at 512 B, ≈ 0 at 1 KB and 4 KB. Cascade sizes unchanged. KAT 35/35 |
| `p1_front` (contiguous) | **WASH / REGRESSION**: +1.37 % (V1), +0.45 % (V2), +0.04 % (V3) at 256 B; only −0.45 … −3.00 % at 128 B. The brief's literal design (a single guarded block) does not pay |
| `p2_ilv` (no frame growth) | **REGRESSION: +2.00 % (V2), +2.19 % (V3), +4.22 % (V1) at 256 B**, +0.23 … +0.48 % at 4 KB, +0.3 … +0.8 % on cascade sizes. KAT 35/35 — correct, just slower |
| `expA` (reference) | reproduces again: −9.28 % (V2), −9.29 % (V1), −8.49 % (V3) at 128 B |
| **`expA` + `p1_ilv`** | **−9.33 % (V2), −8.73 % (V1), −8.58 % (V3) at 128 B** (identical to expA alone: expA's dedicated `nblk==8` path is taken and bypasses the relocation) **and −0.50 % (V2), −0.66 % (V1), −1.37 % (V3) at 256 B** — the two contributions stack additively above 128 B. This is the combination that would ship |
| Does the gain match ≈ −1.7 ns/call? | **No. Measured ≈ −0.9 ns at 128 B and −0.2 … −0.5 ns at ≥ 256 B — 3–8× smaller.** Cause measured, not argued: §3.4. Nothing here is larger than predicted, so no over-claim needs explaining away |

### Recommendation

**Do not take this to proof.** `p1_ilv` buys ≈ −0.2 … −0.5 ns at ≥ 256 B
(≤ 1 % at 256 B, ≈ 0 % at 4 KB) in exchange for: a **grown stack frame
(80 → 128)** that changes the exported theorem's precondition and `MAYCHANGE`;
a rewritten exact-8 drain; and 81 new prologue instructions on the
`byte_len % 128 == 0` path, spread across seven guarded chunks inside the AES
rounds — a proof band with a fresh NZCV-lifetime side condition
(`tst` … 7 × `b.ne` … `cmp x0, x5`). Its one solid win, 128 B, is already
claimed 2.5× more effectively by experiment A, whose `nblk == 8` path bypasses
this code entirely.

The remaining headroom is small and known: switching the mid-lane computation
to the main loop's `trn1`/`trn2` pairing would shave 3 of the 51 prologue ops
(≈ −0.24 ns), roughly doubling the ≥ 256 B win to ≈ −0.5 … −0.7 ns without
changing the verdict. **On V1 no amount of tuning helps** — its interleaved
prologue price (0.318 cyc/op) is *above* its drain price (0.265), so the
transaction is intrinsically loss-making on Neoverse-V1.

### Correction to carry forward

`_docs/prepretail-fusion-experiment-2026-08-14.md`'s marginal-price table
(prologue 0.192–0.212 cyc/op) is **valid only for independent, register-only
ops**. Real relocated GHASH — load-fed, internally dependent — pays
**0.225 (V3) / 0.234 (V2) / 0.318 (V1) cyc/op** interleaved and
**0.259 / 0.266 / 0.310** as a contiguous block. Any future "move work into the
prologue" proposal should be priced with the *actual* op mix, using the
`p1k_*` / `p1z_*` probe pattern (add-only and remove-only halves, each a real
relink), before any code is written.

---

## 6. Artifacts

All under `_docs/prologue-relocation/` (gitignored path):

| file | contents |
|---|---|
| `gen.py` | the generator: builds every variant from the pristine `.S` by anchor matching (no line numbers), emits `eor3` as verified `.inst` words, and asserts the guard's NZCV-lifetime constraint |
| `p1_ilv.patch` | **the winner** (vs pristine `.S`) |
| `p1_front.patch`, `p1_mid.patch`, `p1_end.patch`, `p1_ilv2.patch` | placement sweep |
| `p2_ilv.patch`, `p2_front.patch` | the no-frame-growth (pre-reduced → `Xi`) variants |
| `expA_p1_ilv.patch`, `expA_p2_ilv.patch` | combined, vs pristine `.S` |
| `expA_p1_ilv_vs_expA.patch`, `expA_p2_ilv_vs_expA.patch` | combined, vs `expA`-patched `.S` (the incremental delta) |
| `p1z_ilv.patch`, `p1z_front.patch` | liveness / drain-side probes (KAT 25/10 by design) |
| `p1k_ilv.patch`, `p1k_front.patch` | prologue-side cost probes (KAT 35/35) |
| `bench.c` | 7-slot single-binary interleaved harness: 22-size differential self-check (`out`/`Xi`/`ivec`/return value) then order-rotated best-of-N timing |
| `mk.sh` | `.S` → `.o`, byte-identical to `arm/Makefile`'s rule |
| `kat.sh`, `build_bench.sh`, `run.sh`, `clk.c` | KAT relink, benchmark relink, driver, clock measurement |
| `logs/log_{GV3,GV4,GV5,r8g}.txt` | main 5-size runs, 3 processes × 150 reps |
| `logs/dec_{GV3,GV4,GV5}.txt` | cost-decomposition probe runs |
| `logs/casc_{GV3,GV4,GV5,r8g}.txt` | 8-size runs including the cascade sizes 144 / 240 / 272 B |

Live scratch copies remain in `/tmp/prel` on all four hosts and locally.
No instance was stopped, started, rebooted or terminated.
