# Fusing the GHASH drain into the PREPRETAIL — measurement-only experiment

Follow-on to `_docs/destagger-experiment-2026-08-14.md` ("exact next step" §8).
Kernel `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` at HEAD `464049b0` (verified
byte-identical at the current local HEAD `14f9d9bb`; md5 `6de404ac…`).
No HOL Light, no `.ml`, no proofs. All work in `/tmp/pfx` scratch on each host;
no git repo on any host was modified, and `ec2r8g:~/whole-proofs/s2n-bignum`
was never referenced by any command (its `.S` md5 `6de404ac…` equals HEAD's).

Hosts, clocks measured on the spot with a dependent-add chain (`clk.c`, best of 5):

| label | instance | core | clock |
|---|---|---|---|
| GV3 | c7g.2xlarge | Neoverse-V1 `0xd40` | **2.5913 GHz** |
| GV4 | c8g.4xlarge | Neoverse-V2 `0xd4f` | **2.7916 GHz** |
| GV5 | c9g.4xlarge | Neoverse-V3 `0xd84` | **3.2902 GHz** |
| r8g | (dev host, prior experiment) | Neoverse-V2 | **2.7929 GHz** |

---

## 0. Headline

| | |
|---|---|
| Step 1 static check | prepretail+tail at 256 B is at **75–81 %** of its issue-slot floor — *static* headroom exists (≈ 25 cyc), so the cheap static stop-rule did **not** fire |
| Step 1 register check | **prepretail has 1–7 free SIMD registers through its middle and ZERO registers dead across the whole region** (prologue has 17). A disjoint AES/GHASH partition à la experiment A is impossible there |
| Step 1 *dynamic* check (new, decisive) | The 25 cyc of headroom is **not in the prepretail and not in the drain** — both are at ~100 % of their marginal issue cost. It is all in the **prologue** |
| **Verdict on prepretail fusion** | **WASH → small REGRESSION. Measured, not modelled: −0.4 … −1.0 % at 256 B for a perfect free relocation, +0.9 … +1.7 % on V2/V3 once the algebraically required `T·H⁸` correction terms are counted.** Full hand-scheduled version **not built** — the measured ceiling does not justify it |
| Experiment A cross-core | **REPRODUCED: −9.30 % (V1), −9.86 % (V2), −8.59 % (V3), −9.87 % (r8g) at 128 B.** Shrinks mildly across generations; no regression at any other size |
| Projected −5.7 % at 256 B | **Did NOT materialise for the prepretail. It DOES materialise (partly) if the destination is the PROLOGUE: −2.8 … −5.4 % measured by emulation** |

---

## 1. Step 1 — feasibility

### 1a. Slot count vs measured cycles

Slot counting redone independently (`_docs/prepretail-probes/analyze.py`), adjacent
`aese`+`aesmc` = 1 slot, `.inst`-encoded `eor3` counted, loads/stores excluded
(they do not consume SIMD issue slots — established by experiment C):

| region | pairs | lone `aese` | `pmull` | other vec ALU | **slots** | floor @4/cyc |
|---|---:|---:|---:|---:|---:|---:|
| prologue (52–371) | 104 | 8 | 0 | 26 | **138** | 34.50 |
| main loop body (415–832) | 104 | 7 | 26 | 67 | **204** | 51.00 |
| **prepretail (834–1214)** | 104 | 7 | 26 | 45 | **182** | 45.50 |
| tail entry (1215–1230) | 0 | 0 | 0 | 3 | **3** | 0.75 |
| tail cascade (1294–1489) | 0 | 0 | 24 | 72 | **96** | 24.00 |
| **exact-8 drain (1521–1716)** | 0 | 0 | 24 | 49 | **73** | 18.25 |
| epilogue (1490–1518) | 0 | 0 | 2 | 10 | **12** | 3.00 |

(Reproduces the prior report's 138 / 205 / 183 / 73 to within ±1 slot.)

Whole-call floors and **measured** cycles (min over 3 processes × 200 reps):

| size | path slots | floor (cyc) | GV3 cyc | GV4 cyc | GV5 cyc | r8g cyc | % of floor (GV4) |
|---|---:|---:|---:|---:|---:|---:|---:|
| 128 B (8 blk) | 226 | 56.50 | 78.03 | 71.22 | 70.62 | 71.28 | 79.3 % |
| **256 B (16 blk)** | **408** | **102.00** | **135.58** | **126.79** | **125.61** | **126.83** | **80.5 %** |
| 512 B | 816 | 204.00 | 244.71 | 235.03 | 233.98 | 235.62 | 86.8 % |
| 1024 B | 1632 | 408.00 | 465.90 | 451.63 | 455.79 | 452.10 | 90.3 % |
| 4096 B | 6528 | 1632.00 | 1798.29 | 1755.42 | 1799.35 | 1755.72 | 93.0 % |

**Answer to Step 1's first question: prepretail+tail at 256 B is at 80.5 % of the
slot floor (75.2 % on V1, 81.2 % on V3), not ~95 %.** The static stop-rule did not
fire — 24.8 cyc (8.9 ns) sits above the floor at 256 B. So I continued.

### 1b. Free registers in the prepretail

Full backward SIMD liveness over lines 834–1214, with live-out taken as the union
of what the tail entry, the exact-8 drain and the 8-way cascade read before
writing (`analyze.py`; live-out = `{v0-v7, v19, v28, v30}`, live-in =
`{v0-v4, v8-v15, v19, v30, v31}`):

```
free-count histogram over the 382 program points:
  1 free: 4 pts   2: 19   3: 48   4: 27   5: 61   6: 29   7: 32   8: 15
  9: 24  10: 20  11: 7   12: 1   13: 5  14: 23  15: 8  16: 28  17: 26
 19: 1   20: 3   21: 1
min free = 1        max free = 21
registers dead across the ENTIRE prepretail:  NONE (empty set)
```

* Through the GHASH-heavy middle (source lines ≈ 900–1130) only **2–7** registers
  are dead at any point.
* Only the last ~80 lines (from L1134, after the last raw-ciphertext `pmull`) open
  up to 14–21 free.
* **Zero registers are dead across the whole region**, versus **17** in the
  prologue (`v8`–`v18`, `v20`–`v25`; only `v19` is live there).

So the experiment-A recipe — a disjoint register partition AES ∥ GHASH with no
spills — **cannot be replicated in the prepretail**. At best a *partial* fusion of
the last 3–4 blocks is register-feasible, and a full one needs stack spills for
the group-1 accumulators.

That is the first blocker. The second one is worse.

---

## 2. Step 1c — the dynamic check that actually decides it

Static slot counts say where the *floor* is; they do not say which region owns the
24.8 cyc of slack. Three cheap probe families answer that directly. Every probe is
a real `.S` → `.o` → **relinked** binary, measured in the same interleaved harness.

### Probe A — how much does the drain's GHASH actually cost?

`drain0`: delete all 65 GHASH SIMD-ALU ops from `.L256_dec_exact8_drain`
(keeping the 8 plaintext `eor3`, all loads/stores, the counter store and the
`ldr d16` modulo constant). Functionally wrong on purpose.

Liveness proof that the edit is on a live path: **KAT 25 passed / 10 failed —
failing on exactly the ten `nblk % 8 == 0` cases (8, 16, 24, 32, 40, 48, 64, 128,
200, 256) and passing all 25 others.** That is a sharper liveness probe than
`brk #0` and it also confirms the drain serves exactly the multiples of 8.

| size | GV3 Δ | GV4 Δ | GV5 Δ | r8g Δ |
|---|---:|---:|---:|---:|
| 128 B | −7.51 ns (−24.9 %) | −5.97 ns (−23.4 %) | −4.79 ns (−22.3 %) | −6.00 ns (−23.5 %) |
| 256 B | −7.40 ns (−14.1 %) | −6.15 ns (−13.5 %) | −4.54 ns (−11.9 %) | −5.99 ns (−13.2 %) |
| 512 B | −7.49 ns (−7.9 %) | −6.07 ns (−7.2 %) | −3.53 ns (−5.0 %) | −6.00 ns (−7.1 %) |
| 1024 B | −8.86 ns (−4.9 %) | −6.05 ns (−3.7 %) | −3.06 ns (−2.2 %) | −6.19 ns (−3.8 %) |
| 4096 B | −6.76 ns (−1.0 %) | −5.72 ns (−0.9 %) | −3.12 ns (−0.6 %) | −4.59 ns (−0.7 %) |

**A size-independent ≈ 6 ns (GV4/r8g) / 4.5 ns (GV5) / 7.4 ns (GV3).** That is the
absolute ceiling for making the drain's GHASH free, i.e. the whole prize.

Per relocated op: 6.15 ns / 65 = **0.0946 ns = 0.264 cyc/op** on GV4. The drain's
73 slots / 4 = 18.25 cyc floor and removing 65 of them recovers 17.2 cyc — **the
drain is at ~100 % of its issue floor. It has no latency slack to reclaim.**

### Probe B — what does it cost to put that work into the prepretail?

`mixpp`: inject the drain's *exact op mix* (24 `pmull` + 41 vector `eor`) into the
prepretail at 65 sites chosen by the liveness analysis, never splitting an
`aese`/`aesmc` pair, destinations restricted to registers proved dead at that
point. The drain is left intact, so the variant is **functionally correct**:
**KAT 35/35 PASS** on GV4 and GV5. `mixpr` is the same injection into the
prologue's AES region (also **KAT 35/35 PASS**).

Built-in locality proof: `mixpp` costs **+0.00 %** at 128 B (prepretail is not
executed there) and **+13.2 %** at 256 B. `mixpr` costs +18.3 % at 128 B (the
prologue always runs) and +10.3 % at 256 B.

Marginal cost of one added independent SIMD op, at 256 B:

| host | **into the drain** (removal, probe A) | **into the prepretail** (`mixpp`) | **into the prologue** (`mixpr`) |
|---|---:|---:|---:|
| GV3 | 0.295 cyc | 0.259 cyc | **0.212 cyc** |
| GV4 | 0.264 cyc | 0.260 cyc | **0.192 cyc** |
| GV5 | 0.230 cyc | 0.254 cyc | **0.202 cyc** |
| r8g | 0.258 cyc | 0.265 cyc | **0.202 cyc** |

**This is the result that kills the experiment.** The prepretail's marginal cost
per SIMD op is *the same as the drain's* (≈ 0.26 cyc, i.e. essentially the pure
issue price given that `pmull` itself only sustains 3.47/cyc). Moving work from
the drain to the prepretail is a **1:1 exchange** — zero-sum by construction.
The prologue is ~25 % cheaper per op, and it is the only region with real slack.

Pure-`pmull` sweeps confirm the prepretail's slack is ≈ 0 and that it is linear
(so there is no small free budget either). GV5, 256 B, `ppload<K>`:

| K | 4 | 8 | 16 | 32 | 48 | 72 | 96 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Δ ns | +0.334 | +0.518 | +1.078 | +2.229 | +3.418 | +5.303 | +7.363 |
| ns/op | 0.084 | 0.065 | 0.067 | 0.070 | 0.071 | 0.074 | 0.077 |

96 independent `pmull` at the bare issue price of 0.25 cyc would cost 7.294 ns on
GV5 — measured **7.363 ns**. There is nothing free in the prepretail, at any K.
Contrast the prologue on GV4: 96 ops predicted 8.60 ns at bare price, measured
**7.68 ns** — ≈ 2.6 cyc of genuine slack.

*(The report's earlier suggestion that the prepretail must be latency-slack because
its marginal cost, 256 B − 128 B = 55.5 cyc, exceeds its 45.5 cyc floor is
therefore wrong: that 10 cyc difference is boundary/overlap accounting, not
fillable slack in the prepretail itself. Direct injection is the correct probe and
it says zero.)*

### Probe C — the net effect, measured end-to-end

`fusepp` = `drain0` **+** `mixpp`: the drain's GHASH removed *and* the same 65-op
mix injected into the prepretail. This is a faithful emulation of the proposed
change's *cost arithmetic* (same instruction mix, same two regions, real relink)
without hand-scheduling 500 lines of assembly. `fusepr` puts the mix in the
prologue instead. `*_corr` additionally injects the **7 extra slots the algebra
requires** — see §3.

256 B, Δ vs the base in the same binary:

| variant (destination) | GV3 | GV4 | GV5 | r8g |
|---|---:|---:|---:|---:|
| `fusepp` — prepretail, even spread | −2.54 % | −0.52 % | −0.03 % | −0.52 % |
| `fusepp_front` — prepretail, first third | −1.14 % | +2.26 % | +2.00 % | +2.64 % |
| `fusepp_mid` — prepretail, middle third | −2.08 % | +0.61 % | −0.18 % | +0.31 % |
| **`fusepp_back` — prepretail, last third (best)** | **−0.75 %** | **−0.96 %** | **−0.42 %** | **−0.94 %** |
| **`fusepp_corr` — prepretail + `T·H⁸` correction** | **−1.10 %** | **+1.35 %** | **+0.90 %** | **+1.70 %** |
| `fusepr` — **prologue**, even spread | −5.44 % | −3.18 % | −2.79 % | −3.32 % |
| `fusepr_corr` — prologue + correction | −3.96 % | −1.83 % | −1.64 % | −2.37 % |

Placement inside the prepretail matters by ~3 % (front is *worse* than base) but
no placement escapes the wash: the best is −0.4 … −1.0 %, and the required
correction terms turn it into a **regression on V2 and V3**.

---

## 3. What a *correct* prepretail fusion would have to add — and why it is +7 slots

GHASH is a Horner fold across groups. With `T` the tag after group 0 and `Cᵢ` the
group-1 ciphertext blocks,

```
A₁ = (T ⊕ C₈)·H⁸ ⊕ C₉·H⁷ ⊕ … ⊕ C₁₅·H¹ ,   T_out = reduce(A₁)
```

`T` is only produced by the MODULO reduce at the *end* of the prepretail, so it is
not available while the prepretail runs. Two ways out, both costed:

1. **Keep the partial-tag feed.** Then block 8's product must stay in the drain and
   only blocks 9–15 (7 blocks, ≈ 64 slots) can move. Slot count unchanged, so by
   §2 the net is exactly 0.
2. **Use linearity:** `(T ⊕ C₈)·H⁸ = T·H⁸ ⊕ C₈·H⁸`. Now **all eight** group-1
   products are independent of `T` and can be computed in the prepretail, and the
   drain shrinks to `T·H⁸` + fold + reduce. But `T·H⁸` is **3 extra `pmull` + 1
   `ext` + 1 `eor.8b` + 3 extra `eor3` = 8 new slots**, minus the one `eor v8,v8,v16`
   saved ⇒ **net +7 slots** that the baseline does not pay at all.
   Both regions are issue-saturated, so those 7 slots are pure loss:
   7 × 0.26 cyc ≈ 1.8 cyc ≈ 0.65 ns ≈ +1.4 % at 256 B — which is exactly the
   `fusepp_corr` − `fusepp_back` gap measured above.

On top of that, a real implementation also needs:

* **A duplicated prepretail.** The prepretail runs for *every* `nblk ≥ 9`, so
  group-1 GHASH cannot be folded in unconditionally (it would read past the buffer
  and use the wrong `H` powers when the remainder is 1–7 blocks). It needs a
  `.L256_dec_prepretail_x8` clone reached by a 3-instruction test at the top of
  the prepretail (`sub`/`cmp`/`b.gt` on `x4−x0` vs `#112`) — ≈ 380 duplicated
  lines, a whole new proof band.
* **3 long-lived group-1 accumulators + working temps in a region with 1–7 free
  registers**, i.e. stack spills (free on the load pipes, but they need `ldp`/`stp`
  and force the accumulate order).

Cost: a new ~380-line band plus a rewritten drain and a full re-proof, for a
measured net of **0 % on V2/V3**. Not built. That is the honest answer, and the
probe measurements above are stronger evidence than the static slot count that
the task's stop-rule was based on.

---

## 4. Cross-core reproduction of experiment A (independent, first time off r8g)

HEAD baseline vs HEAD + `_docs/expA-fused8-K80.patch`. Five slots linked into one
binary (`base`, `base` again for the A/A floor, `expA`, `base`, `base`),
round-robin with the order rotated every rep, `taskset -c 3`, best of 200 reps,
3 independent processes. Correctness self-check (18 sizes incl. every cascade
remainder 9–15, 17, 23, 31, 33, 255; `out`, `Xi` and `ivec` all byte-compared)
**passed in every process**. `expA` **KAT 35/35 PASS**; `base` **KAT 35/35 PASS**.

Absolute ns/call (min over the 3 processes):

| size | GV3 base | GV3 expA | GV4 base | GV4 expA | GV5 base | GV5 expA | r8g base | r8g expA |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| **128 B** | 30.114 | **27.312** | 25.512 | **23.007** | 21.464 | **19.619** | 25.522 | **23.003** |
| 256 B | 52.321 | 51.580 | 45.412 | 45.292 | 38.174 | 38.182 | 45.413 | 45.316 |
| 512 B | 94.430 | 94.026 | 84.198 | 84.451 | 71.116 | 71.141 | 84.364 | 84.413 |
| 1024 B | 179.828 | 179.555 | 161.826 | 162.035 | 138.522 | 138.512 | 161.909 | 162.029 |
| 4096 B | 693.997 | 691.473 | 628.752 | 628.811 | 546.858 | 546.854 | 628.644 | 628.776 |

Δ (median of the three per-process best-deltas — robust to the layout jitter that
makes min-of-mins misleading on GV3) and the **A/A noise floor**:

| size | GV3 Δ | GV3 A/A | GV4 Δ | GV4 A/A | GV5 Δ | GV5 A/A | r8g Δ | r8g A/A |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| **128 B** | **−9.30 %** | ±0.35 % | **−9.86 %** | +0.27 % | **−8.59 %** | ±0.02 % | **−9.87 %** | +0.28 % |
| 256 B | −0.21 % | +0.22 % | −0.25 % | −0.16 % | +0.01 % | ±0.02 % | −0.19 % | −0.14 % |
| 512 B | −0.17 % | ±0.30 % | +0.18 % | −0.01 % | +0.02 % | ±0.02 % | +0.13 % | **−0.71 %** |
| 1024 B | −0.32 % | ±0.30 % | +0.11 % | +0.01 % | −0.01 % | ±0.02 % | +0.05 % | −0.05 % |
| 4096 B | −0.36 % | ±0.13 % | +0.01 % | +0.05 % | 0.00 % | ±0.00 % | +0.02 % | +0.05 % |

**Experiment A reproduces on all three target cores.** `−10.1 %` on r8g becomes
**−9.87 % on r8g here, −9.86 % on GV4 (same µarch, different instance), −9.30 % on
V1 and −8.59 % on V3.** It does shrink across generations — V3 gives up 1.3 points
versus V2 — because V3's baseline 128 B call is already at 80.0 % of its slot floor
(V2: 79.3 %, V1: 72.4 %), i.e. V3 has less latency slack in the prologue to
recover. Everything other than 128 B is inside the A/A floor on every host;
**no regression anywhere, including 4 KB.**

Two notes on the floors, both worth carrying forward:
* GV4 and r8g show a **systematic +0.27…+0.30 % A/A bias at 128 B** (same code, two
  symbol names, order-rotated). It is reproducible across processes, so it is code
  *placement*, not noise — treat < 0.4 % deltas at 128 B on V2 as unresolvable.
* The prior report's degraded 512 B floor is confirmed on r8g (**−0.71 %**) and GV3
  (±0.30 %); GV5 is exceptionally quiet at ±0.02 % at every size and is the best
  host for small-effect work.

---

## 5. Answers to the deliverable questions

**(1) Step 1 numbers.** Prepretail+tail at 256 B: **408 slots ⇒ 102.00 cyc floor vs
126.79 measured cyc = 80.5 % on V2** (75.2 % V1, 81.2 % V3). Free registers in the
prepretail: **min 1, max 21, and NO register dead across the whole region**;
2–7 free through the GHASH-heavy middle, 14–21 free only in the last ~80 lines.

**(2) What changed.** No production change was made. 24 probe variants were built,
each a full `.S` → `.o` → relink. Patches and tooling kept at
`/Volumes/workplace/git-code/s2n-bignum-kiro/_docs/prepretail-probes/`:
`drain0.patch`, `drain4.patch`, `mixpp.patch`, `mixpr.patch`,
`ppload{4,8,16,24,32,48,72,96}.patch`, `pptail32.patch`, `prol{48,96}.patch`,
`fusepp.patch`, `fusepp_{front,mid,back}.patch`, `fusepp_corr.patch`,
`fusepr.patch`, `fusepr_corr.patch`, `emulp{p,r}{65,72}.patch`;
generators `gen.py`, `gen2.py`; analysis `analyze.py`, `analyze_lib.py`; harness
`bench.c`, `clk.c`, `mk.sh`, `kat.sh`, `build_bench.sh`; raw logs under `logs/`
(`{GV3,GV4,GV5,r8g}-run{1,2,4,5,6}.log`). Live copies remain in `/tmp/pfx` on each
host and `/tmp/pfx_artifacts` locally.

**(3) Per-host per-size ns/call and A/A floors.** §4 for base/expA (all four
hosts, five sizes, with floors); §2 for every probe. Raw per-process tables in
`logs/`.

**(4) Verdicts.**

| variant | verdict |
|---|---|
| **HEAD + expA (`expA-fused8-K80.patch`)** | **REAL WIN, reproduced cross-core: −9.86 % V2, −9.30 % V1, −8.59 % V3 at 128 B. Wash (inside the A/A floor) at 256 B–4 KB. KAT 35/35.** Ship-worthy given the 128 B dispatch-threshold decision |
| **prepretail drain fusion** | **WASH → REGRESSION. Not built.** Best emulated placement −0.42 … −0.96 % at 256 B; with the algebraically required `T·H⁸` correction **+0.90 % (V3), +1.35 % (V2), +1.70 % (r8g)**, −1.10 % (V1). Cost would be a ~380-line duplicated prepretail + rewritten drain + new proof band |
| **HEAD + both** | Not built — the second component is a wash, so "both" ≡ expA |
| *(bonus)* **prologue drain fusion** | **PROMISING, emulated only: −3.18 % (V2), −2.79 % (V3), −5.44 % (V1), −3.32 % (r8g) at 256 B; −1.6 … −4.0 % with the correction.** See §6 |

**(5) Does A's −10.1 % hold cross-core, and does it shrink?** Yes and yes:
−9.87 % (r8g, reproducing the original −10.1 % to within the 0.28 % A/A bias),
−9.86 % (V2), −9.30 % (V1), −8.59 % (V3). It shrinks by 1.3 points from V2 to V3,
tracking the baseline's rising slot-floor utilisation (72.4 % → 79.3 % → 80.0 %):
the newer core has less prologue latency slack left to sell.

**(6) Did the projected −5.7 % at 256 B materialise?** **No — for the prepretail
destination it cannot, and the mechanism is now measured rather than argued.**

The 2.581 ns that experiment A recovered was *not* "the per-call constant" that any
region can reclaim; it was **prologue latency slack** specifically. The 8.9 ns
sitting above the slot floor at 256 B is not distributed across the call — probe B
localises it:

* **drain**: 0.264 cyc per SIMD op ⇒ at ~100 % of its 18.25 cyc issue floor. No slack.
* **prepretail**: 0.260 cyc per SIMD op — statistically identical to the drain, and
  96 injected `pmull` cost 7.363 ns against a 7.294 ns bare-issue-price prediction.
  **Zero slack.** The prepretail is *already the fused region*: it interleaves 26
  `pmull` + 45 vector-ALU GHASH ops with its AES, and that GHASH has already filled
  every AES dependency stall. There is nothing left for a second group's GHASH to
  hide in.
* **prologue**: 0.192–0.212 cyc per SIMD op, ~25 % below the issue price. **This is
  where the slack lives**, and experiment A is precisely the transaction that
  monetises it.

So drain→prepretail is a 1:1 slot exchange between two saturated regions, which
nets 0 before the `T·H⁸` correction and negative after it — exactly what the
composite emulation measures. The −5.7 % projection assumed the 2.581 ns was a
region-independent constant; it is not.

---

## 6. Exact next step, if continued

The same relocation with the **prologue** as destination is worth **−3.18 % (V2),
−2.79 % (V3), −5.44 % (V1)** at 256 B by direct emulation (`fusepr`), decaying as
`≈ 1.4–2.3 ns / call` at 512 B → 4 KB, and it is register-feasible (17 dead SIMD
registers, disjoint from the AES set exactly as in experiment A). Shape:

1. At entry, when `x9 % 128 == 0 && x9 > 128`, take a variant path.
2. In the prologue, alongside AES(0..7), compute the **eight `Cᵢ·H^(16−i)` products
   of the LAST group** (pointer `x4−128`; `T`-independent by the linearity identity
   in §3) into 3 accumulators, then `stp` them to the stack.
3. Main loop and prepretail run **byte-identical** (they never see the change).
4. The drain reloads the 3 accumulators, folds `T·H⁸`, reduces. Its 65 GHASH ops
   are gone.

Caveats, honestly: this touches the prologue (experiment A's territory, so the two
would have to be merged), needs the last group's ciphertext read early — a
prefetch effect not captured by my dummy-op emulation and worth a separate probe —
and pays the same +7 correction slots. Its measured ceiling with the correction is
**−1.6 % (V3) … −4.0 % (V1)** at 256 B, and only −0.1 … −0.5 % at 4 KB.

Do **not** pursue the prepretail variant. Both its source and its destination
region are at ~100 % of the SIMD issue roofline; the transaction has no profit in it.
