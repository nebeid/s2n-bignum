# De-staggering the AES-256-GCM decrypt kernel — measurement-only experiment

> **HUMAN DECISION, 2026-08-14 — the 128 B-only scope is NOT a limitation.**
> aws-lc's `len >= 256` gate on 8x dispatch (two sites in `gcm.c`) **will be lowered to
> 128**. Any statement in this document (or in
> `task4-fused-short-path-investigation.md`) that a 128 B-only gain is "unreachable in
> production" or "narrow" is therefore superseded: experiment A's −10.1% counts as a real
> production win, and such changes are to be judged on proof cost versus measured gain
> alone.
>
> **HUMAN DECISION, 2026-08-14 — experiment A is archived, not landed.** Despite the
> measured −9.9 % V2 / −9.3 % V1 / −8.6 % V3 at 128 B, the fused path is not being taken
> into the kernel: it is entered by an exact-equality test on one message length, so it
> buys a special case in code that must stay verifiable (a new proved path plus a
> re-anchor of every downstream band, since its 3-instruction dispatch shifts all
> following PCs). `expA-fused8-K80.patch` is kept as a record of the measurement and the
> schedule, not as work queued for landing.

Host `ec2r8g` (Neoverse-V2, aarch64), clock **measured 2.7927 GHz** (dependent-add chain,
5 runs, spread <0.06%). All work done in scratch `/tmp/dstg/`; the live tree
`~/whole-proofs/s2n-bignum` was **never modified** (git status byte-identical before/after,
`arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` md5 unchanged). No HOL Light, no `.ml`, no proofs.

Measurement discipline: every variant rebuilt from `.S` through `arm/Makefile` and
**relinked** (`objcopy --redefine-sym` into `dec_old`/`dec_new`, fresh `gcc` link per variant).
A/A noise floor established first: **±0.19%** at all five sizes.

---

## 0. Headline

| | |
|---|---|
| Constant-overhead model | **HOLDS** — but the constant is **6.35 ns**, not 8.6 ns |
| Experiment A (fused nblk=8) | **REAL WIN: −10.1% at 128 B** (25.589 → 23.008 ns), KAT 35/35 + absolute 23/23 |
| Experiment B (zero-lag pipeline) | **NOT BUILT — dead.** Loop is at 94.4% of the hard SIMD-slot roofline and de-staggering changes zero slots |
| Experiment C (pin round keys) | **WASH, measured to 0.00 ns.** Deleting *all* key loads for free gains nothing |
| Biggest correction | **The "idle GHASH pipes" premise is false.** `aese`/`aesmc`/`pmull`/`eor` all issue on the same 4 SIMD pipes; mixing is **additive**, not overlapped |

---

## 1. Baseline and the constant-overhead fit

Best-of-30, interleaved A/B, `taskset -c 3`, 200-call warmup per pass.

| size | blocks | best | median | worst | cycles |
|---|---:|---:|---:|---:|---:|
| 128 B | 8 | **25.589** | 25.746 | 26.258 | 71.46 |
| 256 B | 16 | **45.351** | 45.705 | 46.389 | 126.65 |
| 512 B | 32 | **84.374** | 84.701 | 88.022 | 235.63 |
| 1024 B | 64 | **161.804** | 162.337 | 164.203 | 451.87 |
| 4096 B | 256 | **628.695** | 629.637 | 632.640 | 1755.76 |

Least-squares fit over all five points:

> **ns/call = 2.4310 × blocks + 6.350**

| size | measured | fit | residual |
|---|---:|---:|---:|
| 128 B | 25.589 | 25.798 | −0.209 (−0.82%) |
| 256 B | 45.351 | 45.246 | +0.105 (+0.23%) |
| 512 B | 84.374 | 84.142 | +0.231 (+0.27%) |
| 1024 B | 161.804 | 161.935 | −0.131 (−0.08%) |
| 4096 B | 628.695 | 628.691 | +0.004 (+0.00%) |

**The constant-overhead model holds very well** — max residual 0.23 ns (0.3%) across a 32x
size range. The fitted constant is **6.350 ns**, not the predicted 8.6 ns, and the marginal
cost is **2.4310 ns/block**.

---

## 2. The premise is wrong: there is no idle GHASH pipe

This is the most important result and it was cheap to get. Direct issue-throughput
microbenchmarks (`/tmp/dstg/pipes.c`, `pipes2.c`, `pipes3.c`), large unrolled bodies to
remove frontend effects:

| body | cycles | instr | instr/cycle |
|---|---:|---:|---:|
| 32 × (`aese`+`aesmc`) adjacent | 7.994 | 64 | **8.006** |
| 32 × lone `aese` | 7.992 | 32 | 4.004 |
| 32 × `pmull`/`pmull2` | 9.217 | 32 | 3.472 |
| 32 × vector `eor` | 8.709 | 32 | 3.674 |
| 32 pairs **+** 32 `pmull` | **16.611** | 96 | 5.779 |
| 32 pairs **+** 32 `eor` | **16.080** | 96 | 5.970 |
| 64 pairs | 15.993 | 128 | 8.003 |

Mixed cost = **sum** of the parts (7.99+9.22 = 17.21 predicted vs 16.61 measured), **not**
`max` (9.22). Conclusion:

* **All vector ops — `aese`, `aesmc`, `pmull`, `pmull2`, `eor`, `eor3`, `ext`, `rev*` — contend
  for the same 4 SIMD issue slots.** There is no separate "GHASH pipe" and the AES-only
  prologue does **not** have idle SIMD capacity.
* **Adjacent `aese`+`aesmc` fuse into one slot** and issue at 4 pairs/cycle = 8 instr/cycle.
  Not 4 ops/cycle.
* Breaking that adjacency **doubles** AES cost. Verified exactly: inserting an `eor` *between*
  `aese` and its `aesmc` gives 23.995 cyc for 32 pairs + 32 eor = 96 unfused slots / 4 = 24.0
  cycles, dead on. (Inserting it *between pairs* instead: 15.994 cyc.) This constraint was
  enforced in the code generator.

### Consequence for the roofline

True AES cost per block = 13 fused pairs + 1 lone `aese` (round 13 has no `aesmc`) = **14 slots
= 3.50 cyc = 1.253 ns**. The briefing's "27 ops @ 4/cycle = 6.75 cyc = 2.417 ns/block"
**overstates pure AES by 1.93x.**

But the briefing's number is nevertheless *numerically* almost right — by coincidence. Counting
every SIMD issue slot per region (`aese`+`aesmc` pairs = 1 slot, `.inst`-encoded `eor3` included):

| region | fused pairs | lone aese | pmull | other vec ALU | **slots** | floor @4/cyc |
|---|---:|---:|---:|---:|---:|---:|
| prologue | 104 | 8 | 0 | 26 | **138** | 34.50 |
| main loop body | 104 | 8 | 26 | 67 | **205** | 51.25 |
| prepretail | 104 | 8 | 26 | 45 | **183** | 45.75 |
| tail cascade | 0 | 0 | 26 | 113 | **139** | 34.75 |
| exact-8 drain | 0 | 0 | 24 | 49 | **73** | 18.25 |
| epilogue | 0 | 0 | 2 | 10 | **12** | 3.00 |

Two ~2x errors cancel: AES is half as expensive as assumed, but the omitted GHASH/CTR/store
SIMD ops (93 slots per 8 blocks) nearly make up the difference.

* **Main loop: 205 slots / 8 blocks → 51.25 cyc floor. Measured marginal 54.31 cyc = 94.4% of
  the true SIMD-slot roofline.**
* **nblk=8 path** (prologue 138 + tail entry 3 + drain 73 + epilogue 12) = **226 slots → 56.50
  cyc = 20.23 ns floor.** Measured 71.46 cyc / 25.589 ns → only **5.36 ns** is theoretically
  recoverable at 128 B, and it is *latency/ILP*, not idle pipes.

---

## 3. Experiment A — fused exact-128-byte path (BUILT, REAL WIN)

**Patches:** `/tmp/expA-fused8-K80.patch` (the winner), `/tmp/expA-fused8-even.patch` (first,
evenly-interleaved version). Generator: `/tmp/gen/genfused2.py` + `/tmp/gen/gh.txt`;
verifier `/tmp/gen/verify.py`. Variant sources `/tmp/dstg/obj/fusedK*.S`.

### What changed

A new straight-line path `.L256_dec_fused8`, entered by `cmp x9,#128 / b.eq` inserted right
after `add x10, sp, #64`. Nothing else in the kernel is touched — the loop, prepretail, tail
cascade and the general exact-8 drain are byte-identical, so **only the 128 B case changes.**

The enabling structural facts:
* The decrypt GHASH input is loaded ciphertext, so GHASH(0..7) has **no** dependency on AES.
* Within a group of 8, GHASH is an **aggregated reduction** (8 independent products + one
  modulo), *not* a sequential Horner fold — so the prologue can absorb all 8 blocks' products.
  (The briefing's Horner caveat is correct only at *group* granularity.)
* **The prologue has 18 free SIMD registers.** `v8`–`v25` are all dead once the CTR setup
  finishes; the AES rounds touch only `v0`–`v7` (states), `v26`–`v28` (rotating round keys)
  and `v30`/`v31` (counter). So the register partition **AES = {v0-v7,v26-v28,v30,v31}** /
  **GHASH = {v8-v25}** is disjoint with zero spills. Verified mechanically: 0 violations.

Schedule (the winner, `K=80` of 119 AES units):
1. CTR/key setup, plus the `add v30,v30,v31` counter bump hoisted out of round 11 so the
   counter store can float freely.
2. GHASH(0..7) **front-loaded** into AES units 0..80, one GHASH op per ~1 AES unit, never
   splitting an `aese`/`aesmc` pair. Ciphertext read with non-post-incrementing
   `ldr q9,[x0,#16*i]` so `x0` stays put.
3. MODULO reduce + tag store + ciphertext **reload** (`ldp q8..q15`, guaranteed L1-hot — the
   GHASH just touched those exact lines) interleaved into AES units 80..119.
4. Final: 8 `eor3` plaintext + 4 `stp` + epilogue.

Front-loading step 2 is what mattered: with an even interleave the 14-cycle MODULO chain is
fully exposed at the end. Sweep of the split point (all KAT 35/35):

| K | 50 | 60 | 70 | 74 | 76 | 78 | **80** | 82 | 84 | 86 | 90 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Δ at 128 B | −9.45% | −9.39% | −9.67% | −10.22% | −10.01% | −10.04% | **−10.11%** | −9.58% | −9.44% | −9.21% | −9.01% |

Even interleave (no front-loading): −6.63%. Plateau at K=74..80.

### Verification
* `brk #0` probe inserted in the new path → binary **crashed** (`Trace/breakpoint trap`),
  proving the path is genuinely entered. Probe then removed.
* Differential KAT: **35 passed, 0 failed — KAT GATE: PASS**
* Absolute enc→dec round-trip KAT (aws-lc): **23 passed, 0 failed — ABSOLUTE KAT: PASS**
* Generator self-check: 104 fused pairs + 8 lone `aese` (as baseline), 0 register-partition
  violations, 225 slots (baseline path 226 — same work, different order).

### Measured, K=80 vs baseline (best-of-30, two independent runs)

| size | baseline best (med / worst) | fused A best (med / worst) | Δ |
|---|---:|---:|---:|
| **128 B** | 25.589 (25.746 / 26.258) | **23.008** (23.132 / 23.852) | **−10.09%  (−2.581 ns)** |
| 256 B | 45.351 (45.705 / 46.389) | 45.355 (45.840 / 48.224) | +0.01% |
| 512 B | 84.374 (84.906 / 85.929) | 84.421 (85.293 / 85.940) | +0.02% |
| 1024 B | 161.804 (162.338 / 164.344) | 161.943 (162.179 / 164.150) | +0.09% |
| 4096 B | 628.695 (629.637 / 632.640) | 628.850 (630.649 / 633.618) | +0.02% |

Repeat run: 128 B −10.10%. Everything except 128 B is inside the ±0.19% A/A noise floor, as
expected. **No regression at any size, including 4 KB.**

### Verdict: REAL WIN, narrow scope
−2.581 ns at 128 B = 48% of the 5.36 ns theoretical headroom (and ~60% of a realistic
headroom of 4.3 ns computed from measured per-op throughputs: 112/4 + 24/3.47 + 90/3.67 =
59.4 cyc = 21.3 ns). Post-fusion the 128 B call sits at 87.9% of its slot roofline, up from
79.1%. The mechanism is **latency/ILP recovery, not pipe recovery** — total slots are
unchanged (226 → 225).

---

## 4. Experiment B — zero-lag pipeline (NOT BUILT — dead, with numbers)

I did not build B. The reason is quantitative, not budgetary:

1. **De-staggering changes zero SIMD slots.** It is a pure reordering — same instructions.
   The main loop body issues 205 slots per 8 blocks = 51.25 cyc floor and **already measures
   54.31 cyc = 94.4% of that floor.** The absolute maximum available anywhere in the loop is
   3.06 cyc per 8 blocks (5.6%), and no reordering can go below the floor.
2. **The current stagger is not costing ILP.** AES(group k) and GHASH(group k−1) are already
   fully independent. Lock-step (AES and GHASH of the *same* group) is equally independent in
   decrypt — so it buys no new ILP, while giving strictly *less* slack to cover load latency
   (the briefing's own second caveat).
3. **The whole prize is the per-call constant, and A measured how much of it is actually
   recoverable: 2.581 ns.** So B's ceiling is that same constant applied at every size:

| size | baseline | B ceiling (−2.581 ns) | ceiling gain |
|---|---:|---:|---:|
| 128 B | 25.589 | 23.008 | 10.1% *(already delivered by A)* |
| 256 B | 45.351 | 42.770 | **5.7%** |
| 512 B | 84.374 | 81.793 | 3.1% |
| 1024 B | 161.804 | 159.223 | 1.6% |
| 4096 B | 628.695 | 626.114 | **0.4%** |

4. Per the briefing's own stop rule ("if A recovers only 1–2 ns, B is probably dead"), A
   recovered 2.58 ns — marginally above that line, and only 30% of the 8.6 ns that the
   original model predicted.

**Verdict: dead as specified.** The cost is rewriting the main loop, prepretail *and* the
8-way tail cascade (GHASH indices shift by 8, load offsets change) plus a complete re-proof,
for an upper bound of 5.7% at 256 B falling to 0.4% at 4 KB. If any of that is wanted, the
sane scope is *not* B: it is to extend A's fusion technique to the other exact-multiple-of-8
entry sizes, which leaves the loop and cascade untouched.

---

## 5. Experiment C — pin round keys in SIMD registers (WASH, measured)

**Register-pressure finding (the direct answer):** de-staggering frees **zero** registers in
the loop. The 8 ciphertext staging registers are needed in *both* schedules — in lock-step,
`C_i` must still be held from its load until the plaintext `eor3`, exactly as in the staggered
version. The lag is not what those registers are for.

In the *fused prologue* the accounting is: `v0`–`v7` AES states (8) + `v8`–`v25` GHASH (18) +
`v26`–`v28` round keys (3) + `v30` counter = 30 of 32. Free: **`v29` and `v31` — 2 registers.**
AES-256 needs **15** round keys. So at most 2 of 15 could ever be pinned.

**Ceiling probe** (`/tmp/expC-ceiling-nokeyloads.patch`): I deleted all 8 round-key
loads from the fused path outright. This is functionally wrong on purpose — it is an upper
bound on what pinning *all 15* keys for free could ever buy. KAT correctly reports **34 passed,
1 failed** (only the nblk=8 case), which also re-confirms the deletion took effect on a live path.

| | 128 B best |
|---|---:|
| Fused A (K=80), correct, KAT 35/35 | 23.005 |
| Fused A with **all key loads deleted** (wrong, ceiling only) | 23.002 |

**Δ = 0.003 ns = 0.01%, i.e. zero.** The key loads sit on the load pipes, are scheduled ahead
of use, and consume **no SIMD issue slots** — the only resource that is scarce. This confirms
and extends the prior investigation: the earlier finding was "no gain in the loop"; the answer
for the **prologue** is the same, and it is a wash there too. **Experiment C is dead everywhere,
and this cost one measurement rather than a rewrite.**

---

## 6. Things that contradict the briefing

1. **"prologue: AES only — SIMD/GHASH pipes idle" is FALSE.** No separate GHASH pipe exists.
   `aese`/`aesmc`/`pmull`/`eor` share 4 SIMD pipes; mixed cost is additive. This invalidates the
   stated *mechanism* for both A and B. (A still won — via latency/ILP recovery — but its
   ceiling is `(226 slots)/4 = 56.5 cyc`, not `prologue-only = 34.5 cyc`.)
2. **"4 AES ops/cycle" is wrong** — adjacent `aese`+`aesmc` fuse; 4 pairs/cycle = 8 instr/cycle.
   True AES cost is 14 slots/block (3.50 cyc), not 27 ops (6.75 cyc).
3. **The 2.419 ns/block roofline is right by coincidence**, via two cancelling ~2x errors
   (AES 2x cheaper; ~93 GHASH/CTR/store slots per 8 blocks omitted). The correct
   total-SIMD-slot roofline is 2.294 ns/block and the loop is at **94.4%** of it, not 98%.
4. **"Measured baseline at 128 B = 27.98 ns" — I measure 25.589 ns**, 8.5% lower, with a
   genuine relink (best-of-30, 200-call warmup, `taskset -c 3`, A/A noise floor ±0.19%).
   Consequently the 128 B baseline is 79.1% of its true roofline, not 69.2%.
5. **The fitted overhead constant is 6.350 ns, not 8.6 ns** — though the constant-overhead
   *model* holds excellently (max residual 0.23 ns / 0.3% over 8..256 blocks). Of that 6.35 ns,
   only ~5.36 ns is above the slot floor and only **2.58 ns proved recoverable**.
6. **"zero free registers"** is true of the loop but **not of the prologue**, which has 18 dead
   SIMD registers (`v8`–`v25`). That is precisely what made A implementable with no spills.
7. **4 KB does not regress** (A does not touch that path), and nothing regresses anywhere.
8. Minor: within a group of 8, GHASH is an aggregated reduction with fully parallel products,
   not a sequential Horner fold; the Horner constraint binds only across groups.

---

## 7. Artifacts

| path | contents |
|---|---|
| `/tmp/expA-fused8-K80.patch` | **Experiment A winner** (−10.1% @128 B, KAT 35/35 + absolute 23/23) |
| `/tmp/expA-fused8-even.patch` | A, evenly interleaved (−6.6% @128 B), KAT 35/35 |
| `/tmp/expC-ceiling-nokeyloads.patch` | C ceiling probe — **functionally wrong on purpose**, KAT 34/35 |
| `/tmp/dstg/obj/base.S`, `fusedK*.S`, `fusedC.S` | variant sources |
| `/tmp/dstg/bench5.c`, `bK80`, `bench_AA` | 5-size interleaved A/B harness + A/A noise floor |
| `/tmp/dstg/pipes.c`, `pipes2.c`, `pipes3.c` | issue-pipe / fusion microbenchmarks |
| `/tmp/dstg/clk.c` | clock measurement (2.7927 GHz) |
| `/tmp/gen/genfused2.py`, `gh.txt`, `verify.py` | code generator + mechanical verifier |
| `/tmp/dstg/s2n/` | scratch worktree copy (live tree never touched) |

## 8. Exact next step, if continued

Extend A's fusion to the other sizes that enter the exact-8 drain, i.e. `byte_len % 128 == 0`
with `nblk > 8`, by fusing the **drain** into the **prepretail** (which is already
AES+GHASH interleaved and has the same register slack). That captures most of the same
2.58 ns constant at 256/512 B — worth ~5.7%/3.1% — while leaving the main loop and the
8-way tail cascade byte-identical, so the proof delta stays bounded. Do **not** attempt B as
specified: it rewrites the loop and cascade for the same constant.
