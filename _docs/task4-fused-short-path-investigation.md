# Task 4 — Fused / de-staggered short-message path: cost-vs-gain investigation

**Session 106, 2026-08-14.** Investigate-and-report-first (per the 2026-08-14 "NEW
PHASE A" directive + its addendum in STATE.md). No `.S` or proof changes made.

**Bottom line (recommendation): DO NOT build it now.** The measured gain ceiling is
a single-digit-ns, ≤256-byte-only, fixed-overhead reclaim on the decrypt kernel; the
proof cost is a *new proved code path with its own interleaved simulation and a
re-derived 8-block GHASH close* — structurally the two-stream main-loop body, which
project history records as the highest-risk, multi-session phase (Phases 2–4), and
whose GHASH-close sub-problem (Q19) alone cost ~15 sessions. The cost/gain ratio is
far worse than any of the four ports that landed. A reasoned negative, as the
directive explicitly invites.

---

## 1. What "fused short path" means here (confirmed against the kernel)

The kernel `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` is a software pipeline. Verified
instruction mix per region (grep counts, this session):

| region | lines | aese | aesmc | pmull(+2) | character |
|---|---|---:|---:|---:|---|
| prologue        | 52..371   | 112 | 104 | 0  | **AES only** (8 blocks: 14·8 aese, 13·8 aesmc) |
| main loop body  | 415..832  | 112 | 104 | 26 | interleaved AES + GHASH of the *previous* group |
| prepretail      | 834..1214 | 112 | 104 | 26 | interleaved (drains the last in-flight group) |
| tail cascade    | 1215..1520| 0   | 0   | 29 | **GHASH only** |
| exact-8 drain   | 1521..1717| 0   | 0   | 41 | **GHASH only** |

At exactly 8 blocks (128 B) the `b.ge .L256_dec_tail` at `.S:371` skips the loop and
prepretail entirely: the call is **prologue (AES only) → tail (GHASH only)** with
**zero overlap**. This is the case the human's roofline measured at 69%.

The GHASH input is ciphertext **loaded from memory** (`ldr q9,[x0]` in the tail, and
`ldp q8,q9,[x0]` in the loop) — never AES output. So in *decrypt* the fill/drain
stagger is **not required by any data dependency**; it exists only to hide *load*
latency (GHASH consumes ciphertext fetched an iteration earlier). A fused short path
would interleave the 8 GHASH folds into the AES-only prologue so the GHASH multiplies
issue on the SIMD pipes in parallel with `aese`/`aesmc` on the AES pipes.

---

## 2. GAIN side — measured, with the roofline validated

Roofline model (human's parameters: 14 aese + 13 aesmc = 27 AES ops/block, 4 AES
ops/cycle, clock 2.79 GHz), reproduced exactly this session:

```
128B (8 blk):  216 AES ops / 4 = 54.0 cyc / 2.79 GHz = 19.35 ns  (AES roofline)
Measured V2 dec 128B (optimised kernel)              = 27.98 ns
  => 19.35 / 27.98 = 69.2 %  of AES roofline   (human's "69%" — confirms the model)
```

- **Max theoretically reclaimable @128B** = the non-overlapped GHASH-tail overhang =
  27.98 − 19.35 = **8.6 ns**. Best case (fused reaches the loop's 98% roofline):
  ~19.75 ns, i.e. **−29 % @128B, ≈ 8.2 ns/call**. This is a *ceiling*, not a forecast:
  the final Barrett reduce can never be hidden (no AES remains after the last block),
  and at only 8 blocks there is less OoO slack than at 4 KB, so the realistic gain is
  materially below 8 ns.
- **Size envelope is narrow.** The reclaim is a fixed per-call overhead, so it decays
  with size exactly like the two landed tail opts: measured dec totals already show
  256 B running at ~80 % of roofline (overlap starts helping by one block-group), and
  512 B-and-up converge to the roofline — a fused path saves essentially nothing there.
  Realistically only **128 B (and partly 256 B)** benefit.
- **Newer cores hide more of it.** The runtime-opt benchmark doc's own pattern (dec
  128 B total: −15.8 % V1 → −13.8 % V2 → −11.1 % V3) is the tell: a wider, better-
  renamed core already overlaps more of the tail. A fused path — like the false-dep
  fixes — pays off most on V1/Graviton3 and least on V3, i.e. the gain shrinks on the
  hardware customers are migrating toward.

**Gain verdict:** a genuine but modest, size-narrow, generationally-shrinking win of
at most ~8 ns/call at 128 B, tapering to ~0 by 512 B. Same *class* of win as the
`ins→ext` and exact-8-drain opts, somewhat larger at 128 B because it attacks the
whole non-overlap rather than one false dependency.

---

## 3. COST side — a new interleaved code path, grounded in this proof's own numbers

### 3a. The existing ≤8-block proof already mirrors the *staggered* machine

`prove_band k` (mainloop.ml:5359) proves each nblk≤8 band as:

```
WB_FRONT_BUF   (AES-only front sim, 0x20..0x428, ~259 steps)   +   WB_TAIL_k (GHASH-only tail sim)
```

composed sequentially — exactly the prologue→tail shape of the machine. Per-theorem
CPU cost from the load profile (`_docs/wb-dec-PROFILE_RESULT.md`, HEAD 4cb31d5e):

- `WB_FRONT_BUF` = 234 s; `WBN_FRONT_BUF` = 270 s (AES-only fronts)
- `WB_TAIL_GEN2_1..8` = 132 s → 311 s (GHASH-only tails); `BUF_kBLOCK` = 143 s → 324 s
- `WBN_MAIN_LOOP` (the ~340-instr **interleaved** AES+GHASH loop body) = 190 s

A fused path is **not** `front + tail`. It is a **new interleaved AES+GHASH stream**
producing the *same* postcondition by a *different* instruction sequence — i.e. the
`WBN_MAIN_LOOP` shape (two-stream, GHASH lagging), not the composable front/tail shape
the ≤8 bands enjoy.

### 3b. Concrete cost anchor: the standalone 1-block interleaved proof

`arm/proofs/aesv8_gcm_8x_dec_256_1block.ml` (git 3fd11092) proves ONE interleaved
AES+GHASH block: 2262 lines, 351 sim steps, **~328 s to cold-load** *after* being
optimized down from 554 s across four dedicated speedup commits. A fused ≤8-block path
is ~8× that instruction volume **with a live GHASH accumulator across all 8 blocks**
(so GHASH terms compound rather than reset) plus the Barrett reduce — i.e. the
`WB_TAIL_8` term-explosion (311 s) now *entangled with* the AES simulation state.

### 3c. The GHASH-close algebra is the landmine

Closing the 8-block GHASH accumulation against `nist_ghash` in an *interleaved* state
is precisely the **Q19** problem: the machine's pipelined pre-summed Karatsuba reduce
vs the spec's fold. Q19 was the single hardest sub-problem of the whole project — on
the order of **15 sessions** (s018–s065; see the Decisions Log and the wb-dec-q19-*
memory entries), only closed by the R1' pre-reduce refold. A fused path re-opens the
GHASH close in a *new* context (no guarantee the existing `WB_TAIL_8_TAC` /
`WBN_MACHINE_REDUCE_IS_PROP3_PACK` machinery transfers, since the accumulator state
and step numbering differ). Best case it ports with a step-shift; worst case it is
another Q19-class arc.

### 3d. "Append is cheap" does not rescue this

The human's cost calibration ("APPENDED code is cheap") held for the exact-8 drain
because that was **GHASH-only** code appended at the end, reached by retargeting one
branch, reusing `WB_TAIL_8`'s machinery with a uniform −13 step-shift. A fused path
cannot be a clean append: the AES-only prologue (52..415) is *shared* by every path
and does blocks 0–7's AES for everyone; fusing means a **separate** interleaved
prologue branched-to at entry on nblk≤8. The layout ripple (a new entry branch) is
cheap, but the *proof* of the appended path is a full interleaved simulation **plus**
the re-established GHASH-8 close — and appending makes neither cheaper. "Append =
cheap" is about the PC-shift ripple, not the new-path simulation.

### 3e. Cost estimate

- **Effort:** several sessions minimum (new invariant/straight-line block + new
  interleaved sim + GHASH-8 close in the fused context + dispatch re-anchor + KAT +
  benchmark), **high variance**, with a real tail risk of reopening Q19-class algebra.
  This is qualitatively the `WBN_MAIN_LOOP` / Phase-4 class of work, not the
  drain/`ins→ext` class (each of which was one session with load going *down* or flat).
- **Load-time:** a new ~120-instruction interleaved theorem adds roughly a front + a
  tail band of CPU (~300–600 s) to the cold gate, i.e. **+5–10 min** on the current
  ~2140 s — a permanent tax on every future gate for a 128-B-only runtime win.

---

## 4. Corroboration: the expert encrypt optimizer did NOT build this

Mila's encrypt kernel on `mila/aes_gcm_256_x8_clean`
(`arm/aes_gcm/aesv8_gcm_8x_enc_256_wb.S`) — **six** optimizations deep — has the
*identical* staggered structure (`main_loop` / `prepretail` / `tail` / `exact8_drain`)
and **no fused/de-staggered short path**. The most aggressive optimizer in this
codebase optimized *within* the stagger (drain, eor3-fusion, counter-flatten) and did
not de-stagger — even for **encrypt**, where the fill/drain *are* dependency-required
(GHASH consumes AES output) and thus a *harder* target than decrypt. That an expert
human-guided optimizer judged it not worth building is strong independent evidence.

---

## 5. Recommendation

**Do not build the fused short path as a from-scratch effort at this time.** Record
the measurement (≤8.6 ns/call ceiling @128 B, tapering to ~0 by 512 B, shrinking on
newer cores) and the reason (new interleaved proved code path ≈ the highest-risk
main-loop-body class, with a Q19-class GHASH-close landmine, for a 128-B-only gain),
per the directive's explicit invitation to report a reasoned negative rather than
silently drop it.

**If the human still wants it** (it is human-*wanted*, only human-*gated on cost*),
the cheapest viable decomposition to scope a dedicated multi-session arc:
1. A dedicated **straight-line ≤8-block fused routine** (no loop — 8 is the short-path
   max), appended after the current code, entered by a new nblk≤8 branch at entry.
2. Prove it as a new `ensures` with the **same DISPATCH postcondition**
   (`gcm_dec_pt_bytes` / `nist_ghash` / ivec write-back), so the existing ≤8 bands can
   be *retired* rather than run in parallel (keeps the exported surface unchanged).
3. Budget it as `WBN_MAIN_LOOP`-class work and pre-decide a fallback: if the GHASH-8
   close does not port from `WB_TAIL_8_TAC` within one session, stop and keep the
   certified staggered proof (the human's standing fallback pattern).

Either way this is **not** a same-session land like the four ports; it needs its own
dedicated arc and an explicit go decision from the human with eyes on this cost.

---

### Evidence index
- Kernel regions/counts: `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` (this session's grep).
- Roofline validation: 27 AES ops/blk, 4/cyc, 2.79 GHz → 69.2 % @128 B.
- Measured ns: `_docs/aes-gcm-8x-wb-runtime-optimisation-benchmarks.md` (V2 dec
  128 B opt = 27.98 ns), `_docs/aead-bench-round1/` (128 B raw).
- Proof timing: `_docs/wb-dec-PROFILE_RESULT.md` (per-theorem CPU).
- Cost anchor: `aesv8_gcm_8x_dec_256_1block.ml` (git 3fd11092), ~328 s / 351 steps.
- GHASH-close history: STATE.md Decisions Log + wb-dec-q19-* memory (s018–s065).
- Corroboration: `mila/aes_gcm_256_x8_clean:arm/aes_gcm/aesv8_gcm_8x_enc_256_wb.S`.
