# "Did we try this?" — AES-256-GCM decrypt kernel optimisation attempts

A reference record of the exploration that started with *"can we de-stagger the GHASH
outside the loop?"* and ended with the fused small path. Written as the questions asked and
the answers measurement gave, so nobody re-runs a dead end.

Scope: `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S`, exploration only. The **five optimisations
already landed** (ins→ext in the GHASH tail mids, dedicated exact-8 drain, eor3-fused drain
accumulate, flattened SETUP counter chain, shortened TAIL odd-block mids — cumulatively
+21 % @128 B, +16 % @256 B, +1.5 % @4 KB) predate this arc and are recorded in
`percommit-crosscore-benchmark-2026-08-14.md`.

All measurements: GV3 = Neoverse-V1 @2.591 GHz, GV4 = Neoverse-V2 @2.792 GHz,
GV5 = Neoverse-V3 @3.291 GHz, plus `ec2r8g` (V2) as an inter-instance control. Every run
used one binary with all variants linked in, round-robin timing with rotated slot order, an
A/A noise floor from identical code under two symbol names, and a byte-compare of
`out`/`Xi`/`ivec`/return before any timing was reported.

---

## Quick reference

| Idea | Verdict | Best number |
|---|---|---|
| De-stagger GHASH in the main loop (zero-lag pipeline) | **dead as specified** | premise false — no idle pipe exists |
| Fused exact-128-byte path | **real win, archived** | −9.9 / −9.3 / −8.6 % @128 B |
| Pin all 15 round keys in SIMD regs (main loop) | **wash** | 0.00 ns |
| Fuse the GHASH drain into PREPRETAIL | **wash → regression** | +0.9…+1.7 % on V2/V3 |
| Relocate final group's GHASH into the prologue | **small win, rejected on cost** | −3.5…−3.9 % @128 B, but frame 80→128 B |
| …same without frame growth | **regression** | +1.8…+4.2 % @256 B |
| Fused small path, 8 per-size bodies | **big win, rejected on shape** | −47 % @16 B … −9.7 % @128 B, `.text` ×2.49 |
| `t4p8` — bodies for {1,2,3,4,8} | **rejected: per-size paths** | −41 % @64 B, −9.9 % @128 B |
| `g4` — one 4-wide group + dead AES for n≤4 | **loses to cascade** | −22/−20/−13 pts worse @16/32/48 B |
| `mix4s4` — 4-wide group + 4 sequential | **regression at 128 B** | +13…+21 % @128 B |
| W=1 cascade over all 8 blocks | **regression at 128 B** | +7 % |
| **`s4h` — W=1 cascade, nblk ≤ 4 only** | **CHOSEN** | −47.1/−42.2/−31.3/−20.0 % (V1) |
| Round-key hoisting *in the fused bodies* | **win, folded in** | 1.8–7.2 points |
| ~50 instruction orderings of `s4h` | **`d5` wins** | −2.16…−2.39 % @64 B |
| Epilogue rejoin (one `ret` for nblk ≥ 1) | **free** | 0.02–0.06 points, −5 instructions |

---

## The finding that explains most of the negatives

**There is no separate GHASH pipe.** `aese`, `aesmc`, `pmull`, `eor` all contend for the
same 4 vector issue slots, so mixed cost is the **sum**, not the max. Two corollaries that
killed several ideas before they were built:

- Adjacent `aese`+`aesmc` **fuse** (4 pairs/cycle = 8 instructions/cycle). Breaking that
  adjacency to slot GHASH work between them *doubles* the AES cost.
- The binding resource is the **~78-µop vector issue queue**, not the ~320-entry reorder
  buffer. (I predicted a fall-through cascade would be ~3× slower by reasoning from ROB
  size. Measurement said otherwise; the queue is what runs out.)

The main loop is already at ~99 % of its issue-slot roofline. That is why every attempt to
find "idle GHASH capacity" inside it failed, and why all the wins are in the *fixed
per-call* phases — setup and tail — and therefore show up at short lengths and amortise
away by 4 KB.

---

## Q&A

### "I don't understand the analysis — I thought we could de-stagger outside the loop and have some gains"

The staggering isn't hiding a bubble. Measured the slot counts: the loop issues at ~99 % of
4 slots/cycle, so removing the one-group lag frees nothing. Building it means rewriting the
main loop, prepretail **and** tail together.
**Verdict: dead as specified.** `destagger-experiment-2026-08-14.md` §4.

### "isn't the prologue before the loop? if you change it, wouldn't that change the loop?"

Correct, and that was the right objection. The prologue's 8-block AES runs for *every*
length, so anything added there is paid by long messages too — and moving GHASH work in
needs spill space.
**Measured:** `p1_ilv` (7/8 of the exact-8 drain's GHASH interleaved into the prologue) is
a **real win at 128 B, −3.5…−3.9 %**, wash from 256 B up — but needs the frame to grow
**80 → 128 B**. The zero-growth variant (`p2_ilv`, pre-reduce and stash in the dead `Xi`
buffer) is KAT-clean but a **regression, +1.8…+4.2 % @256 B**.
**Verdict: declined** — frame growth changes the exported precondition and `MAYCHANGE`
footprint for a 128 B-only gain. `prologue-relocation-experiment-2026-08-14.md`.

### "I think you had a suggestion for an in-between optimisation, can the subagent try it?"

That was fusing the GHASH drain into PREPRETAIL instead of the prologue.
**Measured:** −0.4…−1.0 % @256 B for a *perfect free relocation* — but once the
algebraically required `T·H⁸` correction terms are counted it becomes **+0.9…+1.7 % on
V2/V3**. The full hand-scheduled version was not built; the ceiling doesn't justify it.
**Verdict: wash → small regression.** `prepretail-fusion-experiment-2026-08-14.md`.

### "can we pin the round keys in registers?"

**Measured: 0.00 ns.** Deleting all 8 key loads from the main loop changed nothing — they
aren't on the critical path there. (Note the *opposite* result in the fused small bodies
below; at small `nblk` the same loads do sit on the critical path.)
**Verdict: wash in the loop, win in the small path.** `destagger-experiment-2026-08-14.md` §5.

### "revisit the shelved benchmarking idea, but not only for 128 bytes — for any blocks ≤ 8"

Built eight fused entry points, `nblk = 1..8`, each doing AES and GHASH interleaved for
exactly *n* blocks, entered before the prologue's 8-block AES.
**Measured (GV4; V1/V3 within ~1.5 points):** −47 % @16 B, −43 % @32 B, −44 % @48 B,
−41 % @64 B, −36 % @80 B, −30 % @96 B, −24 % @112 B, −9.7 % @128 B. Wash ≥256 B. KAT 35/35
on four hosts; byte-compared over every whole-block length to 4 KB.
**Cost:** `.text` 4968 → 12376 B (**×2.49**) and eight new proved paths.
Also quantified: roughly half the win at 16 B is the fusion, half is skipping the dead AES
— fusion is worth a near-constant −5.1…−5.8 ns for every `nblk ≤ 7`, while skipping dead
AES decays from −5.2 ns at nblk=1 to −0.0 ns at nblk=8.
`fused-small-path-experiment.md`, `fused-truncation-curve.md`.

### "what's t4p8's cost in code size, proof paths and performance at every size?"  /  "is t4p8 a separate path for each size?"  /  "I don't want per-size paths"

`t4p8` kept bodies for {1,2,3,4,8} only — yes, one separate body per size.
**Measured:** −47/−43/−43/−41 % @16/32/48/64 B, **−9.9 % @128 B**, zero within noise at
80/96/112/256/4096 B. `.text` 4968 → 8832 B. Five new proved straight-line paths.
**Verdict: rejected on shape, not speed.** `fused-t4p8.md`.

### "what dead AES?" / "branch off before the 8 AES blocks to an entry point for the right size — no dead AES"

Confirmed by counting: the prologue issues 112 `aese` = 8 keystream blocks for *every*
length, and the tail cascade throws away `8 − nblk` of them, plus a `mov`-shuffle chain and
`8 − nblk` × `sub v30,v30,v31` to rewind the counter. Your branch-before-the-AES structure
gives exact-`n` with no dead AES — that became the design.

### "put it within the 8-block path, interleaving rounds for the first 4 blocks only" (`mix4s4`)

One 4-wide interleaved group of 4 blocks, then four sequential single-block sections with
their own entry labels; {5,6,7} and >8 fall back.
**Measured:** matches per-size bodies at 16/32 B, −31.3/−37.3/−39.7 @48 B,
−20.0/−25.9/−29.5 @64 B — but **128 B REGRESSES +21.0 / +18.0 / +13.3 %**.
**Mechanism, measured:** four sequential blocks *do* overlap in hardware, but incompletely.
The same work interleaved 4-wide costs 26/20/14 % less, and with no slack left a sequential
block costs ~11.7/9.8/9.4 cycles against 8.6/7.9/7.8 for a 4-wide one.
**Verdict: rejected.** `fused-mix4s4.md`.

### "compare 4-wide with dead AES for smaller blocks vs cascade 4→1 with no dead AES" (`g4` vs `s4h`)

**Measured:** `g4` (one 4-wide group serving all `nblk ≤ 4`, discarding unused lanes) loses
**22 / 20 / 13 points** at 16 / 32 / 48 B. The discarded AES really is nearly free
(+0.1…+1.9 cycles) — but the four GHASH lanes that must run regardless (+6.4 cyc) and the
branch-free masking (+6.6 cyc) sink it.
**Verdict: cascade wins.** `fused-g4.md`.

### "what's the difference between W=1 and W=4 cascades?" / "I prefer no separate paths"

W=4 over all 8 blocks regresses 128 B by +7 %. Capping a W=4 cascade at 4 blocks
degenerates into per-size bodies (10 AES blocks), which you'd ruled out. W=1 restricted to
`nblk ≤ 4` keeps exact-`n`, one region, no per-size code.
**Chosen: `s4h`** — four sections `.L_4/.L_3/.L_2/.L_1`, one block each with its 14 rounds,
GHASH product, `eor3` and store, falling through to a shared GHASH accumulate + MODULO +
tag + counter store; `nblk` 5–8 and >8 unchanged.
**Measured:** −47.1/−42.2/−31.3/−20.0 % (V1) at 16/32/48/64 B; `.text` ×1.20; frame stays
80 B. `fused-cascade-experiment.md`, `fused-mix4s4.md`.

### "is there a reordering that increases the 64 B win on V1? V1 is sensitive to ordering"

Right, and it was worth doing. ~50 orderings over 4 rounds, same instruction multiset each
time (the generator's defaults reproduce the shipped object bit-for-bit as a control).
**Winner `d5`:** ciphertext `ldr` becomes the section's first instruction; the 11 GHASH
product ops go out in three bursts of four (after AES units 0, 4, 9).
**Measured @64 B vs the shipped ordering:** **−2.16 (V1) / −1.91 (V2) / −2.12 (V3)** against
A/A floors of 0.05–0.29 %, each reproduced by its own A/A twin to ≤0.02 points.
Your K-split hunch was right — it is *not* flat on V1 (−1.50 % alone) — but it turned out to
be the same lever as clumping, and clumping is the stronger handle.
**Flat, don't revisit:** dispatch/taken-branch count (3→0 or 3→7: |Δ| ≤ 0.34 %), physical
section layout reversed (−0.34 %), end-relative static addressing (−0.13 %), the counter
chain (bounded above at −0.38 % by a diagnostic that deletes it), all-loads-at-head
(−0.0…−0.3 %), fold-late (+0.06 %). **Idempotent cross-section prefetch is structurally
void** — both copies write the same register, so renaming makes the early copy dead.
**Mechanism:** the whole gain sits in blocks 3 and 4 (V1 −0.50 and −0.60 cyc/block); blocks
1–2 hide in the first block's latency shadow, so ordering cannot matter there.
`fused-w1-reorder.md`.

### "did the code have 2 `ret`s before the extra path?"

Yes — lines 1519 and 1721 at HEAD, inherited from aws-lc: **all six** aws-lc 8x kernels
(enc/dec × 128/192/256) have exactly 2, as do our encrypt kernel and the untouched
originals. aws-lc's *x4* kernels have 1.
The fused region briefly made it 3; rejoining the shared epilogue put it back to 2.
**Measured cost of the rejoin: 0.02–0.06 points @64 B** (inside every A/A floor), and it is
5 instructions *smaller*. Driving it to 1 would mean moving the guards after the frame
push, which makes a zero-length call write 80 bytes below `sp` — a wider proved footprint,
so it was declined.

---

## Landed vs archived

**Chosen and handed to the prover:** `s4h` cascade + `d5` ordering + epilogue rejoin.
Applying `_docs/fused-w1-reorder/d5r.patch` to the `c2609cf8` kernel reproduces object md5
`968b7a2f0e89093da5d1961d978e4f44`; KAT 35/35; one `ret` for `nblk ≥ 1`; **−21.9 / −27.2 /
−31.0 % @64 B** vs HEAD on V1/V2/V3, wash ≥80 B.

**Archived with measurements, not queued:** per-size bodies, `t4p8`, `g4`, `mix4s4`, W=1
over all 8, prologue relocation (`p1_ilv`/`p2_ilv`), prepretail fusion, zero-lag
de-stagger, pinned round keys, exact-128 B fused path (`expA-fused8-K80.patch`).

## Two things that changed how we judge results

1. **aws-lc's `len >= 256` gate on 8x dispatch will be lowered**, so 128 B-only gains count
   as production wins. Judge changes on proof cost vs measured gain alone. Lowering it must
   be done **per direction** though: it's a clear win on decrypt but regresses `seal` by
   6–13 % at 16–64 B on encrypt.
2. **Always benchmark aws-lc against `upstream/main`,** not a release tag. Current upstream
   dispatches the 8x kernel on Neoverse-V3; a v1.68.0 tree does not, which silently makes
   GV5 look like it has no 8x path at all.
