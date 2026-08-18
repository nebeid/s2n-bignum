# A generalised fused small-message path for the AES-256-GCM decrypt kernel — measurement only

Kernel `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S` at local HEAD `14f9d9bb`
(md5 `6de404aca78da9799a911b126727c73f`, 1721 lines; byte-identical to
`ec2r8g:~/whole-proofs/s2n-bignum/…`, whose object md5
`114cedb51f36c584e50843d2838d871e` my build pipeline reproduces exactly).
**No HOL Light, no `.ml`, no proofs.** All work in `/tmp/fsp` on each host and
`/tmp/fsp` locally; no tracked file in any repo was modified; no instance was
stopped, started, rebooted or terminated.

Hosts, clocks measured on the spot (`clk.c`, dependent-add chain, two runs each):

| label | core | clock |
|---|---|---|
| GV3 | Neoverse-V1 `0xd40` | **2.5914 / 2.5909 GHz** |
| GV4 | Neoverse-V2 `0xd4f` | **2.7926 / 2.7922 GHz** |
| GV5 | Neoverse-V3 `0xd84` | **3.2907 / 3.2901 GHz** |
| r8g | Neoverse-V2 (dev)  | **2.7925 GHz** |

---

## 0. Headline

| | |
|---|---|
| **Does the prologue do dead AES for `nblk < 8`?** | **YES.** It issues 112 `aese` = 8 keystream blocks for *every* length, and the tail cascade *throws away* `8 − nblk` of them (a `mov`-shuffle chain plus `8 − nblk` × `sub v30,v30,v31` to rewind the counter). |
| **Was it built?** | **Yes — eight new fused entry points, `nblk = 1..8`.** KAT **35/35** on all four hosts; in-process byte-compare of `out`/`Xi`/`ivec`/return over **every** whole-block length 1..256 blocks against three independent kernels; 8/8 per-entry liveness probes exact; aws-lc `crypto_test` **2611 pass / 0 fail**. |
| **Kernel-level result vs our HEAD kernel** | **−47 % @16 B, −43 % @32 B, −44 % @48 B, −41 % @64 B, −36 % @80 B, −30 % @96 B, −24 % @112 B, −9.7 % @128 B** (GV4; V1 and V3 within ~1.5 points). **Wash at ≥256 B** (max \|Δ\| 0.37 %, inside the A/A floor). |
| **Kernel-level result vs aws-lc as shipped** | **−28 … −49 %** at every length 16–128 B on all three cores (aws-lc's own sub-256 B fallback is the reference below 256 B). |
| **Fusion vs skipping the dead AES** | Roughly **50/50 at 16 B** and the split moves with `nblk`: fusion + tail cleanup is worth a near-constant **−5.1 … −5.8 ns** for every `nblk ≤ 7` (−2.4 ns at `nblk = 8`); skipping the dead AES adds **−5.2 ns at nblk=1** decaying to **−0.0 ns at nblk=8**. Both effects are real and neither dominates. |
| **Stack frame** | **UNCHANGED at 80 bytes.** No new SIMD or GPR register is written, so the exported theorem's precondition and `MAYCHANGE` footprint are untouched. |
| **`nblk > 8` path** | **1240 of the kernel's 1242 instructions are instruction-for-instruction unchanged** (normalised `objdump`); the other 2 are the relocated `.L256_dec_ret` stub, also identical. Only 2 instructions are inserted and 1852 appended. |
| **Cost to declare** | `.text` grows **4968 → 12376 bytes (2.49×)**, and eight already-proven tail bands would be replaced by eight new proved straight-line paths. |
| **AEAD-level (production) reality check** | At 16–64 B the AEAD wrapper costs 85–110 ns/call, so the kernel win shrinks to **−7.6 … −11.8 % vs our HEAD** and **−1.3 … −2.6 % vs shipped aws-lc**; at 128 B on V2 it is **−8.0 % vs shipped**. |
| **New finding, unrelated to this change** | **aws-lc v1.68.0 never reaches the 8x kernel on Neoverse-V3 (Graviton5).** `CRYPTO_is_ARMv8_GCM_8x_capable()` allowlists only Neoverse-V1/V2/Apple-M, so on GV5 variants A, B and C are *identical at the AEAD level* and every GCM call takes the 4x fallback — which the kernel-level numbers show is **31 % slower at 4 KB**. Lowering the length threshold buys nothing on V3 until that allowlist is widened. |

---

## 1. The dead-AES question, answered precisely

### 1.1 Static reading of the baseline

`.S:58..371` is the prologue: 112 `aese` + 104 `aesmc` = **8 blocks of AES, always**.
`x5 = x0 + ((byte_len−1) & ~127)`, so for every `byte_len ≤ 128` the `cmp x0,x5`
at `:348` is an equality and the `b.ge .L256_dec_tail` at `:371` is taken —
after the full 8-block AES has issued.

In `.L256_dec_tail`, block 0 always consumes keystream `v0` (`:1228`), and the
cascade then *shifts the keystream registers down* so that the final block
always lands on `v7`:

| `nblk` | tail entry (first H power) | `mov`-shuffle levels run | keystream blocks discarded |
|---:|---|---:|---:|
| 8 | `.L256_dec_exact8_drain` (H⁸) | 0 | 0 |
| 7 | `.L256_dec_blocks_more_than_6` (H⁷) | 1 | 1 |
| 6 | `…more_than_5` (H⁶) | 2 | 2 |
| 5 | `…more_than_4` (H⁵) | 3 | 3 |
| 4 | `…more_than_3` (H⁴) | 4 | 4 |
| 3 | `…more_than_2` (H³) | 5 | 5 |
| 2 | `…more_than_1` (H²) | 6 | 6 |
| 1 | `…blocks_less_than_1` (H¹) | 7 | 7 |

Each discarded block also costs one `sub v30.4s, v30.4s, v31.4s` to rewind the
counter. So at `nblk = 1`, **98 of the 112 `aese` (7/8 of the AES), 7/8 of the
CTR setup, and 21 `mov`s + 7 `sub`s of pure shuffle are dead work.**

### 1.2 Baseline SIMD issue-slot budget per `nblk`

Counted with the established convention (adjacent `aese`+`aesmc` = 1 slot,
`.inst`-encoded `eor3` counted, loads/stores excluded), summing exactly the
regions each `nblk` traverses (`_docs/fused-small-path/slots.py`):

| `nblk` | pairs | lone `aese` | `pmull` | other vec ALU | **slots** | floor @4/cyc |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 104 | 8 | 5 | 78 | **195** | 48.75 |
| 2 | 104 | 8 | 8 | 87 | **207** | 51.75 |
| 3 | 104 | 8 | 11 | 94 | **217** | 54.25 |
| 4 | 104 | 8 | 14 | 101 | **227** | 56.75 |
| 5 | 104 | 8 | 17 | 106 | **235** | 58.75 |
| 6 | 104 | 8 | 20 | 111 | **243** | 60.75 |
| 7 | 104 | 8 | 23 | 114 | **249** | 62.25 |
| 8 | 104 | 8 | 26 | 88 | **226** | 56.50 |

Two things fall out, both confirmed by measurement:

* **The baseline is *more* expensive at 112 B than at 128 B** — 249 slots vs 226,
  because `nblk = 7` runs the generic cascade (mov-shuffle + a per-block
  partial-tag `eor`/`movi` pair) while `nblk = 8` runs the stripped exact-8
  drain. Measured GV4: **27.455 ns (76.7 cyc) at 112 B vs 25.362 ns (70.8 cyc)
  at 128 B.** The current kernel is non-monotone in length.
* Every row carries the same 112 slots of AES whatever `nblk` is.

---

## 2. What was built

### 2.1 Dispatch

Two instructions inserted immediately after `add x10, sp, #64` (`.S:56`), i.e.
after the frame and the MODULO-constant store, before any CTR/AES work:

```
	cmp	x9, #128				//[FUSE] nblk <= 8 ?
	b.le	.L256_dec_fused_small
```

`x9` is `byte_len` (`lsr x9,x1,#3`), and the whole-blocks contract guarantees
`16 ≤ x9`, so this is exactly `nblk ∈ 1..8`. A new region is appended before
`.L256_dec_ret`: a 3-deep balanced compare tree on `x9` (max 3 `cmp` + 3
branches for every entry) into eight straight-line bodies
`.L256_dec_fused_1 … _8`.

```
.L256_dec_fused_small:            cmp x9,#64 ; b.gt .L256_dec_fs_hi
                                  cmp x9,#32 ; b.gt .L256_dec_fs_34
                                  cmp x9,#16 ; b.eq .L256_dec_fused_1 ; b .L256_dec_fused_2
.L256_dec_fs_34:                  cmp x9,#48 ; b.eq .L256_dec_fused_3 ; b .L256_dec_fused_4
.L256_dec_fs_hi:                  cmp x9,#96 ; b.gt .L256_dec_fs_78
                                  cmp x9,#80 ; b.eq .L256_dec_fused_5 ; b .L256_dec_fused_6
.L256_dec_fs_78:                  cmp x9,#112; b.eq .L256_dec_fused_7 ; b .L256_dec_fused_8
```

### 2.2 One fused body, for exactly `n` blocks

Generated by `_docs/fused-small-path/gen.py` (anchor-matched, no line numbers):

1. **CTR setup for `n` blocks only** — `ld1 {v0.16b},[x16]`, `rev32 v29` base,
   increments `+2..+max(n−1,n)` built as a tree, `n−1` parallel
   `add`/`rev32` pairs for CTR blocks 1..n−1, and
   `add v30.4s, v29.4s, inc[n].4s` for the counter written back. All CTR temps
   are dead before AES round 0.
2. **AES rounds 0..13 for blocks 0..n−1**, emitted round-major so `aese`+`aesmc`
   adjacency is never broken (verified mechanically: **0 violations**), with the
   seven `ldp` round-key loads placed at the same points the baseline uses.
3. **GHASH of the same `n` blocks, interleaved into those AES units.** Block `i`
   uses `H^(n−i)`; the incoming tag is fed into block 0 only
   (`eor v8,v8,v16` with `v16 = ext(Xi',Xi',#8)`). Products go straight into the
   three accumulators for block 0 and are folded in pairs with `eor3`
   thereafter. Ciphertext is read with non-post-incrementing `ldr q9,[x0,#16i]`
   so `x0` stays put.
4. **MODULO reduce, tag store, counter store and an L1-hot ciphertext reload**
   interleaved into the remaining AES units.
5. `n` plaintext `eor3` + `stp`/`str` + the standard 80-byte frame pop + `ret`.

The GHASH schedule is front-loaded: GHASH occupies AES units `0..K−1` and the
MODULO + reload occupy `K..U−1`, with `U = 14n` units and `K = ⌈k·U⌉`.

**One micro-optimisation over the baseline and over `expA`:** the per-block
"k" value (the Karatsuba middle key) is fetched with a **64-bit `ldr d25`** at
`Htable + {168,160,120,112,72,64,24,16}` for `H^{8..1}` instead of loading the
16-byte pair and `ext`-ing it. That removes 4 SIMD ALU ops from the 8-block body
at zero cost (loads do not consume SIMD issue slots — established by the
destagger experiment's key-load ceiling probe).

### 2.3 Register allocation — identical for every entry point

| role | registers |
|---|---|
| AES states | `v0 … v(n−1)` |
| round keys | `v26, v27, v28` (`v28` becomes `rk14` for the final `eor3`) |
| counter | `v30` |
| GHASH working | `v8` block, `v9` ciphertext, `v10` mid operand, `v24` `H^p l\|h`, `v25` `H^p k` |
| GHASH products | `v11,v12,v13` (slot A) and `v14,v15,v20` (slot B) |
| accumulators | `v17` high, `v18` mid, `v19` low (also holds `Xi` during tag prep) |
| tag feed → MODULO constant | `v16` |
| CTR-setup temps (all dead before AES round 0) | `v29`, `v31`, `v20…v25`, `v17`, `v8…v14` |

Free SIMD registers *inside the interleaved region*, measured by the verifier:

| entry | `nblk`=1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| free regs | **14** | 11 | 9 | 8 | 7 | 6 | 5 | **4** |
| slots | 44 | 71 | 95 | 122 | 146 | 173 | 197 | 224 |
| floor @4/cyc | 11.0 | 17.8 | 23.8 | 30.5 | 36.5 | 43.3 | 49.3 | 56.0 |

Register pressure is never the binding constraint: even at `nblk = 8` there are
4 free (`v22,v23,v29,v31`) — one more than `expA` had, thanks to the `ldr d`
key fetch. **No spills anywhere, and the 80-byte frame is untouched.**
Slot counts fall from 195→44 at `nblk=1` and 226→224 at `nblk=8` (so at 128 B
this is essentially `expA` re-derived; the 224 vs `expA`'s 225 vs the baseline's
226 confirms it is the same work in a different order).

### 2.4 What did **not** change

Normalised `objdump` instruction-stream comparison of `base.o` vs `tuned.o`
(branch targets and addresses masked):

```
base 1242 instructions, tuned 3094
first divergence at instruction 14   (base: ld1  | tuned: cmp)
then 1226 more identical after skipping the 2 inserted instructions
base tail left 2 (the .L256_dec_ret stub) — identical, relocated after the new region
```

So the prologue, main loop, prepretail, tail dispatch, the whole 8-way cascade,
the exact-8 drain and the shared epilogue are **instruction-for-instruction
unchanged**; only their addresses shift by 8 bytes. Register footprint is
identical (SIMD `v0`–`v31` and GPRs `x0,x4,x5,x9,x10,x11,x15,x16` written by
both), and the frame is `stp d8,d9,[sp,#-80]!` / `ldp d8,d9,[sp],#80` in both.

**Code size: `.text` 4968 → 12376 bytes (+7408, ×2.49).** The
`fuse8` diagnostic variant is 15708 bytes. This is the one real non-proof cost
of the design and it is not visible in a microbenchmark; a real workload mixing
lengths would pay some I-cache/I-TLB pressure for it.

---

## 3. Correctness evidence

1. **Build-pipeline fidelity.** `mk.sh` reproduces `arm/Makefile`'s rule
   (`gcc -E -Iinclude -xassembler-with-cpp | tr ';' '\n' | as -march=armv8.2-a+sha3`)
   and its output for the pristine source is **byte-identical** to the object in
   the synced tree (`114cedb51f36c584e50843d2838d871e`) on all four hosts.
   Every variant is a full `.S` → `.o` → **fresh link**.
2. **Differential KAT gate**, genuine rebuild *and* relink
   (`gcc -O2 -o kat/kat_wb_dec kat/kat_wb_dec.c obj/tuned.o obj/ref.o`) against
   the trusted sibling `aesv8_gcm_8x_dec_256.o`:
   **35 passed, 0 failed — `KAT GATE: PASS`** on GV3, GV4, GV5 and r8g.
   `arm/aes-gcm/kat` was never touched and `make clean` was never run.
   *Note on "build through the top-level `arm/Makefile`":* the fused kernel
   cannot be put into the tracked tree without modifying it (and
   `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o` is itself a checked-in frozen
   object), so instead `mk.sh` reproduces `arm/Makefile`'s rule **verbatim** and
   the proof that this is the same build is the md5:
   `obj/base.o = 114cedb51f36c584e50843d2838d871e` = the object `arm/Makefile`
   produced in the synced tree, on all four hosts. The KAT binary is deleted and
   re-linked from `kat_wb_dec.c` + the fresh `.o` on every run, so a stale
   object cannot be tested.
3. **In-process byte-compare, run before every timing pass**, over **every
   whole-block length from 1 to 256 blocks (16 B … 4096 B)** — which includes
   each of `nblk = 1..8` explicitly, i.e. all eight new entry points — comparing
   `out`, `Xi`, `ivec` **and the return value** of all six linked variants:
   ```
   SELFCHECK OK (256 whole-block lengths 1..256 blk x 6 variants; out/Xi/ivec/ret byte-identical)
   ```
   This is an **absolute** check, not just differential: the harness builds a
   real AES-256 schedule with aws-lc's `aes_hw_set_encrypt_key`, computes
   `H = E_K(0)` with `aes_hw_encrypt` and fills a real `H^1..H^8` table with
   `gcm_init_v8` (aws-lc asm assembled read-only). With a consistent table the
   fused kernel is byte-compared against **three independent implementations**:
   our HEAD 8x kernel, aws-lc's shipped `aesv8_gcm_8x_dec_256`, and aws-lc's
   4x `aes_gcm_dec_kernel`. All four agree everywhere.
4. **Per-entry-point liveness probes** (the differential trick, stronger than
   `brk #0`). `zapN` replaces body `N`'s block-0 GHASH products with zeros —
   functionally wrong on purpose — and must break **exactly** `nblk == N`:
   ```
   zap1: nblk=1   zap2: nblk=2   zap3: nblk=3   zap4: nblk=4
   zap5: nblk=5   zap6: nblk=6   zap7: nblk=7   zap8: nblk=8
   ```
   Eight probes, eight single-length failures, no collateral failure at any
   other length. Each of the eight new entry points is therefore proved to be
   entered for exactly its own length, and its fused GHASH proved load-bearing.
   (The AES half is proved live by `out` being byte-identical at every length.)
5. **Static verifier** (`verify.py`): **0 `aese`/`aesmc` adjacency violations**
   in any body — the one scheduling constraint that would silently double AES
   cost.
6. **aws-lc's own tests, with the threshold patched to 16 and the fused kernel
   substituted** (variant C, GV4):
   * `crypto_test --gtest_filter=*GCM*:*gcm*:*AEAD*:*aead*` → **334 / 334 PASS**
   * full `crypto_test` → **2612 tests, 2611 passed, 0 failed** (1 skipped:
     `randTest.ReseedIntervalWhenUbeNotSupported`).

---

## 4. Kernel-level measurements (primary)

Discipline: all six variants `objcopy --redefine-sym`'d to distinct symbols and
linked into **one** binary; round-robin with the slot order rotated every rep;
`taskset -c 3`; 200-call warm-up per pass; **best of 120 reps × 3 processes**.
Absolute figures are the min over the three processes; Δ % are the **median of
the per-process best-deltas**. Slot 1 is `base` a second time: the **A/A floor**.

Slots: `base` = our HEAD kernel (**variant B**) · `baseAA` = A/A floor ·
`awslcfb` = aws-lc `aes_gcm_dec_kernel` (its shipped path below 256 B) ·
`awslc8x` = aws-lc `aesv8_gcm_8x_dec_256` (its shipped path at/above 256 B) ·
`tuned` = the new fused path (**variant C**) · `fuse8` = fused but with the
prologue's dead AES retained (diagnostic).

### 4.1 Absolute ns/call

**GV4 — Neoverse-V2, 2.7926 GHz**

| bytes | blk | base (B) | A/A | awslcfb | awslc8x | **tuned (C)** | fuse8 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 1 | 23.311 | 23.291 | 18.163 | 25.529 | **12.339** | 17.490 |
| 32 | 2 | 23.410 | 23.377 | 20.575 | 25.667 | **13.370** | 18.108 |
| 48 | 3 | 24.238 | 24.254 | 21.560 | 26.251 | **13.669** | 18.964 |
| 64 | 4 | 25.107 | 25.115 | 21.465 | 27.415 | **14.872** | 19.467 |
| 80 | 5 | 25.986 | 25.994 | 32.111 | 29.432 | **16.649** | 20.524 |
| 96 | 6 | 26.941 | 26.861 | 33.031 | 30.527 | **18.794** | 21.185 |
| 112 | 7 | 27.455 | 27.349 | 34.057 | 31.914 | **20.843** | 22.321 |
| 128 | 8 | 25.362 | 25.574 | 34.464 | 32.817 | **22.911** | 22.922 |
| 256 | 16 | 45.456 | 45.408 | 60.845 | 55.370 | 45.291 | 45.320 |
| 512 | 32 | 84.305 | 84.425 | 114.158 | 94.230 | 84.438 | 84.457 |
| 1024 | 64 | 161.958 | 161.958 | 220.761 | 171.742 | 162.046 | 161.631 |
| 4096 | 256 | 628.058 | 628.823 | 861.635 | 639.119 | 628.836 | 628.572 |

**GV3 — Neoverse-V1, 2.5914 GHz**

| bytes | blk | base (B) | A/A | awslcfb | awslc8x | **tuned (C)** | fuse8 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 1 | 26.153 | 26.201 | 20.248 | 28.791 | **13.882** | 19.425 |
| 32 | 2 | 26.443 | 26.495 | 21.696 | 29.135 | **14.843** | 20.581 |
| 48 | 3 | 27.637 | 27.723 | 23.310 | 30.050 | **15.467** | 21.687 |
| 64 | 4 | 28.914 | 28.882 | 23.832 | 31.412 | **17.055** | 22.705 |
| 80 | 5 | 29.956 | 29.980 | 35.725 | 32.977 | **19.531** | 23.854 |
| 96 | 6 | 30.909 | 30.857 | 37.372 | 35.687 | **21.543** | 24.813 |
| 112 | 7 | 31.810 | 31.690 | 38.273 | 37.284 | **24.622** | 26.158 |
| 128 | 8 | 30.093 | 29.901 | 39.310 | 38.789 | **27.112** | 27.122 |
| 256 | 16 | 52.189 | 52.343 | 69.347 | 62.140 | 51.989 | 52.068 |
| 512 | 32 | 94.704 | 95.147 | 130.428 | 104.641 | 94.440 | 94.469 |
| 1024 | 64 | 179.600 | 180.755 | 252.103 | 189.632 | 179.545 | 179.618 |
| 4096 | 256 | 692.726 | 694.343 | 983.514 | 700.206 | 692.201 | 690.990 |

**GV5 — Neoverse-V3, 3.2907 GHz** (the quiet host: A/A floor ≤ 0.02 %)

| bytes | blk | base (B) | A/A | awslcfb | awslc8x | **tuned (C)** | fuse8 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 1 | 19.621 | 19.624 | 15.671 | 21.686 | **10.532** | 15.152 |
| 32 | 2 | 19.639 | 19.641 | 17.754 | 21.777 | **11.337** | 16.062 |
| 48 | 3 | 20.356 | 20.358 | 18.410 | 22.143 | **11.186** | 16.365 |
| 64 | 4 | 20.948 | 20.950 | 18.309 | 22.609 | **12.156** | 16.671 |
| 80 | 5 | 21.601 | 21.604 | 26.802 | 23.601 | **13.602** | 17.578 |
| 96 | 6 | 22.378 | 22.377 | 27.852 | 24.896 | **15.639** | 18.187 |
| 112 | 7 | 22.833 | 22.846 | 28.400 | 25.886 | **17.526** | 18.607 |
| 128 | 8 | 21.449 | 21.457 | 28.557 | 26.452 | **19.736** | 19.737 |
| 256 | 16 | 38.167 | 38.169 | 50.566 | 44.350 | 38.170 | 38.167 |
| 512 | 32 | 71.089 | 71.112 | 94.921 | 78.215 | 71.124 | 71.116 |
| 1024 | 64 | 138.500 | 138.495 | 183.615 | 146.116 | 138.500 | 138.501 |
| 4096 | 256 | 546.860 | 546.860 | 716.964 | 554.798 | 546.836 | 546.835 |

r8g reproduces GV4 to within 0.2 % at every length (full table in
`_docs/fused-small-path/logs/kernel_tables.txt`).

### 4.2 Δ % vs our HEAD kernel, with the A/A noise floor

| bytes | GV3 A/A | **GV3 C** | GV4 A/A | **GV4 C** | GV5 A/A | **GV5 C** | r8g A/A | **r8g C** |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | +0.03 | **−47.04** | −0.09 | **−47.07** | +0.00 | **−46.31** | −0.05 | **−47.07** |
| 32 | +0.20 | **−43.87** | −0.10 | **−42.88** | −0.01 | **−42.28** | −0.15 | **−42.86** |
| 48 | −0.14 | **−44.28** | +0.02 | **−43.64** | +0.01 | **−45.04** | −0.04 | **−43.60** |
| 64 | −0.11 | **−41.01** | +0.07 | **−40.82** | +0.01 | **−41.97** | +0.04 | **−40.85** |
| 80 | +0.08 | **−34.40** | +0.03 | **−35.93** | +0.02 | **−37.03** | +0.02 | **−35.94** |
| 96 | −0.16 | **−30.11** | −0.08 | **−30.24** | −0.00 | **−30.12** | −0.01 | **−30.21** |
| 112 | −0.29 | **−22.38** | −0.27 | **−24.08** | +0.06 | **−23.26** | −0.35 | **−24.06** |
| 128 | −0.21 | **−9.87** | +0.80 | **−9.72** | +0.02 | **−7.99** | +0.77 | **−9.63** |
| 256 | +0.30 | +0.01 | −0.11 | −0.32 | +0.02 | +0.01 | −0.02 | −0.37 |
| 512 | +0.67 | −0.32 | +0.05 | +0.02 | +0.01 | +0.02 | −0.09 | −0.08 |
| 1024 | +0.81 | −0.01 | +0.05 | +0.07 | −0.01 | +0.00 | −0.05 | +0.01 |
| 4096 | +0.11 | −0.25 | +0.01 | +0.04 | −0.00 | +0.00 | +0.01 | +0.02 |

**Nothing at ≥256 B is outside the floor.** The known systematic +0.28 %
placement bias at 128 B on V2/r8g shows up here as +0.80 %/+0.77 %, and the
512 B/1024 B floor on GV3 is +0.67 %/+0.81 % as history predicts — every
`≥256 B` delta for the fused variant is smaller in magnitude than its own host's
floor at that length, so **≥256 B is a measured wash, not a measured win.**
The 128 B result (−9.6 … −9.9 % on V1/V2, −8.0 % on V3) reproduces
`expA-fused8-K80` (−9.30/−9.86/−8.59) as expected: at `nblk = 8` there is no
dead AES and the new body is `expA` re-derived.

### 4.3 vs aws-lc as shipped (its fallback below 256 B, its 8x kernel at/above)

| bytes | GV3 shipped | GV3 fused | Δ | GV4 shipped | GV4 fused | Δ | GV5 shipped | GV5 fused | Δ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 16 | 20.248 | 13.882 | **−31.5 %** | 18.163 | 12.339 | **−32.2 %** | 15.671 | 10.532 | **−33.0 %** |
| 32 | 21.696 | 14.843 | **−33.8 %** | 20.575 | 13.370 | **−35.0 %** | 17.754 | 11.337 | **−36.2 %** |
| 48 | 23.310 | 15.467 | **−33.7 %** | 21.560 | 13.669 | **−36.6 %** | 18.410 | 11.186 | **−39.3 %** |
| 64 | 23.832 | 17.055 | **−28.5 %** | 21.465 | 14.872 | **−30.7 %** | 18.309 | 12.156 | **−33.7 %** |
| 80 | 35.725 | 19.531 | **−45.5 %** | 32.111 | 16.649 | **−48.2 %** | 26.802 | 13.602 | **−49.3 %** |
| 96 | 37.372 | 21.543 | **−42.2 %** | 33.031 | 18.794 | **−43.1 %** | 27.852 | 15.639 | **−43.9 %** |
| 112 | 38.273 | 24.622 | **−35.5 %** | 34.057 | 20.843 | **−38.8 %** | 28.400 | 17.526 | **−38.3 %** |
| 128 | 39.310 | 27.112 | **−31.0 %** | 34.464 | 22.911 | **−33.5 %** | 28.557 | 19.736 | **−30.9 %** |
| 256 | 62.140 | 51.989 | −16.3 % | 55.370 | 45.291 | −18.2 % | 44.350 | 38.170 | −14.0 % |
| 512 | 104.641 | 94.440 | −9.8 % | 94.230 | 84.438 | −10.4 % | 78.215 | 71.124 | −9.2 % |
| 1024 | 189.632 | 179.545 | −5.3 % | 171.742 | 162.046 | −5.7 % | 146.116 | 138.500 | −5.3 % |
| 4096 | 700.206 | 692.201 | −1.1 % | 639.119 | 628.836 | −1.7 % | 554.798 | 546.836 | −1.4 % |

The ≥256 B column is our *existing* HEAD optimisation showing up against
aws-lc's unmodified 8x kernel, not this change. The jump at 80 B is aws-lc's
4x fallback crossing into its own main loop (5 blocks = 1 iteration + tail).

Two observations worth carrying to upstream:

* **Below 80 B our current HEAD 8x kernel is *slower* than the fallback
  aws-lc already ships** (16 B GV4: 23.311 vs 18.163 ns, i.e. +28 %). That is
  the concrete justification for the `len >= 256` gate as it stands, and it is
  exactly what this change removes: the fused path beats the fallback by
  28–49 % at *every* length 16–128 B on all three cores.
* aws-lc's shipped 8x kernel is slower than our HEAD everywhere
  (+8 … +29 % at 16–128 B, +1.5 … +22 % above), reconfirming the earlier
  runtime-optimisation arc.

### 4.4 Separating fusion from skipping the dead AES

`fuse8` is the new fused body generated with `n_aes = 8, n_ghash = n`: same
interleaved schedule, same stripped tail, but the prologue's full 8-block AES
and CTR setup are retained, exactly as today. So

* `base → fuse8` = **fusion (+ replacing the cascade with a straight-line
  tail)**, at unchanged AES cost;
* `fuse8 → tuned` = **skipping the dead AES and CTR work** alone.

GV4, ns/call (min of 3 processes):

| `nblk` | base | fuse8 | tuned | fusion Δ | dead-AES Δ | blocks skipped |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 23.311 | 17.490 | 12.339 | **−5.82** | **−5.15** | 7 |
| 2 | 23.410 | 18.108 | 13.370 | −5.30 | −4.74 | 6 |
| 3 | 24.238 | 18.964 | 13.669 | −5.27 | −5.30 | 5 |
| 4 | 25.107 | 19.467 | 14.872 | −5.64 | −4.60 | 4 |
| 5 | 25.986 | 20.524 | 16.649 | −5.46 | −3.88 | 3 |
| 6 | 26.941 | 21.185 | 18.794 | −5.76 | −2.39 | 2 |
| 7 | 27.455 | 22.321 | 20.843 | −5.13 | −1.48 | 1 |
| 8 | 25.362 | 22.922 | 22.911 | −2.44 | −0.01 | 0 |

In % (median of per-process best-deltas vs `base`), `fuse8` is
**−25.5/−25.0/−22.8 % at 16 B** and **−17.8/−18.7/−18.5 % at 112 B** on
V1/V2/V3, versus `tuned`'s −47/−47/−46 % and −22/−24/−23 %.

**Answer: both effects pay, and neither is a rounding error.**
Fusion (with the tail cleanup it enables) is worth a near-constant
**−5.1 … −5.8 ns for every `nblk ≤ 7`** — larger than the −2.44 ns it buys at
`nblk = 8`, because for `nblk < 8` it also deletes the cascade's `mov`-shuffle
and its per-block partial-tag `eor`/`movi` pairs. Skipping the dead AES is
worth **−5.15 ns at `nblk = 1`**, decaying monotonically (bar one 0.7 ns wobble
at `nblk = 3`) to zero at `nblk = 8`. At 16 B the split is almost exactly 50/50.

Note the dead-AES saving is strongly **sublinear** in blocks skipped
(7 blocks → 5.15 ns, 1 block → 1.48 ns, i.e. 0.74 vs 1.48 ns per block). The
reason is the AES round chain: skipping 7 blocks removes 98 issue slots
(24.5 cyc of issue) but cannot shorten the 14-round dependency chain, which
becomes the binding constraint. Slot arithmetic confirms this — `nblk = 1` goes
from 195 slots (48.75 cyc floor) to 44 slots (11.0 cyc floor) but measures
34.5 cyc, i.e. **3.1× its issue floor**, because it is latency-bound.

### 4.5 Where the `nblk = 1` fused path actually sits

Microbenchmark of the AES round chain (`aeslat.c`, `taskset -c 3`):

| host | 1 stream: ns per fused `aese`+`aesmc` pair | 8 streams: ns/pair | cyc/pair, 1 stream |
|---|---:|---:|---:|
| GV3 (V1) | 1.0485 | 0.0966 | 2.72 |
| GV4 (V2) | 0.7176 | 0.0897 | **2.00** |
| GV5 (V3) | 0.6089 | 0.1022 | **2.00** |

14 rounds of serial latency is therefore **10.05 ns on V2** and **8.52 ns on
V3**. The fused 16 B call measures **12.339 ns (V2)** and **10.532 ns (V3)** —
i.e. **2.0–2.3 ns above the irreducible AES dependency chain**, which is the
`ivec` load, the 3-branch dispatch, the final `eor3`/`str` and the call itself.
There is essentially nothing left at `nblk = 1`. (V1's 1-stream figure is an
over-estimate: 14 × 1.0485 = 14.68 ns exceeds the 13.88 ns measured in situ, so
treat 2.72 cyc/round as an upper bound on V1.)

### 4.6 Schedule tuning (the `K` sweep)

`K` = the AES-unit index at which GHASH stops and the MODULO/reload start.
Swept at `k ∈ {0.10,0.15,0.20,0.25,0.30,0.35,0.45,0.50,0.60,0.70,0.85}`
uniformly across all eight bodies, r8g, 50–60 reps (all KAT 35/35, all
selfcheck-clean). Best-per-`n` and the spread across the whole sweep:

| `nblk` | best `k` | best ns | worst ns in sweep | spread |
|---:|---:|---:|---:|---:|
| 1 | flat (0.15–0.60) | 12.145 | 12.501 | 2.9 % |
| 2 | 0.30 | 13.319 | 13.540 | 1.7 % |
| 3 | 0.45 | 13.679 | 13.768 | 0.7 % |
| 4 | 0.25–0.30 | 14.769 | 15.588 | 5.5 % |
| 5 | 0.45 | 16.636 | 17.505 | 5.2 % |
| 6 | 0.35–0.45 | 18.789 | 20.077 | 6.9 % |
| 7 | 0.45 | 20.846 | 21.688 | 4.0 % |
| 8 | **0.70** | 22.941 | 23.784 | 3.7 % |

The shipped variant uses `k = (0.45, 0.30, 0.45, 0.30, 0.45, 0.45, 0.45, 0.70)`.
The trend is the predicted one and it is the *opposite* of `expA`'s: small `n`
wants GHASH front-loaded **harder** (`k ≈ 0.3–0.45`) because with few AES units
the 14-cycle MODULO chain has to start early or it becomes the critical path;
`n = 8` reproduces `expA`'s `K = 80/112 ≈ 0.71` plateau. Sensitivity is only
1–7 %, so the schedule is not delicate.

---

## 5. AEAD-level measurements (`bssl speed`)

Three complete aws-lc v1.68.0 Release builds per host:

| variant | build |
|---|---|
| **A** | pristine aws-lc as shipped (`len >= 256`, its own kernels) |
| **B** | our HEAD kernel substituted for `aesv8_gcm_8x_dec_256`, `len >= 16` |
| **C** | the new fused kernel substituted, `len >= 16` |

Substitution method: the shipped `aesv8_gcm_8x_dec_256` is renamed
`…_SHIPPED` inside
`generated-src/linux-aarch64/crypto/fipsmodule/aesv8-gcm-armv8-unroll8.S` and
our preprocessed kernel is appended to that same file with its labels prefixed
(`.L256_dec_` → `.L256_decWB_`) and its symbol renamed to
`aesv8_gcm_8x_dec_256`. Verified in the built library:
`aesv8_gcm_8x_dec_256` has size `0x3058` = **12376 bytes = exactly our
`tuned.o` `.text`**, and `aesv8_gcm_8x_dec_256_SHIPPED` is present at 4608
bytes. No CMake or source-list change was needed.

Threshold patch: `crypto/fipsmodule/modes/gcm.c`, `sed 's/len >= 256/len >= 16/'`
— exactly the two sites (`hw_gcm_encrypt:164`, `hw_gcm_decrypt:201`), asserted
by the script. **The whole-blocks contract is preserved**: both functions
compute `len_blocks = len & kSizeTWithoutLower4Bits` and pass `len_blocks * 8`
bits, return early when `len_blocks == 0` (so `len < 16` never reaches the
kernel), and return `len_blocks` so the caller's existing code handles the
sub-block remainder. Only whole-block lengths reach the 8x kernel. Confirmed by
the 2611-test `crypto_test` pass.

`./tool/bssl speed -filter AEAD-AES-256-GCM -chunks 16,32,64,128,256,512,1024,4096
-timeout_ms 250`, `taskset -c 3`, 5 reps with the variant order cycled per rep,
min taken. `AEAD-AES-256-GCM-SIV` and the `-TLS12`/`-TLS13` rows are discarded
by **exact name match** in the parser. AD = 13 bytes (`kTLSADLen`).

### 5.1 ns/op, `open` (= DECRYPT — the direction this kernel serves)

**GV4 — Neoverse-V2**

| variant | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| A shipped | 99.4 | 100.5 | 100.9 | 116.7 | 142.5 | 188.6 | 262.3 | 729.6 |
| B HEAD, thr 16 | 104.9 | 106.4 | 109.3 | 109.9 | 132.4 | 174.1 | 251.6 | 718.4 |
| **C fused, thr 16** | **96.8** | **98.0** | **99.6** | **107.4** | **132.3** | **173.8** | **251.7** | **718.4** |
| C vs A | −2.6 % | −2.4 % | −1.3 % | **−8.0 %** | −7.2 % | −7.8 % | −4.0 % | −1.5 % |
| C vs A, ns | −2.5 | −2.4 | −1.3 | −9.3 | −10.2 | −14.8 | −10.6 | −11.2 |
| C vs B | **−7.6 %** | **−7.9 %** | **−8.8 %** | −2.2 % | −0.1 % | −0.2 % | +0.0 % | −0.0 % |
| rep spread (A) | 1.3 % | 0.9 % | 1.0 % | 0.9 % | 0.6 % | 0.6 % | 0.1 % | 0.1 % |

**GV3 — Neoverse-V1**

| variant | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| A shipped | 109.8 | 111.3 | 113.4 | 132.7 | 164.8 | 215.1 | 302.5 | 816.9 |
| B HEAD, thr 16 | 120.5 | 122.6 | 125.5 | 126.5 | 155.2 | 207.6 | 294.1 | 812.7 |
| **C fused, thr 16** | **107.8** | **108.8** | **110.8** | 126.7 | 156.1 | 210.5 | 296.3 | 809.5 |
| C vs A | −1.9 % | −2.3 % | −2.3 % | −4.5 % | −5.3 % | −2.1 % | −2.1 % | −0.9 % |
| C vs B | **−10.6 %** | **−11.2 %** | **−11.8 %** | +0.2 % | +0.6 % | +1.4 % | +0.8 % | −0.4 % |
| rep spread (A) | 2.0 % | 2.1 % | 2.0 % | 1.5 % | 1.5 % | 1.3 % | 1.2 % | 0.6 % |

GV3's 128 B row is the one place where the AEAD harness fails to resolve a
kernel-level effect: the kernel measurement says C should be 2.98 ns faster
than B at 128 B, but the AEAD numbers put them level (+0.2 %) with a 1.5 %
(≈ 2 ns) rep-to-rep spread. That row is inside GV3's AEAD noise; the 16–64 B
rows (−10.6 … −11.8 %, i.e. 12–15 ns) are far outside it.

**Absolute ns matter here, as warned.** The AEAD wrapper's fixed cost is
84–110 ns/call, so a 11 ns kernel saving at 16 B is a 2.6 % AEAD-level saving
even though it is a 47 % kernel-level saving. The right reading is the **ns
column**: C recovers 1.3–2.6 ns at 16–64 B against shipped aws-lc, and
9–15 ns at 128 B–4 KB (most of the latter being our pre-existing HEAD
optimisation, not this change).

### 5.2 `seal` (= encrypt) — context only

Both threshold sites were patched, so in B and C the *encrypt* direction also
starts using aws-lc's own unmodified 8x **enc** kernel below 256 B. That kernel
is slower than aws-lc's fallback there, so seal **regresses +8.3 … +12.9 % at
16–64 B** in B and C alike (B ≡ C on the seal side to within 0.5 %). This is a
property of the *threshold patch* applied to the un-optimised enc kernel, not
of anything in this experiment — and it is a concrete argument that lowering the
gate should be done per-direction, or paired with the same treatment for
encrypt. Full tables in `_docs/fused-small-path/logs/aead_tables.txt`.

### 5.3 Neoverse-V3: the 8x path is unreachable in aws-lc v1.68.0

On GV5 variants A, B and C measured **identical at every length in both
directions** (max \|Δ\| 0.3 %, inside the 0.8 % rep spread). Cause found in
`crypto/fipsmodule/cpucap/internal.h:239`:

```c
OPENSSL_INLINE int CRYPTO_is_ARMv8_GCM_8x_capable(void) {
  return (CRYPTO_is_ARMv8_SHA3_capable() &&
          ((OPENSSL_armcap_P & ARMV8_NEOVERSE_V1) != 0 ||
           (OPENSSL_armcap_P & ARMV8_NEOVERSE_V2) != 0 ||
           (OPENSSL_armcap_P & ARMV8_APPLE_M) != 0));
}
```

**Neoverse-V3 (`0xd84`, Graviton5) is not in the allowlist**, so *no* GCM call
on GV5 reaches any 8x kernel, at any length, in any of the three builds — and
the kernel-level table shows that fallback is 31 % slower than the 8x kernel at
4 KB (716.96 vs 546.86 ns) and 24–49 % slower than the fused path at 16–128 B.
Lowering the length threshold is worth nothing on V3 until that predicate is
widened; the two changes are independent and both are needed. To obtain V3
numbers at all I rebuilt A/B/C on GV5 with the predicate relaxed to
`return CRYPTO_is_ARMv8_SHA3_capable();` — see §5.4.

### 5.4 GV5 with the allowlist relaxed — and what that alone is worth

A/B/C rebuilt on GV5 with `CRYPTO_is_ARMv8_GCM_8x_capable()` relaxed to
`return CRYPTO_is_ARMv8_SHA3_capable();` (`awslc_v3.sh`). ns/op, `open`
(decrypt), 5 reps, min:

| variant | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| A shipped kernels, 8x enabled, `len>=256` | 83.9 | 85.4 | 85.6 | 96.4 | 118.3 | 151.8 | 220.0 | 628.4 |
| B HEAD, thr 16 | 86.6 | 88.3 | 90.2 | 90.4 | 108.2 | 142.0 | 210.3 | 618.8 |
| **C fused, thr 16** | **82.8** | **83.6** | **83.7** | **88.4** | 108.3 | 142.2 | 210.4 | 618.7 |
| C vs A | −1.4 % | −2.2 % | −2.2 % | **−8.3 %** | −8.4 % | −6.3 % | −4.3 % | −1.5 % |
| C vs A, ns | −1.2 | −1.8 | −1.9 | −8.0 | −10.0 | −9.6 | −9.6 | −9.7 |
| C vs B | **−4.5 %** | **−5.3 %** | **−7.2 %** | −2.2 % | +0.1 % | +0.1 % | +0.0 % | −0.0 % |
| rep spread (A) | 1.1 % | 0.7 % | 0.6 % | 0.8 % | 1.0 % | 1.0 % | 0.7 % | 0.3 % |

Comparing this table's A row with §5.1's GV5 A row isolates the value of the
capability fix on its own, with *no* kernel or threshold change:

| bytes | 16 | 32 | 64 | 128 | 256 | 512 | 1024 | 4096 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| aws-lc as shipped (8x dead on V3) | 84.2 | 85.3 | 85.5 | 96.8 | 119.2 | 163.5 | 252.5 | 786.6 |
| same, 8x allowlist widened to V3 | 83.9 | 85.4 | 85.6 | 96.4 | 118.3 | 151.8 | 220.0 | 628.4 |
| Δ | −0.4 % | +0.1 % | +0.1 % | −0.4 % | −0.8 % | **−7.2 %** | **−12.9 %** | **−20.1 %** |

**Adding Neoverse-V3 to the `CRYPTO_is_ARMv8_GCM_8x_capable` allowlist is worth
up to −20 % at 4 KB at the AEAD level on Graviton5, with no other change.**
That is a larger production win than anything in this experiment and it is
orthogonal to it.

### 5.5 GV3 re-run with 8 reps × 500 ms

To test whether GV3's 128 B row was noise, the whole GV3 AEAD grid was re-run at
8 reps × 500 ms (`logs/aead_GV3b.txt`). It reproduces:
16/32/64 B `C vs B` = **−11.3 / −11.8 / −12.5 %** (vs −10.6/−11.2/−11.8 % in the
first run) — clean and outside the 1.8–1.9 % spread; 128 B `C vs B` = −0.5 %
(was +0.2 %), still inside the 1.6 % spread. GV3's AEAD harness also compresses
the *known* B-vs-A kernel delta at 128 B (expects −9.2 ns from the kernel table,
measures −5.4 ns), so treat GV3's ≥128 B AEAD rows as under-resolving and use
its kernel-level numbers instead. GV3's 16–64 B rows are the largest AEAD-level
`C vs B` effects seen on any host.

---

## 6. Verdict per length band

| band | `nblk` | kernel-level vs our HEAD | kernel-level vs shipped aws-lc | AEAD-level vs shipped | verdict |
|---|---:|---|---|---|---|
| 16–64 B | 1–4 | **−41 … −47 %** (11–12 ns) | **−28 … −39 %** | −1.3 … −2.6 % (1.3–2.6 ns) | **large, unambiguous win**; at `nblk=1` the fused path is within 2.0–2.3 ns of the irreducible 14-round AES latency, so this band is essentially finished |
| 80–112 B | 5–7 | **−22 … −37 %** (5–10 ns) | **−35 … −49 %** | (not separately resolved) | **large win**; also removes the baseline's non-monotonicity (112 B was slower than 128 B) |
| 128 B | 8 | **−8.0 … −9.9 %** (1.7–3.0 ns) | **−31 … −34 %** | −4.5 … −8.0 % | **real win, = `expA` re-derived**; nothing new, but it comes free with the generalisation |
| 256 B – 4 KB | ≥16 | **0 %** — max \|Δ\| 0.37 %, below every host's own A/A floor at those lengths | −1.1 … −18 % (that is our *existing* HEAD optimisation) | −0.9 … −7.8 % (ditto) | **measured wash. No claim.** The `nblk>8` code is instruction-identical, so this is as it should be |
| seal (encrypt) 16–64 B | — | untouched | — | **+5.7 … +12.9 % regression** caused by the *threshold patch* hitting aws-lc's un-optimised 8x enc kernel | patch the gate per-direction, or optimise encrypt's small path too |
| Neoverse-V3, AEAD, as shipped | any | — | — | **exactly 0 %** — the 8x path is not reachable in v1.68.0 | needs the `CRYPTO_is_ARMv8_GCM_8x_capable` allowlist widened as well |
| Neoverse-V3, AEAD, allowlist widened | 1–8 | — | — | **−1.4 … −8.3 %** vs shipped kernels; −4.5 … −7.2 % vs our HEAD at 16–64 B | win, and widening the allowlist is separately worth **−20 % at 4 KB** |

**Costs to weigh against this**, all measured or exact:

* `.text` **4968 → 12376 bytes (×2.49)** — eight straight-line bodies. Not
  visible in a microbenchmark; a length-mixing workload would pay some
  I-cache/I-TLB for it.
* Proof surface: **eight new proved straight-line paths** would replace the
  eight existing tail bands. Each is a fully interleaved AES+GHASH simulation
  with a live accumulator and a MODULO close — the class of work that
  `task4-fused-short-path-investigation.md` costed as `WBN_MAIN_LOOP`-class,
  though this time the *dispatch* is trivial and the `nblk>8` machine code is
  provably unchanged, so no downstream band needs re-deriving beyond a uniform
  PC shift.
* **No change** to the frame (80 bytes), the register footprint, the memory
  footprint, or the exported statement.

---

## 7. Artifacts

All under `_docs/fused-small-path/` (gitignored path). Live scratch copies
remain in `/tmp/fsp` on GV3, GV4, GV5, r8g and locally.

| file | contents |
|---|---|
| `fused-small-path.patch` | **the variant measured as C** (vs pristine `.S`): entry test + dispatch tree + eight fused bodies, `k = 0.45,0.30,0.45,0.30,0.45,0.45,0.45,0.70` |
| `fused-small-fuse8.patch` | the `fuse8` diagnostic (fusion only, dead AES retained) |
| `gen.py` | generator: emits any `(n_aes, n_ghash, k)` schedule from the pristine `.S` by anchor matching, `eor3` as verified `.inst` words, `--zap N` liveness probes |
| `verify.py` | static checks: `aese`/`aesmc` adjacency, per-body slot counts, per-body free-register counts |
| `slots.py` | baseline SIMD-slot budget per `nblk` (the §1.2 table) |
| `bench.c` | 8-slot single-binary harness: real AES-256 schedule + real `H^1..H^8` via aws-lc asm, byte-compare over all 256 whole-block lengths, then order-rotated best-of-N over 12 sizes |
| `mk.sh`, `kat.sh`, `build_bench.sh`, `run.sh`, `provision.sh`, `measure.sh` | `.S`→`.o` (byte-identical to `arm/Makefile`), KAT relink, benchmark relink, drivers |
| `awslc.sh`, `awslc_v3.sh`, `aead.sh`, `aead_v3.sh` | aws-lc variant builds (threshold patch + kernel substitution; `_v3` also relaxes the 8x capability allowlist) and the `bssl speed` runners |
| `analyze.py`, `aead_analyze.py` | table generation (exact-name AEAD filter) |
| `clk.c`, `aeslat.c` | clock measurement; AES round-chain latency / throughput microbenchmark |
| `logs/{GV3,GV4,GV5,r8g}.log` | kernel-level runs, 3 processes × 120 reps |
| `logs/aead_{GV3,GV4,GV5,GV5v3,GV3b}.txt` | raw `bssl speed` output |
| `logs/kernel_tables.txt`, `logs/aead_tables.txt`, `logs/baseline_slots.txt`, `logs/verify_tables.txt` | generated tables |
