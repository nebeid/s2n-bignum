# Htable Lane-Exchange Analysis

## Terminology

A 128-bit polynomial in a NEON register has two 64-bit lanes:

- **Natural polynomial order**: `d[0]` = low 64 coefficients (x⁰..x⁶³),
  `d[1]` = high 64 coefficients (x⁶⁴..x¹²⁷). This is the order where
  `pmull` on `d[0]` gives the low×low product.

- **Lanes-exchanged**: `d[0]` = high coefficients, `d[1]` = low
  coefficients. Produced by applying `ext v, v, #8` to natural order
  (or vice versa).

The `ext v, v, v, #8` instruction swaps between these two layouts.

## How data blocks arrive

GCM blocks are big-endian in memory. On little-endian aarch64, `ld1 {v.2d}`
loads bytes 0–7 (MSB) into `d[0]` and bytes 8–15 (LSB) into `d[1]`.

`rev64` reverses bytes within each 64-bit lane, putting bits into
polynomial order within each lane. But the MSB half is still in `d[0]`
and the LSB half in `d[1]`. Since the low polynomial coefficients come
from the LSB half (bytes 8–15), they end up in `d[1]` (the high lane).

Therefore:
- `rev64` alone → **lanes-exchanged** (low poly coefficients in high lane)
- `rev64` + `ext #8` → **natural polynomial order** (low poly in low lane)

## gcm_init_v8 (ghashv8-armx.S, line 16)

### Twist computation

The twist (shift-left-by-1 with conditional reduction) produces H in
**natural polynomial order**: `d[0]` = low coefficients, `d[1]` = high.

### Lane exchange before storing

Init applies `ext #8` before every store, converting to **lanes-exchanged**:

```asm
eor  v20, v3, v16              // twisted H — natural order
ext  v20, v20, v20, #8         // → lanes-exchanged
st1  {v20}, [x0], #16          // store Htable[0]
```

Same pattern for H²..H⁸: each result is `ext #8`'d before storing
(via v22, v23, v25, v26, v28, v29, v31).

### Redundant exchange in H² computation

The stored (lanes-exchanged) v20 is immediately used to compute H².
The first step of that computation is:

```asm
ext  v16, v20, v20, #8         // Karatsuba pre-processing: back to natural!
```

So init exchanges the lanes, then immediately exchanges back for the
next computation. This round-trip costs one `ext` per H power and
saves nothing.

### Karatsuba middle terms

`mid(H^k) = xor(H^k_lo, H^k_hi)` — two middle terms are packed into
a single 128-bit slot via `ext`:

```asm
ext  v21, v16, v17, #8    // v21.d[0] = mid(H^k), v21.d[1] = mid(H^{k+1})
st1  {v21}, [x0], #16     // one 128-bit store
```

This halves the memory and loads needed (6 middle terms for H¹..H⁸
fit in 3 slots instead of 6). Consumers access each half via
`pmull` (low lane → `mid(H^k)`) or `pmull2` (high lane → `mid(H^{k+1})`).

The middle terms themselves are lane-order agnostic since
`H_lo ⊕ H_hi = H_hi ⊕ H_lo`.

### Htable layout

Stored in groups of 3 entries:
`[lanes-exchanged(H^k), pack(mid(H^k), mid(H^{k+1})), lanes-exchanged(H^{k+1})]`

12 entries total for H¹..H⁸.

## gcm_gmult_v8 (ghashv8-armx.S, line 201)

Single-block GHASH multiply. Converts both H and data to natural order:

```asm
ld1  {v20, v21}, [x1]          // load H (lanes-exchanged) and mid
ext  v20, v20, v20, #8         // → natural order
...
rev64  v17, v17                // data: byte-reverse within lanes
ext  v3, v17, v17, #8          // → natural order
```

Then `pmull v0, v20.1d, v3.1d` (low×low) and `pmull2 v2, v20.2d, v3.2d`
(high×high) operate on matching lanes.

## gcm_ghash_v8 — 2x loop (ghashv8-armx.S, line 245)

Converts H, H² and data to natural order:

```asm
ld1  {v20, v21}, [x1], #32     // load H (lanes-exchanged), mid
ext  v20, v20, v20, #8         // → natural order
ld1  {v22}, [x1]               // load H² (lanes-exchanged)
ext  v22, v22, v22, #8         // → natural order
...
rev64  v16, v16                // data block
ext  v3, v16, v16, #8          // → natural order
```

## gcm_ghash_v8_4x (ghashv8-armx.S, line 380)

Converts H, H², H³, H⁴ and data to natural order:

```asm
ld1  {v20, v21, v22}, [x1], #48  // load H, mid, H²
ext  v20, v20, v20, #8           // → natural order
ext  v22, v22, v22, #8           // → natural order
ld1  {v26, v27, v28}, [x1]       // load H³, mid, H⁴
ext  v26, v26, v26, #8           // → natural order
ext  v28, v28, v28, #8           // → natural order
...
rev64  v4, v4                    // data blocks
ext  v3, v16, v16, #8            // → natural order
```

4 `ext` instructions to convert H powers, plus 1 `ext` per data block.

## aesv8_gcm_8x (aesv8-gcm-armv8-unroll8.S, line 16)

Works entirely in **lanes-exchanged** order. Does NOT convert anything:

```asm
ldr  q25, [x6, #176]           // load H⁸ (lanes-exchanged, used as-is)
...
rev64  v8, v8                   // data: rev64 only → lanes-exchanged
```

Both H and data are lanes-exchanged, so `pmull` gets high coefficients
and `pmull2` gets low coefficients — opposite to the natural-order
functions, but consistent with each other.

The Karatsuba middle term uses `trn1`/`trn2` instead of `ext`+`eor`:

```asm
trn1  v18.2d, v9.2d, v8.2d     // collect d[0] from two blocks
trn2  v8.2d,  v9.2d, v8.2d     // collect d[1] from two blocks
eor   v8, v8, v18              // XOR halves → middle terms for 2 blocks
```

### What trn1/trn2 do

```
trn1 vd.2d, vn.2d, vm.2d   →  vd = { vn.d[0], vm.d[0] }  (low lanes)
trn2 vd.2d, vn.2d, vm.2d   →  vd = { vn.d[1], vm.d[1] }  (high lanes)
```

This collects all d[0] values into one register and all d[1] values
into another, then XORs to get middle terms for two blocks in 3
instructions. Compare with `ext`+`eor` which needs 2 instructions per
block (and wastes half the `eor` output — both halves of
`ext(H,H,#8) XOR H` contain the same value `H_lo ⊕ H_hi`, but only
one lane is consumed by `pmull`).

### trn1/trn2 vs ext+eor

| | `ext`+`eor` | `trn1`/`trn2` |
|---|---|---|
| Instructions per 2 blocks | 4 (2 `ext` + 2 `eor`) | 3 (1 `trn1` + 1 `trn2` + 1 `eor`) |
| Wasted computation | Half of each `eor` output unused | None — both lanes used |
| Lane-order dependent | Yes (needs natural order) | No (works with either layout) |
| Used by | gmult, ghash 2x, ghash 4x | unroll8 |

## Summary table

| Function | H from Htable | Data prep | Working order |
|----------|---------------|-----------|---------------|
| gcm_init_v8 | — (stores lanes-exchanged) | — | — |
| gcm_gmult_v8 | `ext #8` → natural | `rev64` + `ext #8` → natural | natural |
| gcm_ghash_v8 (2x) | `ext #8` → natural | `rev64` + `ext #8` → natural | natural |
| gcm_ghash_v8_4x | `ext #8` → natural | `rev64` + `ext #8` → natural | natural |
| aesv8_gcm_8x | used as-is (lanes-exchanged) | `rev64` only (lanes-exchanged) | lanes-exchanged |

## What if init stored in natural order instead?

If `gcm_init_v8` omitted the `ext #8` before storing (natural order):

| Function | Change needed |
|----------|---------------|
| gcm_init_v8 | Remove `ext #8` before each store. Also removes the redundant `ext #8` at the start of each H² computation. Saves ~8 `ext` instructions. |
| gcm_gmult_v8 | Remove `ext #8` on H load. H is already natural. Data is already natural (`rev64` + `ext #8`). **Saves 1 `ext`.** |
| gcm_ghash_v8 (2x) | Remove `ext #8` on H loads. **Saves 2 `ext`.** |
| gcm_ghash_v8_4x | Remove `ext #8` on H loads. **Saves 4 `ext`.** |
| aesv8_gcm_8x | **Needs change.** H is now natural but data is lanes-exchanged (`rev64` only). Mismatch. Must either: (a) add `ext #8` on each H load, or (b) add `ext #8` on each data block, or (c) swap `pmull`↔`pmull2` roles throughout. |

The first four functions get simpler. The unroll8 gets more complex —
any fix adds instructions to the hottest loop (8 blocks of AES+GHASH
interleaved). This is likely why the original author chose the
lanes-exchanged storage convention: it optimizes for the unroll8 path.

## Alternatively: keep lanes-exchanged storage, fix gmult/ghash

| Function | Change needed |
|----------|---------------|
| gcm_init_v8 | No change. |
| gcm_gmult_v8 | Remove `ext #8` on H load. Remove `ext #8` on data. Use lanes-exchanged order throughout. Adopt `trn1`/`trn2` or swap `pmull`↔`pmull2`. |
| gcm_ghash_v8 (2x) | Same: remove `ext #8` on H and data, work in lanes-exchanged order. |
| gcm_ghash_v8_4x | Same. |
| aesv8_gcm_8x | No change. |

This keeps the unroll8 (hot path) untouched and simplifies the other
functions. The trade-off is that gmult/ghash need their `pmull`/`pmull2`
and Karatsuba logic adjusted, but these are much smaller and simpler
than the 8000-line unroll8.
