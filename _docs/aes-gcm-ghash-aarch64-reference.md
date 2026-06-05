# AES-GCM GHASH on AArch64: Mathematics, Implementation, and Verification

A unified reference for the GHASH authentication component of AES-GCM
as implemented in AWS-LC's AArch64 assembly, grounded in NIST SP 800-38D
and Gueron's "A New Interpretation for the GHASH Authenticator" (2023).

## References

- **NIST SP 800-38D** — Section 6.3 (GHASH), Section 6.4 (GF(2¹²⁸) multiply)
- **Gueron (2023)** — "A New Interpretation for the GHASH Authenticator of
  AES-GCM", CSCML 2023, LNCS 13914, pp. 424–438.
  Local copy: [Shay-NewInterpretationGHASH-2023.txt](Shay-NewInterpretationGHASH-2023.txt)
- **Assembly files**: `arm/aes-gcm/ghashv8-armx.S` (init, gmult, ghash 2x/4x),
  `arm/aes-gcm/aesv8-gcm-armv8-unroll8.S` (8x interleaved AES+GHASH)

---

## 1. The NIST GHASH Specification

### 1.1 GHASH iteration

NIST SP 800-38D Section 6.3 defines GHASH as an iterated
XOR-then-multiply over ciphertext blocks:

```
Y₀ = 0
Yⱼ = (Yⱼ₋₁ ⊕ Xⱼ) • H       for j = 1, ..., m
GHASH(H, X₁...Xₘ) = Yₘ
```

where `•` is multiplication in GF(2¹²⁸) and H is the hash key
(AES-encrypt of the zero block).

### 1.2 The NIST multiply algorithm (bit-by-bit)

NIST defines `•` via Algorithm 1, a 128-step shift-and-XOR loop:

```
Z ← 0
V ← Y
for i = 0 to 127:
    if bit i of X:
        Z ← Z ⊕ V
    if LSB(V):
        V ← (V >> 1) ⊕ R      // R = 0xE1 || 0^120
    else:
        V ← V >> 1
return Z
```

This is schoolbook polynomial multiplication with online reduction.
At each step, V is shifted right (= multiplied by x in NIST's
bit-reflected convention), and if the low bit overflows, the result
is reduced by XORing with R (the reduction constant `0xE1 || 0^120`,
derived from the low-order terms x⁷ + x² + x + 1 = 0x87, shifted to
align with the MSB-first convention).

No implementation uses this loop directly. Hardware carry-less multiply
instructions (`pmull` on AArch64) compute the full 128×128 → 256-bit
product in one instruction, then reduce separately.

### 1.3 NIST's bit ordering

NIST uses a non-standard convention: "bit 0" of a byte is the MSB
(leftmost). A 128-bit block b₀b₁...b₁₂₇ maps to the polynomial
b₀·x¹²⁷ + b₁·x¹²⁶ + ... + b₁₂₇·x⁰.

The reduction polynomial is:

```
P(x) = x¹²⁸ + x⁷ + x² + x + 1
```

This bit ordering is the opposite of how `pmull` interprets register
bits (bit 0 = x⁰ = constant term). Section 3 explains how the
assembly handles this mismatch.

---

## 2. Gueron's Reinterpretation

### 2.1 The problem

As Gueron explains (Section 2 of his paper), NIST's bit-reflection
convention means that `pmull`/`PCLMULQDQ` do not directly compute
multiplication mod P(x). The bit-reflection must be accounted for.

### 2.2 Q(x): the bit-reflected polynomial

Gueron's Proposition 1 shows that GHASH `•` is equivalent to
multiplication in a different field representation:

```
G = GF(2¹²⁸) / Q(x)    where Q(x) = x¹²⁸ + x¹²⁷ + x¹²⁶ + x¹²¹ + 1
```

Q(x) is the bit-reflection of P(x): each coefficient pⱼ of P(x) maps
to q₁₂₈₋ⱼ of Q(x).

| P(x) term | Q(x) term |
|------------|-----------|
| x¹²⁸ | x¹²⁸ |
| x⁷ | x¹²¹ |
| x² | x¹²⁶ |
| x¹ | x¹²⁷ |
| x⁰ | (folds into x¹²⁸) |

Proposition 1 shows that the GHASH `•` operation — which the spec
defines as a bit-level algorithm hiding three steps (bit-reflect
inputs, multiply mod P(x), bit-reflect output) — is equivalent to a
Montgomery multiplication in this new representation.

### 2.3 The x-shift trick (Gueron equation 4.6)

The GHASH `•` operation is (equation 3.10):

```
A • B = A ⊗ B ⊗ x⁻¹²⁷  (mod Q(x))
```

where ⊗ is standard polynomial multiplication mod Q(x). Computing
this directly would require two multiplications. Equation 4.6 shows:

```
A • B = A ⊗ (x · B) ⊗ x⁻¹²⁸
```

Since H is fixed, the library pre-computes H̄ = x · H (mod Q(x)) once
during key setup (`gcm_init_v8`). Each GHASH step then computes
A × H̄ × x⁻¹²⁸ (mod Q(x)), which Proposition 3 handles efficiently.

### 2.4 The special form of Q(x)

Q(x) factors as:

```
Q(x) = x¹²⁸ + W(x)·x⁶⁴ + 1
```

where W(x) = x⁶³ + x⁶² + x⁵⁷ = `0xc200000000000000`.

In hexadecimal, the individual bit contributions are:

| Bit | Power | Hex contribution |
|-----|-------|-----------------|
| 63 | x⁶³ | 0x8000000000000000 |
| 62 | x⁶² | 0x4000000000000000 |
| 57 | x⁵⁷ | 0x0200000000000000 |
| Sum | | 0xc200000000000000 |

This `x²ᵗ + W(x)·xᵗ + 1` form (with t=64) is what makes the
two-phase reduction in Proposition 3 possible using only two 64×64
polynomial multiplications by W(x). See Section 5.

### 2.5 The twist in code

The pre-multiplication H̄ = x · H (mod Q(x)) is visible in the C
fallback (`gcm_nohw.c`):

```c
// mulX_POLYVAL: shift H left by 1 bit, conditionally reduce
Htable[0].hi <<= 1;
Htable[0].hi |= Htable[0].lo >> 63;
Htable[0].lo <<= 1;
// Conditional reduction by Q(x): XOR with 0xc200...0001
Htable[0].lo ^= carry & 1;
Htable[0].hi ^= carry & UINT64_C(0xc200000000000000);
```

And in the AArch64 assembly (`gcm_init_v8`), the constant is loaded as:

```asm
movi  v19, #0xe1
shl   v19, v19, #57            // v19 = 0xc200000000000000
```

---

## 3. From Memory to pmull: Bit and Byte Ordering

### 3.1 The mapping problem

AES outputs 16 bytes in big-endian order. GHASH needs to interpret
them as a GF(2¹²⁸) element. The `pmull` instruction treats register
bit k as the coefficient of xᵏ. We need NIST's b₀ (= x¹²⁷) to end
up at register bit 127.

### 3.2 Tracing a concrete bit

**Example**: byte 0 = 0x80 (binary 10000000). In NIST, b₀=1, so the
polynomial contribution is x¹²⁷.

**Stage 1: `ld1 {v.2d}`** — On little-endian aarch64, bytes 0–7 load
into `v.d[0]` (register bits 0–63), bytes 8–15 into `v.d[1]`
(bits 64–127). The MSB of byte 0 (our b₀=1) lands at register bit 7.

```
Register bit 7 = 1    (pmull reads this as x⁷ — wrong)
```

**Stage 2: `rev64 v.16b, v.16b`** — Reverses the 8 bytes within each
64-bit lane. Byte 0 moves from the lowest to the highest byte position
within `v.d[0]`. The MSB of byte 0 is now at register bit 63.

```
Register bit 63 = 1   (pmull reads this as x⁶³ — wrong lane)
```

**Stage 3: `ext v.16b, v.16b, v.16b, #8`** — Swaps `v.d[0]` and
`v.d[1]`. The bit moves from position 63 to position 127.

```
Register bit 127 = 1  (pmull reads this as x¹²⁷ — correct!)
```

### 3.3 Summary of each step

| Step | Fixes | Example bit position |
|------|-------|---------------------|
| `ld1` | — | bit 7 (x⁷) |
| `rev64` | Byte order within each lane | bit 63 (x⁶³) |
| `ext #8` | Lane placement | bit 127 (x¹²⁷) ✓ |

### 3.4 No bit-reversal within a byte is needed

Neither `rev64` nor `ext #8` reverses bits within a byte. None is
needed, because both NIST and `pmull` agree that higher bit positions
within a byte correspond to higher polynomial degree:

- NIST: b₀ is the MSB of byte 0 = bit 7 of byte 0 = highest degree
  within that byte
- `pmull`: bit 7 of a byte = x⁷ = highest degree within that byte

The only mismatch is byte ordering (NIST is big-endian, the register
is little-endian) and lane placement. `rev64` fixes byte order,
`ext #8` fixes lane placement.

In the formal verification, `bit_reverse_per_byte` is a mathematical
abstraction relating NIST's bit numbering to HOL Light's
`poly_of_word`. In the actual hardware, `rev64` + `ext #8` achieves
the correct mapping through byte reordering alone.

### 3.5 Cross-platform byte reversal

The same logical transformation is needed on all platforms, but the
mechanism differs:

| Platform | GHASH input reversal | Mechanism |
|----------|---------------------|-----------|
| AArch64 | `rev64` + `ext #8` | `rev64` reverses bytes within each 64-bit lane; `ext #8` swaps the two halves |
| x86_64 (aesni-gcm) | `movbe` loads | `movbe` byte-swaps during 64-bit load; halves loaded in reversed address order to swap them. Avoids SIMD shuffle pressure |
| x86_64 (ghash-x86_64) | `vpshufb` with `.Lbswap_mask` | Full 128-bit byte reversal via shuffle with mask `{15,14,...,1,0}` |
| C (gcm_nohw.c) | `CRYPTO_load_u64_be` + half-swap | Loads each 64-bit half with big-endian byte order, stores with halves swapped |

The x86_64 `movbe` approach moves the byte-swap off the SIMD pipeline
entirely, doing it in the scalar load path while the SIMD units are
busy with AES rounds.

---

## 4. Karatsuba Multiplication

### 4.1 Three products instead of four

To multiply two 128-bit elements C = (C_hi : C_lo) and H = (H_hi : H_lo),
Karatsuba reduces four 64×64 multiplications to three:

```
P_lo  = C_lo × H_lo                       (pmull)
P_hi  = C_hi × H_hi                       (pmull2)
P_mid = (C_hi ⊕ C_lo) × (H_hi ⊕ H_lo)    (pmull, using precomputed H_hi ⊕ H_lo)
```

The true cross terms are recovered by:

```
cross = P_mid ⊕ P_hi ⊕ P_lo
```

This works because expanding P_mid gives:

```
P_mid = C_hi×H_hi ⊕ C_hi×H_lo ⊕ C_lo×H_hi ⊕ C_lo×H_lo
      = P_hi ⊕ (cross terms) ⊕ P_lo
```

So `P_mid ⊕ P_hi ⊕ P_lo` cancels the contamination, leaving only
the cross terms `C_hi×H_lo ⊕ C_lo×H_hi`.

In the unroll8 assembly (using the 3-way XOR instruction):

```asm
eor3  v18.16b, v18.16b, v17.16b, v19.16b   // Karatsuba tidy-up
```

### 4.2 256-bit product layout

After tidy-up, the 256-bit product T(x) is spread across three
128-bit registers:

```
bit:  255        192       128        64         0
       |          |         |          |         |
v17:  [  D(x)    :  C(x)   ]                         (high)
v18:              [  cross_hi : cross_lo ]             (middle)
v19:                         [  B(x)    :  A(x)  ]    (low)
```

The four 64-bit limbs of T(x) = D·x¹⁹² + C·x¹²⁸ + B·x⁶⁴ + A are:

- bits [255:192] = D = v17_hi
- bits [191:128] = C ⊕ cross_hi = v17_lo ⊕ v18_hi
- bits [127:64]  = B ⊕ cross_lo = v19_hi ⊕ v18_lo
- bits [63:0]    = A = v19_lo

### 4.3 The trn1/trn2 trick (unroll8 only)

When processing pairs of blocks, the unroll8 uses AArch64 transpose
instructions to compute C_hi ⊕ C_lo for two blocks simultaneously:

```asm
trn1  v18.2d, v9.2d, v8.2d     // v18 = { v9.d[0], v8.d[0] }
trn2  v8.2d,  v9.2d, v8.2d     // v8  = { v9.d[1], v8.d[1] }
eor   v8.16b, v8.16b, v18.16b  // middle terms for 2 blocks
```

Then `pmull2` and `pmull` against the packed key register compute both
middle terms in two instructions.

| | `ext`+`eor` (gmult/ghash) | `trn1`/`trn2` (unroll8) |
|---|---|---|
| Instructions per 2 blocks | 4 | 3 |
| Wasted computation | Half of each `eor` unused | None |
| Used by | gmult, ghash 2x/4x | unroll8 |

---

## 5. Modular Reduction (Proposition 3)

### 5.1 Statement

Proposition 3 (Gueron, 2023): Let T(x) be a 256-bit polynomial and
Q(x) = x¹²⁸ + W(x)·x⁶⁴ + 1 where W(x) has degree 63. Then
T(x) × x⁻¹²⁸ (mod Q(x)) can be computed with two 64×64 polynomial
multiplications by W(x) and three XORs.

For AES-GCM: W(x) = x⁶³ + x⁶² + x⁵⁷ = `0xc200000000000000`.

### 5.2 Phase 1 — Fold A(x) out (equation 4.2)

Starting from T(x) = D·x¹⁹² + C·x¹²⁸ + B·x⁶⁴ + A, add A·Q(x)
(which is zero mod Q(x)) to cancel A:

```
U = C ⊕ A ⊕ high_half(W × A)
V = B ⊕ low_half(W × A)
```

Assembly:

```asm
pmull  v21.1q, v17.1d, v16.1d              // W(x) × A(x)
ext    v29.16b, v17.16b, v17.16b, #8       // swap halves of high
eor3   v18.16b, v18.16b, v29.16b, v21.16b  // fold into middle
```

The `ext #8` puts A(x) (= v17_lo) into the high lane and D(x)
(= v17_hi) into the low lane, so the `eor3` simultaneously adds A(x)
into the U(x) position and keeps D(x) in the correct place.

### 5.3 Phase 2 — Fold V(x) out (equation 4.5)

Same technique applied to V (now in v18_lo):

```
G(x)·xᵗ + F(x) = (D(x) + V(x))·xᵗ + U(x) + W(x) × V(x)    (4.5)
```

```asm
pmull  v17.1q, v18.1d, v16.1d              // W(x) × V(x)
ext    v21.16b, v18.16b, v18.16b, #8       // swap halves of middle
eor3   v19.16b, v19.16b, v17.16b, v21.16b  // fold into low = result
```

The result has degree < 128, so it equals T(x) × x⁻¹²⁸ (mod Q(x)).

### 5.4 C implementation equivalent

The C fallback (`gcm_nohw.c`) performs the same reduction using
bit-shifted XORs instead of `pmull`:

```c
// Phase 1: gather excess bits from shifts by 63, 62, 57
r1 ^= (r0 << 63) ^ (r0 << 62) ^ (r0 << 57);
// Phase 2: fold r0 into r2/r3
r2 ^= r0;
r2 ^= r0 >> 1; r2 ^= r1 << 63;
r2 ^= r0 >> 2; r2 ^= r1 << 62;
r2 ^= r0 >> 7; r2 ^= r1 << 57;
```

This is the same reduction expressed in the POLYVAL domain where the
shifts go in the opposite direction.

### 5.5 Total cost

- 2 polynomial multiplications (64×64 `pmull` by W(x))
- 3 XORs (two `eor3` + implicit additions)
- 2 half-swaps (`ext #8`)

No full 128×128 multiplication is needed for reduction.

---

## 6. Aggregation Before Reduction

When processing multiple blocks (e.g., 8 at a time in the unroll8),
all Karatsuba products are accumulated (XORed) into three registers
(high, low, mid) before performing a single reduction.

From Gueron's equation 4.8:

```
T = X₁ × H̄⁸ + X₂ × H̄⁷ + ... + X₈ × H̄¹
```

Then a single reduction (equation 4.9):

```
GHASH = T × x⁻¹²⁸ (mod Q(x))
```

The two-phase reduction is performed only once per batch, not once per
block. The hash table stores precomputed H̄ʲ values and their Karatsuba
helpers (H_hi ⊕ H_lo) for each power j = 1..8.

---

## 7. Htable: Lane Conventions and Storage

### 7.1 Terminology

- **Natural polynomial order**: `d[0]` = low 64 coefficients (x⁰..x⁶³),
  `d[1]` = high 64 coefficients (x⁶⁴..x¹²⁷).
- **Lanes-exchanged**: `d[0]` = high, `d[1]` = low. Produced by
  `ext v, v, #8`.

### 7.2 What gcm_init_v8 stores

`gcm_init_v8` computes the twist H̄ = x · H (mod Q(x)) in natural
polynomial order, then applies `ext #8` before every store:

```asm
eor  v20, v3, v16              // twisted H — natural order
ext  v20, v20, v20, #8         // → lanes-exchanged
st1  {v20}, [x0], #16          // store Htable[0]
```

All H powers are stored lanes-exchanged. Karatsuba middle terms
(H_hi ⊕ H_lo) are packed two per 128-bit slot:

```asm
ext  v21, v16, v17, #8    // v21.d[0] = mid(H^k), v21.d[1] = mid(H^{k+1})
```

Consumers access each half via `pmull` (low lane) or `pmull2` (high lane).

Htable layout: groups of 3 entries —
`[lanes-exchanged(H^k), pack(mid(H^k), mid(H^{k+1})), lanes-exchanged(H^{k+1})]`
— 12 entries total for H¹..H⁸.

### 7.3 Htable offset map

| Offset | Content | Used against block |
|--------|---------|-------------------|
| `[x6]` (0) | H¹ (lanes-exchanged) | 8k+7 (nearest) |
| `[x6, #16]` | pack(mid(H²), mid(H¹)) | Karatsuba mid for H¹, H² |
| `[x6, #32]` | H² (lanes-exchanged) | 8k+6 |
| `[x6, #48]` | H³ (lanes-exchanged) | 8k+5 |
| `[x6, #64]` | pack(mid(H⁴), mid(H³)) | Karatsuba mid for H³, H⁴ |
| `[x6, #80]` | H⁴ (lanes-exchanged) | 8k+4 |
| `[x6, #96]` | H⁵ (lanes-exchanged) | 8k+3 |
| `[x6, #112]` | pack(mid(H⁶), mid(H⁵)) | Karatsuba mid for H⁵, H⁶ |
| `[x6, #128]` | H⁶ (lanes-exchanged) | 8k+2 |
| `[x6, #144]` | H⁷ (lanes-exchanged) | 8k+1 |
| `[x6, #160]` | pack(mid(H⁸), mid(H⁷)) | Karatsuba mid for H⁷, H⁸ |
| `[x6, #176]` | H⁸ (lanes-exchanged) | 8k+0 (farthest) |

Block 8k+0 (the oldest in the batch) is multiplied by H⁸ (the highest
power) because GHASH expands as:
`(Xi ⊕ C₀)·H⁸ ⊕ C₁·H⁷ ⊕ ... ⊕ C₇·H¹`.

### 7.4 Redundant exchange in init

After storing lanes-exchanged H, init immediately un-exchanges it for
the next H² computation:

```asm
ext  v16, v20, v20, #8         // back to natural for Karatsuba!
```

This round-trip costs one `ext` per H power and saves nothing.

### 7.5 Per-function convention

| Function | H from Htable | Data prep | Working order |
|----------|---------------|-----------|---------------|
| gcm_init_v8 | — (stores lanes-exchanged) | — | — |
| gcm_gmult_v8 | `ext #8` → natural | `rev64` + `ext #8` → natural | natural |
| gcm_ghash_v8 (2x) | `ext #8` → natural | `rev64` + `ext #8` → natural | natural |
| gcm_ghash_v8_4x | `ext #8` → natural | `rev64` + `ext #8` → natural | natural |
| aesv8_gcm_8x | as-is (lanes-exchanged) | `rev64` only (lanes-exchanged) | lanes-exchanged |

The unroll8 works in lanes-exchanged order because `rev64` alone
(without `ext #8`) naturally produces lanes-exchanged data. By storing
H powers lanes-exchanged, init matches the unroll8's convention
directly, avoiding any conversion in the hottest loop.

### 7.6 Optimization tradeoffs

**Option A: store natural order** — Saves `ext #8` in init, gmult,
ghash 2x/4x. Breaks unroll8 (H natural, data lanes-exchanged →
mismatch). Any fix adds instructions to the 8-block hot loop.

**Option B: keep lanes-exchanged, fix gmult/ghash** — Remove `ext #8`
on H and data loads in gmult/ghash, work in lanes-exchanged order
throughout. Swap `pmull`↔`pmull2` roles or adopt `trn1`/`trn2`.
Leaves init and unroll8 untouched. Smaller, simpler functions change;
the 8000-line unroll8 stays as-is.

Option B is the better direction — it optimizes for the hot path.

---

## 8. Correspondence to NIST SP 800-38D

| NIST concept | Implementation |
|---|---|
| Section 6.3: Yⱼ = (Yⱼ₋₁ ⊕ Xⱼ) • H | `eor` accumulator with block, then Karatsuba multiply |
| Section 6.4: multiply in GF(2¹²⁸) mod P(x) | Actually mod Q(x) with Montgomery factor x⁻¹²⁷ (Gueron Prop 1) |
| Bit ordering (Section 6.1) | `rev64` + `ext #8` (or `rev64` alone in unroll8) |
| P(x) = x¹²⁸ + x⁷ + x² + x + 1 | Equivalent to Q(x) after bit-reflection; W(x) = `0xc200000000000000` |
| Horner's method (single block at a time) | Expanded to 8-block aggregation, single reduction at end |

---

## 9. The Assembly Functions

### 9.1 gcm_init_v8

```c
void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);
```

Computes the twisted hash key H̄ = x · H (mod Q(x)) and all powers
H̄¹..H̄⁸, storing them in Htable with Karatsuba middle terms. See
Section 7 for the storage layout and lane conventions.

### 9.2 gcm_gmult_v8

```c
void gcm_gmult_v8(uint8_t Xi[16], const u128 Htable[16]);
```

Single-block GHASH multiply: Xi = Xi · H in GF(2¹²⁸). Loads Xi,
byte-reverses it (`rev64` + `ext #8`), performs 3-pmull Karatsuba
against the twisted H from Htable, reduces via two-phase Prop 3,
byte-reverses the result, and stores back. 27 NEON instructions total.

### 9.3 gcm_ghash_v8

```c
void gcm_ghash_v8(uint8_t Xi[16], const u128 Htable[16],
                  const uint8_t *inp, size_t len);
```

Multi-block GHASH. Three code paths by input length:

| Path | Input size | Blocks/iter | H powers | Key optimization |
|------|-----------|-------------|----------|------------------|
| 4x (`gcm_ghash_v8_4x`) | ≥ 64 bytes | 4 | H, H², H³, H⁴ | 4 independent pmull chains, single reduction |
| 2x (`Loop_mod2x_v8`) | 32–63 bytes | 2 | H, H² | Reduction of current pair overlaps with pmull of next pair |
| 1x (`Lodd_tail_v8`) | 16 bytes | 1 | H | Same as gcm_gmult_v8 |

The 4x path computes
`(Xi ⊕ inp[i])·H⁴ ⊕ inp[i+1]·H³ ⊕ inp[i+2]·H² ⊕ inp[i+3]·H`
simultaneously, interleaving the `pmull` instructions for all four
multiplications before doing a single combined reduction.

Batching helps because the Karatsuba multiplications for independent
blocks can be issued simultaneously, and the reduction overhead is
amortized. For the 2x path, the reduction of one pair overlaps with
the `pmull` instructions of the next pair, keeping the pipeline busy.

### 9.4 aesv8_gcm_8x (unroll-by-8)

```c
size_t aesv8_gcm_8x_enc_128(const uint8_t *in, uint8_t *out,
    size_t len, const void *key, const uint8_t ivec[16],
    const u128 Htable[16], uint8_t Xi[16]);
```

Processes 8 blocks at a time, interleaving AES encryption with GHASH
to hide latency. Uses a one-iteration-delayed design: ciphertext
produced in iteration N is GHASH'd in iteration N+1, allowing AES
rounds and GHASH multiplies to overlap.

Six variants exist for enc/dec × 128/192/256-bit keys.

#### Step-by-step pipeline

1. **Load plaintext** into v8–v15 (`ldp`)
2. **Produce ciphertext** via `eor3 v8, v8, v0, v27` — this folds
   the final AES round (normally `aese` + XOR with last round key)
   into a single 3-way XOR with the plaintext. Store to output.
   v8–v15 are NOT overwritten — they hold ciphertext for GHASH.
3. **Next iteration top**: byte-reverse previous ciphertext (`rev64`)
4. **XOR accumulator** into first block (`ext #8` + `eor`). The
   `ext #8` on the accumulator aligns it with the lanes-exchanged
   data convention.
5. **Karatsuba multiply** all 8 blocks against H⁸..H¹ in pairs,
   using `trn1`/`trn2` for middle terms, accumulating into v17/v18/v19
6. **Karatsuba tidy-up**: `eor3 v18, v18, v17, v19`
7. **Two-phase reduction**: 2 × `pmull` by W(x) + `eor3` (Section 5)
8. **Result** in v19 = new GHASH accumulator

Steps 3-7 are interleaved with AES rounds for the next batch's
counter blocks, keeping both the crypto and polynomial pipelines busy.

At the end of the function (after all blocks are processed), the
accumulator is converted back to memory order with `ext #8` + `rev64`
before being stored back to `[x3]` (the Xi pointer).

---

## 10. NEON vs Scalar Reduction

A straightforward implementation of POLYVAL — as defined in RFC 8452
for AES-GCM-SIV, using the same Q(x) polynomial as GHASH after
bit-reflection — can be written in assembly using scalar registers
with explicit shifts instead of NEON `pmull` for the reduction phase.
This confirms that both approaches compute the same polynomial
arithmetic, and serves as a useful proof-of-concept of the equivalence.

The two reduction styles compared:

| Aspect | NEON (gcm_gmult_v8) | Scalar (explicit shifts) |
|---|---|---|
| Domain | NEON throughout | NEON for multiply, scalar for reduce |
| Reduction method | `pmull` × `0xC200000000000000` | Explicit shifts by 63, 62, 57 |
| Reduction instructions | ~8 (2 `pmull` + `eor`/`ext`) | ~14 `eor` with shifted operands |
| Byte reversal | Yes (GHASH big-endian interface) | No (POLYVAL little-endian native) |

### Same polynomial, different encoding

`gcm_gmult_v8` reduces via `pmull` against `0xC200000000000000`. A
`pmull` of a 64-bit value against this constant is equivalent to
XOR-ing shifted copies at positions 63, 62, 57 (the set bits).

The scalar approach does the same with explicit shifts:

```asm
eor  x4, x4, x3, lsl #63    // shift by 63
eor  x4, x4, x3, lsl #62    // shift by 62
eor  x4, x4, x3, lsl #57    // shift by 57
```

And the carry-over bits crossing the 64-bit boundary:

```asm
eor  x5, x5, x3, lsr #1     // 64-63 = 1
eor  x5, x5, x3, lsr #2     // 64-62 = 2
eor  x5, x5, x3, lsr #7     // 64-57 = 7
```

These right-shifts by 1, 2, 7 are the complements of 63, 62, 57
relative to the 64-bit word boundary. In `gcm_gmult_v8`, the second
`pmull` against the same `0xC200000000000000` constant handles this
second word automatically — the 128-bit `pmull` output spans both
halves.

Same polynomial {63, 62, 57} = W(x) = x⁶³ + x⁶² + x⁵⁷. Same
arithmetic. The NEON version is more compact; the scalar version
avoids NEON→scalar transfer latency when the caller is already in
scalar code.

---

## 11. Formal Verification

### 11.1 Proof architecture

The formal verification in HOL Light connects NIST's specification to
the ARM assembly through a layered chain:

```
NIST SP 800-38D Algorithm 1            (bit-level shift-and-XOR loop)
        |
        v
Polynomial algebra mod P(x)            (ghash_reduce, word_pmul)
        |
        v
POLYVAL / polyval_dot mod Q(x)         (Gueron's reinterpretation)
        |
        v
gcm_gmult_spec / gcm_ghash_spec        (instruction-level spec)
        |
        v
ARM assembly                            (27 instructions for gmult)
```

### 11.2 Two approaches to the NIST bridge

Two independent strategies can connect NIST Algorithm 1 to polynomial
algebra:

| | Direct induction | Via POLYVAL |
|---|---|---|
| Route | NIST loop → `ghash_reduce(word_pmul)` | NIST → POLYVAL → `ghash_reduce` via Gueron Prop 1 |
| Technique | Induction on 128 loop steps, each step = multiply by x mod P(x) | Algebraic identity P(x) ↔ Q(x), then twist |
| Best for | Single-block proofs (gmult) | Full suite (gmult + ghash + batched + unroll8) |

The direct approach is more self-contained for verifying a single-block
function like `gcm_gmult_v8`. The POLYVAL approach builds reusable infrastructure: the
batched equivalence theorem and NIST-to-POLYVAL bridge apply to all
consumers (gmult, ghash, 4x, 8x) without re-derivation.

### 11.3 Key theorems from the POLYVAL stack

| Theorem | Session | Role |
|---------|---------|------|
| `PMUL_KARATSUBA` | 1 | 3-pmull Karatsuba = word_pmul |
| `POLYVAL_REDUCE_PROP3_CORRECT` | 2-3 | Prop 3 reduction is correct mod Q(x) |
| `POLYVAL_DOT_CORRECT` | 4 | Single multiply is correct |
| `GHASH_POLYVAL_ACC_BATCHED` | 5 | n-block batched = iterative GHASH |
| `GHASH_TWIST_CORRECT` | 6 | Twisted H connects to algebraic H |
| `NIST_GHASH_IS_POLYVAL` | 7 | NIST GHASH = POLYVAL iteration |

### 11.4 Unroll8 verification path

```
NIST GHASH (iterated)
    ↓  NIST_GHASH_IS_POLYVAL
POLYVAL iteration
    ↓  GHASH_POLYVAL_ACC_BATCHED
8-block batched = iterative
    ↓  POLYVAL_DOT_CORRECT × 8
Each block multiply correct
    ↓  ARM simulation (new work)
Assembly output matches spec
```
