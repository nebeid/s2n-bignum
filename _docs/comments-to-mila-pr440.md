# Comments on PR #440 (AES-256-GCM 8x encrypt, whole blocks) — from the decrypt side

Context: #440 (encrypt) and #445 (decrypt) are sibling kernels from the same
aws-lc generator, developed in parallel. Both are currently drafts with no
reviewers assigned and **no review comments on either** — so none of this is
inherited feedback; it is what we found while building the decrypt side and
comparing the two.

Ordered by importance. Items 1–3 are things we think need fixing; 4–6 are
coordination; 7–8 are things #440 does better than #445, recorded so we adopt
them rather than argue.

---

## 1. #440 does not build on macOS — the CFI directives cannot be assembled

`make -C arm aes-gcm/aesv8_gcm_8x_enc_256_wb.o` fails on macOS/arm64:

```
<stdin>:1501:41: error: invalid CFI advance_loc expression
```

Line 1501 is the first epilogue `CFI_STACKLOAD2`. We hit the identical failure
in the decrypt kernel and bisected it: **on Mach-O, `.L`-prefixed labels are not
assembler-local.** The Mach-O local prefix is `L`, not `.L`, so every
`.L256_enc_*` label creates an atom boundary, and CFI cannot compute an
`advance_loc` across one. Our bisect found CFI works up to the instruction
immediately before the first `.L` label in the body and fails from that
instruction onward — for us that was `.L256_dec_main_loop:`, for #440 it will be
`.L256_enc_main_loop:` at line 426.

The fix is a mechanical rename of the 14-ish `.L256_enc_*` labels to
`L256_enc_*`, which is what `arm/aes-xts/aes_xts_{en,de}crypt.S` already does
(`Lxts_dec_big_size:`, `Loop5x_xts_dec:`, …). We verified on both platforms that
the rename is **text-byte neutral**: `.text` md5 and length unchanged, and the
`L` labels stay out of the Mach-O symbol table (4 symbols, same as XTS). On ELF
they appear as `LOCAL NOTYPE` symbols — 14 for us, 15 for XTS — which upstream
evidently accepts.

Worth noting the Type 0 checklist item this trips: *"Also try on macOS (different
assembler)"*. CI would not have caught it — `s2n-bignum-tutorial-macos-arm` is
the only macOS job and it does not build `arm/aes-gcm/`.

## 2. `CFI_DEC_SP` changes the object bytes; a one-instruction alternative exists

#440's prologue is `CFI_START` / `CFI_DEC_SP(STACK_SIZE)` /
`CFI_STACKSAVE2X(d8,d9,0,8)` / …. `CFI_DEC_SP` emits a separate
`sub sp, sp, #80`, so where the generator emitted one pre-index
`stp d8, d9, [sp, #-80]!` there are now two instructions. That means the object
is no longer byte-comparable to the aws-lc original, which matters for #440's own
provenance claim that "the instruction body below is a verbatim copy of the
generator's output", and for any differential KAT against the upstream sibling.

The macro set has the right shape already — `CFI_PUSH2` / `CFI_POP2` are exactly
pre/post-index pair push/pop with `.cfi_adjust_cfa_offset` — but they are
hardcoded to a 16-byte frame. We added a size-parameterised pair to
`include/_internal_s2n_bignum_arm.h` in #445:

```c
#define CFI_PUSH2N(lo,hi,negsize,size) stp lo, hi, [sp, #(negsize+0)]! __LF \
        .cfi_adjust_cfa_offset size __LF .cfi_rel_offset lo, 0 __LF .cfi_rel_offset hi, 8
#define CFI_POP2N(lo,hi,size) ldp lo, hi, [sp], #(size+0) __LF \
        .cfi_adjust_cfa_offset -size __LF .cfi_restore lo __LF .cfi_restore hi
```

`negsize = -size` is passed explicitly rather than computed, following
`CFI_STACKSAVE2X`'s existing comment about composite expressions and the AWS-LC
FIPS delocator. Verified on both `as` implementations; DWARF output confirms
`DW_CFA_def_cfa_offset: 80` and `r72/r73 (v8/v9) at cfa-80/-72`; `.text`
byte-identical to the plain form.

With the label rename from item 1 plus `CFI_PUSH2N`/`CFI_POP2N`, #440 gets full
prologue+epilogue CFI, builds on macOS, and regains byte-parity with the
generator output. Since the macros land in a shared header, it may be cleanest to
split them into their own small PR so neither kernel PR blocks on the other.

## 3. Buffer extents in the signature metadata are 8× too large

`include/s2n-bignum.h` and the generated
`arm/proofs/subroutine_signatures.ml` entry describe the input as `in[bit_len]`
and `("in", "bit_len", 1)`. `bit_len` is a **bit** count; the buffer is
`bit_len / 8` bytes. As written this claims an 8× larger input buffer than the
function reads.

That metadata feeds constant-time / memory-safety spec generation, so the
overstatement is not cosmetic. #445 writes `in[bit_len/8]` and
`("in", "bit_len/8", 1)`; `collect-signatures.py` parses the division without
complaint.

## 4. Let's settle the theorem namespace jointly

#440 exports `AESV8_GCM_8X_ENC_256_WB_*`. #445 deliberately dropped the `_wb`
infix and exports `AESV8_GCM_8X_DEC_256_*` — which, on reflection, claims the
namespace of the **non-WB** upstream kernel. #440's convention is the safer one
and we are inclined to move to it rather than have the sibling PRs disagree.

Two related items on #440's side:

- `arm/proofs/specifications.txt` lists the narrow
  `AESV8_GCM_8X_ENC_256_WB_SUBROUTINE_CORRECT`, whereas the proof file itself
  describes `_SUBROUTINE_CORRECT_GEN` as "the externally-used spec". Since
  `tools/count-proofs.sh` diffs proven `*_SUBROUTINE_{CORRECT,SAFE}` names
  against that file, it is worth checking the intended entry is the listed one.
- #440 exports 6 theorems (`_WB_CORRECT`, `_GEN`, `_G1`, `_ALL`,
  `_SUBROUTINE_CORRECT`, `_SUBROUTINE_CORRECT_GEN`); #445 consolidated to 2. A
  reviewer will likely ask why the sibling kernels expose different surfaces.

## 5. The two exported specifications use different vocabularies for the same thing

Concretely, for the same kernel family:

| | #440 (encrypt) | #445 (decrypt) |
|---|---|---|
| AES block function | `aes256_cipher` | `aes256_encrypt` |
| round-key reads | per-index `EL n rk` | `wordlist_from_memory` |
| counter index | hardcoded `2` | symbolic `c` |
| code length | `LENGTH ..._mc` | literal `4968` |
| length bound | `2 EXP 64` | `2 EXP 62` |

We already carry this as an open TODO (#445 commit `37e86d60`, "aes_ctr_spec:
TODO for the round-key representation divergence"). Since CTR mode is its own
inverse and both kernels GHASH the ciphertext, the exported contracts *can* share
one vocabulary — #445's `arm/proofs/utils/aes_ctr_spec.ml` was written for
exactly that, and is loaded by both the encrypt and decrypt proof chains. Worth
converging before either PR is reviewed, or a reviewer will ask why sibling
kernels describe the same computation two ways.

## 6. Shared test files, and the collision list

Eight files are touched by both PRs. Two are **byte-identical** and will
auto-resolve on an add/add merge:

- `tests/known_value_tests_gcm_256.h`
- `tests/ref_gcm_v8table.c`

`tests/ref_gcm_nohw.c` differs by +5 / −49: we omit the verbatim
`hw_gcm_encrypt` Path-B dispatch, because it call-references
`aesv8_gcm_8x_enc_256_wb` and friends, which #445 does not add — so with it
present our test binary does not link. We replaced it with a 5-line NOTE
explaining the omission. If #440 lands first we will simply adopt your file
unchanged; if #445 lands first, the block wants restoring. Either way it should
end up as one copy.

The remaining collisions are `tests/test.c`, `benchmarks/benchmark.c`,
`arm/Makefile` (both rewrite the same `AES_GCM_OBJ` / `OBJ =` lines),
`include/s2n-bignum.h`, and adjacent single-line inserts in
`specifications.txt` / `subroutine_signatures.ml` / `collect-signatures.py`.

Also: thank you for `ref_gcm_v8table.c`. Reproducing `gcm_init_v8` with each NEON
op annotated against the `.pl` line it mirrors is the piece that made the decrypt
KAT tractable — we would otherwise have had to guess the `Htable` layout.

## 7. Two things #440 does better, which we are adopting

- **`arm/aes-gcm/Makefile`.** Every other `arm/` subdirectory has one; #445
  relies on the generic `%.o : %.S` rule, so `cd arm/aes-gcm && make` fails even
  though CI is green. We are adding yours.
- **The guard test's false-positive check.** #440 re-encrypts
  `floor(bitlen/128)` blocks with the reference and asserts the kernel output did
  *not* match ("guard bypassed!"). #445's guard test only checks the return value
  and the untouched sentinel — it would pass even if the guard silently processed
  the truncated block count. We are adopting the check. We are also moving our
  bad bit-lengths into the ≥256 B dispatch-eligible band; ours are currently all
  below it.

## 8. On the published performance numbers — a harness note, not a correction

#440's body reports −17.8 % at 256 B on Neoverse-V1 via `benchmarks/benchmark.c`.
Measuring the identical code pair with a dedicated harness gives **−15.6 %** at
that size. Both are right; the difference is the harness. `benchmarks/benchmark.c`
re-initialises 30 round keys, 32 `Htable` words and 32 bytes **inside** its timed
helper on every call, and reports an arithmetic mean via `clock()` at 1 µs
granularity, so it inflates the denominator. Across four harnesses, one code
change at one size on one microarchitecture spans **5.2 % to 16.1 %**.

Two practical consequences:

- Our PRs will publish different-looking percentages for structurally similar
  work. If we each name the harness and host in the body, that reads as rigour
  rather than as one of us being wrong.
- `benchmarks/benchmark.c` has **no 128 B registration** for either direction —
  which is exactly the size where this class of optimisation pays most (we
  measure −22 % vs aws-lc at 128 B on Graviton4). Worth adding a 128 B row for
  both kernels.

One small thing in the assembly: #440 encodes all 70 `eor3` as
`.inst 0xce1c3631` with the mnemonic in a trailing comment, and carries ~34
internal `[s097]`-style session markers in the shipped `.S`. We converted our 64
`.inst` words to real `eor3` mnemonics (needs `+sha3` in `.arch`) and verified
`.text` byte-identical on both platforms, so the encoding is free to change. The
session markers are presumably just leftovers.
