# Suggested PR description for awslabs/s2n-bignum#445

Draft for review. Replace the current placeholder body with the section marked
**PR BODY** below. Everything after that section is supporting material and
rationale, not intended for the PR itself.

---

## PR BODY

### ARM: whole-blocks-only AES-256-GCM decrypt kernel + HOL Light proof

Adds `aesv8_gcm_8x_dec_256_wb`, an AES-256-GCM decrypt kernel restricted to
whole 16-byte blocks, together with a machine-checked HOL Light functional
correctness proof and its supporting shared specification layer.

#### What it is

The kernel is derived from the aws-lc 8x-unrolled decrypt kernel
(`crypto/fipsmodule/modes/asm/aesv8-gcm-armv8-unroll8.pl`, function
`aesv8_gcm_8x_dec_256`) with two intentional divergences:

1. **A whole-blocks guard at entry** — `tst x1, #127; b.ne .L256_dec_ret`.
   `bit_len` must be a nonzero multiple of 128. Otherwise the function returns 0
   having touched no memory.
2. **Deletion of the partial-final-block masking machinery.** Under the
   whole-blocks contract that code is dead: the length mask is all-ones, the
   GHASH input mask is a no-op, and the output `bif` blend degenerates to the
   plain block. Removing it also removes the original's 16-byte overread and
   read-modify-write of the output buffer on the last block.

The aws-lc caller already satisfies the contract:
`crypto/fipsmodule/modes/gcm.c` masks the length with
`kSizeTWithoutLower4Bits` and passes `len_blocks * 8`.

#### Verification

Exported theorems, both proved 0-CHEAT with `axioms = 3` and no hypotheses:

- `AESV8_GCM_8X_DEC_256_CORRECT` — the core contract
- `AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT` — the AAPCS64 wrapper

The proof covers symbolic block counts, not a fixed length: the exported
statements quantify over `nblk` and are stated over an abstract input via a
byte-list spine, in the shared NIST counter vocabulary
(`arm/proofs/utils/aes_ctr_spec.ml`) so that the encrypt and decrypt contracts
present the same per-block keystream term.

Full-file cold gate, from source, against the CI-pinned HOL Light:
`axioms = 3`, target theorem 0 hypotheses, `GATE_PASS`.

#### Testing

`tests/test.c` adds three checks, registered under `aes && sha3`:

- **Differential** against a pure-C GCM reference. GCM encrypt folds its
  *output* into `Xi` and decrypt folds its *input*, so reference-encrypting
  `P → C` and then decrypting `C` must agree on the recovered plaintext, the
  GHASH accumulator, the advanced counter, and the returned byte count.
- **Whole-blocks contract** — a `bit_len` that is not a nonzero multiple of 128
  returns 0 and leaves `out` / `Xi` / `ivec` untouched.
- **Known-answer tests** over 7 aws-lc AES-256-GCM vectors
  (`crypto/cipher_extra/test/aes_256_gcm_tests.txt`), feeding the published
  ciphertext and checking both the recovered plaintext and the tag through the
  production call path.

`tests/ref_gcm_nohw.c` is the aws-lc pure-C GCM reference and
`tests/ref_gcm_v8table.c` reproduces `gcm_init_v8`, building the v8-format
`Htable` the kernel consumes. Both are shared with the AES-GCM **encrypt**
change set (#440) and should converge on one copy.

#### Performance

Two independent harnesses, both reported. Percentages are
`(old − new) / old`; negative means the new code is faster.

**Versus current aws-lc `aesv8_gcm_8x_dec_256`** — one binary, all variants
linked with distinct symbols and timed round-robin interleaved, `taskset`-pinned,
best-of-N over 22 processes, min across processes. Host: Graviton4 /
Neoverse-V2, 2.79 GHz measured in-process.

| size | aws-lc | this PR | delta | A/A noise floor |
|---:|---:|---:|---:|---:|
| 128 B | 32.729 ns | 25.454 ns | **−22.2 %** | 0.81 % |
| 256 B | 55.261 ns | 45.564 ns | **−17.5 %** | 0.44 % |
| 512 B | 94.167 ns | 83.116 ns | **−11.7 %** | 1.11 % |
| 1024 B | 171.764 ns | 161.655 ns | **−5.9 %** | 0.62 % |
| 4096 B | 638.301 ns | 628.438 ns | −1.6 % | 0.11 % |

A correctness gate ran in every timed process before any measurement: all
symbols called on identical input, with plaintext, `Xi`, `ivec` and the return
value compared byte-for-byte. It passed in 22/22 processes at all sizes — so
these numbers come from a binary whose symbol wiring is verified.

**Cross-generation**, cumulative over the five optimisation commits in this PR,
from an earlier interleaved harness on three Graviton generations:

| size | Graviton3 / V1 | Graviton4 / V2 | Graviton5 / V3 |
|---:|---:|---:|---:|
| 128 B | −20.9 % | −21.4 % | −17.3 % |
| 256 B | −15.5 % | −16.3 % | −13.7 % |
| 512 B | −9.8 % | −11.0 % | −8.7 % |
| 1024 B | −5.0 % | −5.4 % | −5.3 % |
| 4096 B | −1.3 % | −1.5 % | −1.4 % |

The gains concentrate on short messages and amortise away by 4 KB. That is
structural, and a reviewer can verify the reason in one command: the region
`.L256_dec_main_loop:` → `.L256_dec_tail:` is **byte-identical across all six
commits** (md5 `7d1d51f5…`). Every optimisation lives in SETUP or in the TAIL,
so at 256 blocks the changed code is a vanishing fraction of the work.

At the library level the same change is worth roughly half the kernel-level
figure, because the AEAD wrapper contributes a fixed per-call cost: measured
−5.8 % / −6.1 % / −8.0 % at 256 B on V1 / V2 / V3 through `bssl speed`.

Caveats stated plainly: absolute nanosecond figures are not comparable to
`benchmarks/benchmark.c`, which re-initialises round keys and the `Htable`
inside its timed region; buffers here are L1-resident, which flatters
dependency-depth optimisations relative to a streaming caller; and deltas below
the per-size A/A floor are not resolved by this method.

#### The fused short-message path

This PR also includes a **fused** variant covering 1–4 whole blocks
(16/32/48/64 B), separately proof-complete: `WB_FUSED_{1,2,3,4}BLOCK`, each
`hyps=0`, `axioms=3`, 0-CHEAT, re-validated against upstream's instruction model.

Differential benchmark, fused versus the non-fused kernel above, same host and
method (median of per-process paired deltas; `~` = below that size's placement
floor, i.e. not resolved):

| size | fused vs non-fused |
|---:|---:|
| 16 B | **−46.4 %** |
| 32 B | **−43.6 %** |
| 64 B | **−26.9 %** |
| 128 B | −0.05 %~ |
| 256 B | −0.22 %~ |
| 512 B | −0.29 % (V1) / +0.14 % (V2) / +0.02 % (V3) — no regression on any core |
| 1024 B | +0.44 %~ |
| 4096 B | −0.00 %~ |

Structural, and the numbers reflect it exactly: the fused bodies cover
`nblk ∈ {1,2,3,4}` only, and the `nblk ≥ 8` code is verified content-unchanged,
so every size from 128 B up is at or below the placement floor.

**Differential size: `.text` grows 4968 → 5960 bytes, +992 B (+20.0 %).** That is
the honest cost of the fused entry paths, paid in instruction footprint for
messages of 1–4 blocks.

Two caveats stated plainly. First, an earlier revision of these numbers reported
a +1.48 % penalty at 512 B; that was an artifact of a `min`-over-processes
estimator and has been **retracted** — a four-host study (32–40 processes each,
bootstrap CIs, 5 link permutations × 5 padding offsets) measured no regression on
any core. Second, aws-lc's current dispatch gates the 8x kernel on `len >= 256`
(moving to 128), so the sizes where fusion wins are not ones its dispatch routes
here today; the value is for callers that do, or for a future threshold change.

#### Main-loop alignment

The same study found something that applies to the **non-fused** kernel and is
worth landing independently. `.align 4` before the function entry is the only
alignment directive in the file — inherited from the aws-lc generator, which
aligns each exported entry and never an internal label — so the main loop's
address is purely a consequence of preceding code size, and nothing re-anchors
it.

On Neoverse-V1 the kernel's runtime depends on the main-loop entry address
**mod 16, and only on that** — not on which variant. Verified by a 2×2 test that
swaps alignment between variants and by single-variant offset sweeps showing a
clean period-16 effect; V2/V3 sensitivity is ≤ 0.05 %, i.e. nil. The shipped
kernel's main loop sits at function offset 1208 (≡ 8 mod 16), the slow class; the
fused variant is at 1216 (≡ 0) by accident.

Adding `.balign 16` before the main-loop label — gas emits 8 bytes, two `nop`s
executed once per call and never inside the loop — measured on Graviton3:

| size | 64 B | 256 B | 512 B | 1024 B |
|---:|---:|---:|---:|---:|
| gain | −0.02 % | **−0.38 %** | **−0.44 %** | **−0.37 %** |

Free ~0.4 % at every size that runs the main loop on Graviton3, no cost at 64 B,
~0 on V2/V3.

---

## Supporting material (not for the PR body)

### Why these numbers and not the others

Five harness generations exist in `_docs/`. They disagree by more than the
effect being measured in some cells, so the choice matters:

| harness | statistic | resolving power |
|---|---|---|
| in-tree `benchmarks/benchmark.c` | arithmetic mean, `clock()` at 1 µs, per-call key/`Htable` re-init inside the timed region | ~≥5 % |
| dedicated `mbg.c` | best-of-12 over 400k reps, 20k warm-up | ~1 % |
| per-commit cross-core | min over 10 processes × best-of-200 | claimed 0.03–0.7 % |
| `bench.c` experiment family | median of per-process best-deltas | ~0.1–0.5 % on V3 |
| aws-lc AEAD (`bssl speed`) | mean of 3 × 1 s runs | ~1.5 % |

For one code change at one size on one microarchitecture, the four harnesses
span **5.2 % to 16.1 %**. The in-tree harness reads low because its per-call
re-initialisation inflates the denominator. **#440's published table uses the
in-tree harness**, which is why its −17.8 % at 256 B corresponds to −15.6 % on a
dedicated harness for identical code. If the two PRs are read side by side, this
should be said out loud rather than left as an apparent discrepancy.

### Known weaknesses in our own prior measurements

Carried here so they are not repeated, and so nothing in the PR body overstates:

1. **The flagship cross-core harness was not preserved.** `/tmp/pcbench` is
   empty; the source, raw per-process lines and analysis script are gone. That
   table cannot be re-derived or re-analysed. Bank the harness in-repo next time —
   `_docs/prologue-relocation/` and `_docs/fused-*/` already do this correctly.
2. **`min` across processes is the wrong estimator** and two same-day sibling
   documents say so explicitly, preferring the median of per-process deltas.
   Min-of-mins selects the luckiest ASLR draw independently per symbol, and ASLR
   is the jitter mechanism those documents identified.
3. **The quoted noise floor is ~15× optimistic across builds.** The same code
   (v5) at 128 B on Neoverse-V2 measures 25.362–25.515 ns across five separate
   binaries — a 0.61 % range — against a quoted floor of 0.04 %. Every prior
   delta below ~0.6 % should be read as unresolved. The 2026-08-20 four-host
   study re-measured the floors properly over 120 A/A pairs per host: at 512 B
   they are ≤ 0.32 % (V1), ≤ 0.37 % (V2), ≤ 0.07 % (V3) — so the long-quoted
   "512 B cliff of ~1.1 %" was itself a min-of-mins artifact, and 512 B is not a
   special size (the V1 alignment effect is the same at 256 B and 1024 B).
4. **Every size in the per-commit table is a multiple of 8 blocks**, so the
   8-way cascade path is never timed — yet two of the five commits edit cascade
   code. A per-commit gate cannot see a cascade regression on 7 of 8 message
   lengths. Add 144/240/272 B.
5. **Only 2 of 6 variants had an A/A twin**; the floor was then applied to the
   four that had none.
6. At 16–48 B the A/A floor on V1/V2 is **4.9–8.6 %**, so small-size claims on
   those cores need a per-run A/A. Only Graviton5 supports sub-0.5 % claims.
7. The baseline is **non-monotone in length**: 112 B is slower than 128 B on all
   four hosts. Any "gain vs size" curve drawn only from 128 B upward is wrong
   about the shape below 128 B.

Today's Graviton4 run addresses 1, 5 and part of 6 (harness banked, four A/A
twins, per-size floors), and adds the aws-lc baseline and the 16/32/64 B band.
It does not address 2, 4 or 7.

### Defects to fix in #445 before it leaves draft

1. **`arm/aes-gcm/kat/Makefile` cannot build from a clean checkout.** It
   requires `aesv8_gcm_8x_dec_256.o` and `aesv8_gcm_8x_enc_256.o`, neither of
   which exists in the tree, plus a hardcoded
   `AWS_LC_DIR ?= $(HOME)/workplace/git-code/aws-lc`. The primary target fails.
   Either fix it or drop the directory from the PR.
2. **`arm/aes-gcm/Makefile` is missing.** Every other `arm/` subdirectory has
   one; #440 adds it. CI is green only because of the generic `%.o : %.S` rule,
   but `cd arm/aes-gcm && make` fails.
3. **Guard-test bit-lengths are all below 256 B**, so the dispatch-eligible band
   is never exercised. #440 also adds a false-positive check ("guard bypassed!")
   that re-encrypts `floor(bitlen/128)` blocks and asserts the output did *not*
   match. Worth adopting.
4. **Theorem naming.** Dropping the `_wb` infix put our theorems in the
   `AESV8_GCM_8X_DEC_256_*` namespace, which belongs to the non-WB upstream
   kernel. #440 kept `_WB_`. This should be settled jointly.
5. **Commit hygiene.** `5b5b6707` is titled "…decrypt kernel + KAT harness" but
   contains no KAT harness; the 513-line `arm/aes-gcm/kat/*` tooling is buried
   inside a proof commit. The five `Optimize:` commits carry no numbers — Part 2
   above has them.
6. **Proof-file hygiene.** Three mid-file `needs` (lines 1298, 6134, 6135),
   seven `Gc.compact()` calls, and process archaeology in the header comment
   ("[later] FRONT-N capture…", "CONSOLIDATED: … formerly a separate file").
7. **The `−117` deletions** are a rename touching three pre-existing XTS spec
   files we do not own (`ptext` → `xts_tv_ptext` etc., to avoid a HOL namespace
   collision with the shared spec layer). Rename-only, no functionality removed,
   but it must be called out in the PR body or a reviewer will ask.
8. **Spec-vocabulary divergence** with #440 is still an open TODO in commit
   `37e86d60`. Resolve before review — see the comments-to-#440 document.

### Collision surface with #440

Eight files are touched by both PRs; whichever lands second must reconcile.

| file | relationship |
|---|---|
| `tests/known_value_tests_gcm_256.h` | **byte-identical** |
| `tests/ref_gcm_v8table.c` | **byte-identical** |
| `tests/ref_gcm_nohw.c` | differs by +5 / −49 (we drop the encrypt-side dispatch) |
| `tests/test.c` | same insertion point |
| `benchmarks/benchmark.c` | same two hunks |
| `arm/Makefile` | both rewrite the same `AES_GCM_OBJ` / `OBJ =` lines |
| `include/s2n-bignum.h` | same insertion point |
| `specifications.txt`, `subroutine_signatures.ml`, `collect-signatures.py` | adjacent alphabetical inserts |

The two byte-identical files will auto-resolve on an add/add merge. The others
will not.
