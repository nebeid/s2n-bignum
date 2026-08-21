# Suggested PR description for awslabs/s2n-bignum#445

Draft for review. Replace the current placeholder body with the section marked
**PR BODY** below. Everything after that section is supporting material and
rationale, not intended for the PR itself.

## Status against the actual PR branch — read before pasting

**PR #445 head is `73638528` on `aes-gcm-dec-clean` (draft, CI 12/12 green).** Three
pieces of work described below are proved and gated on other branches but are
**NOT on the PR branch yet**, so the body must not claim them until the
mainloop → squashes → dec-clean re-flow has happened:

| item | state on `aes-gcm-dec-clean` @ `73638528` | where it is |
|---|---|---|
| the whole-blocks kernel + proof, tests, headers, build wiring | **present** — this is the PR today | — |
| `.balign 16` on the main loop | **absent** (0 occurrences) | `aes-gcm-wb-mainloop` `1735b5e7`+`541de123` |
| code size as `LENGTH …_wb_mc` instead of a literal | **absent** (34× literal `4968`) | `aes-gcm-wb-mainloop` `37715896`+`dd8740b2` |
| the fused 1–4 block path | **absent** (0 `w5r` labels, 0 `WB_FUSED` theorems) | `aes-gcm-splice-wip-s143` `d7b524e2` |

Sections below tagged **[PENDING FLOW]** describe work that is complete and
cold-gated but not yet on the PR branch. Either flow it first or delete those
sections before pasting — do not paste them as-is.

When porting, note that `dec-clean` spells every `.L`-prefixed label as `L`
(Mach-O's local prefix is `L`, and `.L` labels create atom boundaries CFI cannot
compute an `advance_loc` across). So `.L256_dec_main_loop` and the fused path's
twelve new labels all need renaming. The wrong spelling silently creates a new
label instead of the intended one.

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

Cold load times, from source at the CI pin, for reference when reviewing scope:
**2459 s** for the kernel as it stands on the PR branch, **2559 s** with the
alignment and `LENGTH …_wb_mc` changes, and **4011 s** with the fused path
spliced in. The last figure is above the repo's 30-minute norm and a refinement
pass to bring it down is queued — the load is dominated by ARM-simulation
proofs, several near-identical families of which can share one simulation.

**[PENDING FLOW]** The exported statements express the code region's length as
`LENGTH aesv8_gcm_8x_dec_256_wb_mc` rather than a hardcoded byte count, matching
`arm/proofs/aes_xts_{en,de}crypt.ml` and the sibling encrypt PR #440, so a
`.text`-size change needs no bookkeeping in the proof. The PR branch still spells
it as a literal in 34 places. Note for anyone repeating this: the ARM
store-safety check does numeric arithmetic on that length, so it must be reduced
back to a numeral at each simulation init — a mixed numeral/`LENGTH` state fails,
and an unreduced one fails at the fifth instruction with "could not prove that
updates will not modify the program code".

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

#### The fused short-message path — **[PENDING FLOW]**

A **fused** path covering 1–4 whole blocks (16/32/48/64 B). Proof-complete:
`WB_FUSED_{1,2,3,4}BLOCK`, each `hyps=0`, `axioms=3`, 0-CHEAT, re-validated
against upstream's current instruction model, and the spliced whole file
cold-gates at the CI-pinned HOL Light with `axioms=3` and both exported targets
bound at 0 hypotheses.

Differential benchmark, fused versus the non-fused kernel, both in one binary
with an A/A twin per variant. Negative = faster.

| size | V1 / Graviton3 | V2 / Graviton4 | V2 / r8g | V3 / Graviton5 |
|---:|---:|---:|---:|---:|
| 16 B | **−47.50 %** | *floor* | *floor* | **−46.17 %** |
| 32 B | **−42.52 %** | **−43.56 %** | **−43.54 %** | **−42.89 %** |
| 48 B | **−32.33 %** | **−37.66 %** | **−37.70 %** | **−40.31 %** |
| 64 B | **−21.92 %** | **−27.23 %** | **−27.24 %** | **−31.02 %** |
| 80 B | +0.28 % | −0.01 % | +0.01 % | −0.05 % |
| 128 B | −0.15 % | +0.28 % | +0.19 % | +0.03 % |
| 4096 B | −0.40 % | −0.02 % | −0.02 % | +0.00 % |

The win is strongly core-dependent — at 64 B it spans −21.9 % on V1 to −31.0 % on
V3 — so no single number represents that row. *floor* = the non-fused baseline
drew a bad 16 B link slot in that binary on the two V2 hosts (its own A/A floor
there is 4.38 % and 7.55 %), so no 16 B figure is claimed on those; V1 and V3
resolve it, and a separate median-estimator run on r8g independently gets
−46.4 % at 16 B, agreeing to 0.1–0.4 points with this table where they overlap.
A second run also covers the sizes this one omits: 256 B −0.22 %, 512 B +0.14 %,
1024 B +0.44 %, all inside their floors.

Structural, and the numbers reflect it: the fused bodies cover
`nblk ∈ {1,2,3,4}` only, and the `nblk ≥ 8` code is verified content-unchanged —
940 instructions diff-confirmed byte-identical **at the same offsets**, same
main-loop backedge — so every size from 80 B up is at or inside the floor.

**Differential size: `.text` grows to 5960 bytes.** Against the pre-`.balign`
kernel that is +992 B (+20.0 %); against the `.balign` kernel it is **+984 B
(+19.8 %)**, because the fused prologue's 8 extra bytes are absorbed by the
existing `.balign 16` — it emits zero padding instead of eight. Quote the figure
that matches whichever baseline lands. That absorption is also why the main loop
keeps the same address in both, so the fused measurement is not confounded by a
placement change.

Two caveats stated plainly. First, an earlier revision of these numbers reported
a +1.48 % penalty at 512 B; that was an artifact of a `min`-over-processes
estimator and has been **retracted** — a four-host study (32–40 processes each,
bootstrap CIs, 5 link permutations × 5 padding offsets) measured no regression on
any core. Second, aws-lc's current dispatch gates the 8x kernel on `len >= 256`
(moving to 128), so the sizes where fusion wins are not ones its dispatch routes
here today; the value is for callers that do, or for a future threshold change.

#### Main-loop alignment — **[PENDING FLOW]**

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

**Caveat on those four numbers:** they were measured on a *synthetic padded
probe*, not on the committed `.balign` object. The committed artifact is
`.text` 4976 B (md5 `a28d72a6…`) versus 4968 B without it, and it moves the main
loop from function offset 1208 (≡ 8 mod 16, the slow class) to 1216 (≡ 0). A
direct measurement of the two committed objects on all three cores is the right
evidence and should replace this table before the claim goes in the body.

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

1. ~~**`arm/aes-gcm/kat/Makefile` cannot build from a clean checkout.**~~
   **FIXED** in `73638528`. It required `aesv8_gcm_8x_dec_256.o` and
   `aesv8_gcm_8x_enc_256.o`, neither of which is in this change set, plus a
   hardcoded `AWS_LC_DIR ?= $(HOME)/workplace/git-code/aws-lc`. The directory is
   dropped; its seven aws-lc vectors are the same seven the `tests/test.c`
   known-answer test now drives through the production call path, so no coverage
   is lost.
2. ~~**`arm/aes-gcm/Makefile` is missing.**~~ **FIXED** in `73638528` — the
   `arm/aes-xts/Makefile` verbatim with the object list changed. Mirrored onto
   `aes-gcm-wb-mainloop` in `52e539f2` so the branches do not diverge on build
   files. Verified: `cd arm/aes-gcm && make` now works on both macOS and Linux.
3. **Guard-test bit-lengths are all below 256 B**, so the dispatch-eligible band
   is never exercised. #440 also adds a false-positive check ("guard bypassed!")
   that re-encrypts `floor(bitlen/128)` blocks and asserts the output did *not*
   match. Worth adopting. **Still open** — `73638528` widened only the *random
   differential* test's block-count draw (16..63 common, one-in-four on 16..23
   for the cascade and exact-8 drain, one-in-eight on 64..256 for the long
   main-loop path). The guard test itself is unchanged.
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
