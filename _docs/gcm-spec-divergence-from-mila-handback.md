# AES-GCM spec: where our layer diverges from Mila's (handback to Mila)

**Purpose.** A running record of where the s2n-bignum-kiro (nebeid) AES-GCM spec layer
diverges from Mila's `aes256_gcm_whole` branch
(`manastasova/s2n-bignum-dev@756df852`), WHY, and which side is more
concise / elegant / faster (with measured load times where available). Hand this back to
Mila to converge on ONE shared spec home.

**Status:** started 2026-06-18. Updated as the byte_list_at output layer is wired
(plan Tasks 5/6).

---

## TL;DR — the big realization

Mila has **already built and proven the entire `byte_list_at` output spec layer**
(`bytes_to_int128` / `int128_to_bytes` / `byte_list_at` / `gcm_ct_bytes_rec` /
`gcm_ctm_tail` / `aes256_gcm_encrypt` / `gcm_final_xi` + the `OUT_BRIDGE_GEN` masked-tail
bridge + `GHASH_BLOCKS_1..8`). This is exactly the generic, length-uniform output spec we
concluded is the right target for the whole algorithm. So our job is **adopt + bridge to
OUR binary**, NOT rebuild. The only genuine divergences are (1) the AES block primitive and
(2) the binary entry/frame — everything else should converge to her names.

---

## Side-by-side: names + shapes

| Concept | Mila (`@756df852`) | Ours (kiro) | Verdict |
|---|---|---|---|
| Counter increment | `gcm_ctr_inc` | `gcm_ctr_inc` | **IDENTICAL** (we lifted hers verbatim into `arm/proofs/utils/gcm_ctr_helpers.ml`) |
| Counter iterator | `gcm_ctr_iter` (`new_recursive_definition`: `SUC n => gcm_ctr_inc (gcm_ctr_iter n)`) | `gcm_ctr_inc_iter` (`define`, same recursion) | **SAME RECURSION, different NAME** — converge on `gcm_ctr_iter` (hers). See Divergence D1. |
| NIST inc32 | `inc32` (in `common/gcm.ml`) | `inc32` (copied from PR#389) | IDENTICAL (both copy PR#389) |
| inc32↔ctr bridge | (not present in her files surveyed) | `GCM_CTR_INC_INC32`, `GCM_CTR_INC_ITER_INC32` | **OURS ADDS** the NIST byteswap bridge. Candidate @UPSTREAM-389. |
| AES block primitive | `aes256_block_enc` (flat 15-arg `aesmc(aese ...)` tower — the ARM instruction form) | `aes256_encrypt` (list-arg, `aes256_encrypt_round` fold + explicit `aes_shift_rows`/`aes_sub_bytes` final round) | **DIVERGENT.** See Divergence D2 (the one real obstacle). |
| Keystream | `gcm_keystream i ivec rks = aes256_block_enc (gcm_ctr_iter i ivec) (EL 0 rks)..(EL 14 rks)` | (implicit in `aes_ctr_block` = `word_xor pt (aes256_encrypt (gcm_ctr_inc_iter k ctr0) keys)`) | converge on `gcm_keystream` once D2 resolved |
| Recursive CT (int128 list) | `gcm_ct_rec` (`new_specification` + `prove_general_recursive_function_exists`) | `aes_ctr_rec` (`define`, plain structural recursion on the block list) | **OURS SIMPLER** (no WF measure). See Divergence D3. |
| Recursive CT (byte list) | `gcm_ct_bytes_rec` (APPEND of `int128_to_bytes`) | (not built — we stop at int128 list) | hers needed for `byte_list_at`; adopt |
| Masked partial tail | `gcm_ctm_tail i tail .. = word_and ct (word (2 EXP (8*tail)-1))` | LE1BLOCK postcond inline: `word_and CT (word (2 EXP (8*bl)-1))` | **IDENTICAL mask form** — adopt `gcm_ctm_tail`. |
| Top CT spec | `aes256_gcm_encrypt len P ivec rks : byte list` | `aes_ctr ctr0 pts keys : int128 list` | hers is the length-uniform `byte list`; adopt as the OUTPUT TARGET. Ours is the int128 block layer underneath. |
| Output postcond | `byte_list_at (aes256_gcm_encrypt ...) out_p len s` (ONE clause, all lengths) | `EL i (aes_ctr ...)` per block (+ LE1BLOCK masked `bytes128` for partial) | **HERS more elegant for whole algorithm.** Adopt. |
| Tag spec | `gcm_final_xi len P ivec rks xi h` | inline `word_bytereverse (ghash_polyval_acc (byteswap128 h) (brev xi) (MAP brev (aes_ctr ...)))` | adopt `gcm_final_xi` (same shape; hers uses `word_reversefields 8` = our `byteswap128`/`brev`) |
| GHASH block list | `gcm_ghash_blocks len P ivec rks` (+ `GHASH_BLOCKS_1..8`) | `MAP word_bytereverse (aes_ctr ...)` | adopt `gcm_ghash_blocks` |
| Output readback bridge | `OUT_BRIDGE_GEN` (N-1 full + masked tail ⇔ `byte_list_at`), `BYTE_LIST_AT_BLOCK`, `INPUT_*` | (none — we read per-block `bytes128`) | adopt; these are the reusable Task 5 bridges |

---

## Divergences (numbered, for Mila)

### D1 — counter iterator name: `gcm_ctr_iter` (hers) vs `gcm_ctr_inc_iter` (ours)
SAME definition (recursive, `SUC n => gcm_ctr_inc (...)`). Ours additionally proves
`= ITER k gcm_ctr_inc` and the NIST bridges. **Resolution: rename ours to `gcm_ctr_iter`**
(hers, fewer chars, already upstream-shaped); keep our extra lemmas (`_ITER`, `_1`, `_ADD`,
`_INC32`) attached to her name. No semantic divergence. Cost: trivial rename in
`gcm_ctr_helpers.ml` + `aes_ctr_spec.ml`.

### D2 — AES block primitive: `aes256_block_enc` (hers) vs `aes256_encrypt` (ours) — THE real obstacle
- Hers: `aes256_block_enc input rk0..rk14` = flat 15 register args, body is the literal ARM
  `aesmc (aese ...)` 14-round tower (matches the instruction trace directly).
- Ours: `aes256_encrypt block keys` = `int128 list` keys, `aes256_encrypt_round` fold, with the
  final round written as explicit `aes_sub_bytes joined_GF2 (aes_shift_rows ...)` then XOR.
- They compute the SAME AES-256, but are NOT syntactically equal: her last round is
  `aese s12 rk13` (aese bundles shift_rows+sub_bytes+addroundkey), ours splits the last round.
- **No `aes256_block_enc ⇔ aes256_encrypt` bridge exists in either tree.** It is provable: our
  2-block proof ALREADY rewrites `aes256_encrypt` down to the same `aese`/`aesmc` tower
  (`aesv8_gcm_8x_enc_256_2block.ml:761` — `REWRITE_TAC[aes256_encrypt_round; aese; aesmc]`), which
  is exactly her `aes256_block_enc` form. So a `AES256_BLOCK_ENC_EQ_ENCRYPT` lemma is bounded
  work (unfold both to the aese/aesmc tower; the last-round split reconciles via the aese/aesmc
  defs). **Action: prove it once, put it in the shared utils, then her keystream/output spec
  drops onto our binary.** This is the gating item for adopting her `byte_list_at` layer here.
- Which is more elegant? Hers (`aese`/`aesmc`) is closer to the metal / the proof's working
  form; ours (`aes256_encrypt`) is the abstract FIPS-197 form used across the kiro AES/XTS
  proofs. Neither is wrong — they sit at different abstraction levels and want a bridge, not a
  merge. (Open question for Mila: standardize the GCM *spec* on the abstract `aes256_encrypt`
  with `aes256_block_enc` as the proof-side unfolding, or vice versa?)

### D3 — recursive ciphertext: `define` (ours) vs `new_specification`+WF (hers)
- Hers: `gcm_ct_rec`/`gcm_ct_bytes_rec` via `prove_general_recursive_function_exists` (recurses
  on a numeric `nfull` count, decreasing).
- Ours: `aes_ctr_rec` via plain `define` structural recursion on the block LIST.
- **Ours is more concise** (no WF-measure / existence boilerplate — plan risk R3 avoided) AND
  proves `LENGTH`, a generic `EL_AES_CTR` (element i for any N), and 2-block reductions cheaply.
  loadt of our whole `aes_ctr_spec.ml` = **2.5s**.
- Caveat: hers recurses on the byte list with SUB_LIST windows (needed because her top spec is
  byte-level and length-generic incl. a non-block tail); ours is block-list. To feed
  `byte_list_at` we still need a byte-level top spec — so the likely convergence is: keep our
  structural `aes_ctr_rec` as the int128 block layer, add a thin `bytes_to_int128`/`SUB_LIST`
  adapter to reach her byte-list `aes256_gcm_encrypt`, mirroring how XTS bridges its int128
  round spec to its byte_list top spec. **Measure both once wired; record here.**

### D4 — binary entry + stack frame (NOT a spec divergence, but affects theorem shape)
- Hers: whole routine `aes256_gcm.o`, entry pc+0, full 80-byte prologue/epilogue, `SP =
  stackptr+80`, MAYCHANGE carries the full frame (`MAYCHANGE [SP]` + `bytes64 stackptr..+72`).
- Ours: per-call `aesv8_gcm_8x_enc_256.o`, entry pc+0x18 (C_ARGUMENTS, prologue skipped),
  MAYCHANGE carries only `bytes(stackpointer+64,16)` (the Prop3 reduction-constant spill).
- This is the Q-binary finding (SAME source routine, different entry). Her spec layer is
  binary-agnostic and transfers; her concrete sim/closers (ARM_STEP from pc+0) do not.

### D5 — her MAYCHANGE output is `bytes(out_ptr,128)`; ours is `bytes(out_p,32)`
Both round up to the full register region (she covers up to 8 blocks; we cover 2). Same idea,
different N. Converges automatically when we state our band over `byte_list_at ... len`.

---

## DECISION (2026-06-18): reuse the XTS substrate → sidesteps D2

Both our tree AND Mila's `byte_list_at` / `bytes_to_int128` / `int128_to_bytes` are
**byte-identical copies of the AES-XTS originals** (`arm/proofs/utils/aes_xts_common.ml:17`,
`aes_xts_common_spec.ml:19,29`). And XTS's own output spec (`aes256_xts_encrypt_round`) is
built on **`aes256_encrypt`** — OUR primitive, the one our binary simulation produces — NOT
`aes256_block_enc`.

So the maximum-reuse path (what XTS is built on) is: build the GCM output layer on the
**existing XTS `byte_list_at`/`bytes_to_int128`/`int128_to_bytes` + `aes256_encrypt`**. This
**ELIMINATES divergence D2** (no `aes256_block_enc ⇔ aes256_encrypt` bridge needed) while
staying name-compatible with Mila for free (she copied the same XTS defs). The ONLY thing we
decline to adopt from Mila is her `aes256_block_enc` substitution; everything else converges.

Concrete shape (mirrors XTS `aes256_xts_encrypt_rec` → `aes256_xts_encrypt : byte list`):
- block layer  = our `aes_ctr` (int128 list, structural recursion) — keep (D3).
- byte top spec = `aes_ctr_bytes ctr0 P keys : byte list` = APPEND of `int128_to_bytes` over
  full blocks ++ `SUB_LIST(0,tail)(int128_to_bytes (masked last block))` — SAME shape as Mila's
  `aes256_gcm_encrypt`, but keystream via `aes256_encrypt` (XTS substrate) not `aes256_block_enc`.
- masked tail  = `word_and ct (word (2 EXP (8*tail)-1))` — identical to Mila's `gcm_ctm_tail`
  AND our LE1BLOCK.
- output postcond = `byte_list_at (aes_ctr_bytes ...) out_p len s`.
- readback bridge = GCM analog of XTS `READ_BYTES_EQ_READ_BYTE128_*BLOCKS` (reuse XTS proof shape).

For Mila: if she standardizes her keystream on `aes256_encrypt` (the XTS substrate) instead of
`aes256_block_enc`, our layers become a single shared file with no D2 bridge at all. That is the
recommended convergence (D2 resolution = "use the XTS primitive both XTS and we already use").

## Recommended convergence path (proposed; confirm with Mila)
1. **Adopt her spec NAMES** for the output/tag layer (`byte_list_at`, `bytes_to_int128`,
   `int128_to_bytes`, `gcm_keystream`, `gcm_ct_bytes_rec`, `gcm_ctm_tail`, `aes256_gcm_encrypt`,
   `gcm_final_xi`, `gcm_ghash_blocks`) + the bridges (`OUT_BRIDGE_GEN`, `BYTE_LIST_AT_BLOCK`,
   `INPUT_*`, `GHASH_BLOCKS_*`) into ONE shared file both trees `needs`.
2. **Rename ours** `gcm_ctr_inc_iter → gcm_ctr_iter` (D1).
3. **Prove `AES256_BLOCK_ENC_EQ_ENCRYPT`** once (D2) so her keystream spec composes with our
   binary's `aes256_encrypt` readbacks. Decide the canonical spec-side primitive.
4. **Keep our `aes_ctr_rec` (structural)** as the int128 block layer; bridge it to her byte-list
   `aes256_gcm_encrypt` with a thin SUB_LIST adapter (D3). Compare load times; record winner here.
5. Wire OUR binary's 2-block (then N-block) theorem to `byte_list_at (aes256_gcm_encrypt ...)
   out_p len` over `1 ≤ len ≤ 32`, discharged via `OUT_BRIDGE_GEN` + the AES bridge.

## Measured timings (fill in as we go)
| Item | Load time | Axioms | Notes |
|---|---|---|---|
| `gcm_ctr_helpers.ml` (ours) | 1.90s | 3 | counter core |
| `aes_ctr_spec.ml` (ours, int128 layer only) | 2.5s | 3 | int128 CTR list spec |
| `aes_ctr_spec.ml` (ours, + byte-list layer) | 94s | 3 | adds `needs aes_xts_common.ml` (GF/tweak machinery is the cost); `aes_ctr_bytes` byte spec built on XTS substrate + aes256_encrypt, name/shape-compatible with Mila's `aes256_gcm_encrypt` |
| Mila's `aes256_gcm.ml` | (not measured) | — | 8305 lines incl. all proofs |
| `byte_list_at` postcond wiring on our 2-block | ~1050s (full binary loadt) | 3 | DONE for whole-block (len=32). `AESV8_GCM_8X_ENC_256_2BLOCK_BYTELIST` proved: out_p postcond is one `byte_list_at (aes_ctr_bytes ...) out_p (word 32)` clause. Derived as a CHEAP postcond-weakening corollary of the main theorem (no re-simulation). |

## Where we stand vs Mila (status 2026-06-19)

**Output postcondition shape: PARITY reached (whole-block).** Our
`AESV8_GCM_8X_ENC_256_2BLOCK_BYTELIST` now states the output exactly like Mila's
`AES256_GCM_ENCRYPT_CORRECT`: a single `byte_list_at (<top ct spec>) out_p len s` clause.
Our top ct spec is `aes_ctr_bytes` (= `int128_list_to_bytes (aes_ctr ...)`); hers is
`aes256_gcm_encrypt`. Same SHAPE, and both reduce to `int128_to_bytes` of the per-block
`word_xor pt (cipher (ctr) keys)`. The substantive remaining differences are the two
divergences below, plus that hers is length-generic (`val len <= 128`) while ours is fixed
at `len = 32` (2 whole blocks) so far.

**How we got byte_list_at without an `aes256_block_enc` bridge (D2 stays resolved):** the
whole readback chain reuses the AES-XTS substrate verbatim -- `byte_list_at`,
`bytes_to_int128`/`int128_to_bytes`, `READ_BYTES_AND_BYTE128_SPLIT`,
`READ_MEMORY_BYTES_BYTES128`, `BYTE_LIST_TO_NUM_THM`, the `*_INT128_TO_BYTES` round-trip
lemmas (all in `aes_xts_common.ml`) -- built on `aes256_encrypt`. New shared bridges added
(`aes_ctr_spec.ml`): `CTR_BLOCK0_BYTES16`, `READ_BYTES_EQ_BYTE128_2BLOCKS_CTR`,
`BYTE_LIST_AT_2BLOCKS_CTR` (the GCM analogs of XTS `READ_BYTES_EQ_READ_BYTE128_*BLOCKS_ENC`).

**Outstanding to fully match Mila's whole-routine theorem:**
1. **Partial tail 1 <= bl <= 16: DONE (2026-06-19).** `AESV8_GCM_8X_ENC_256_LE1BLOCK_BYTELIST`
   proves the out_p postcond as `byte_list_at (aes_ctr_tail_bytes ctr0 plaintext keys bl) out_p
   (word bl) s` for the masked partial single block -- the nfull=0 tail of Mila's
   `aes256_gcm_encrypt`/`gcm_ctm_tail`. Built on a shared masked-tail bridge
   `BYTE_LIST_AT_TAIL_CTR` + the byte-extraction sublemmas PORTED VERBATIM from Mila
   (`BYTE8_OF_BYTES128`, `SUBWORD_BYTES_TO_INT128`, `EL_SUB_LIST_0`, `EL_INT128_TO_BYTES`,
   `MASK_BYTE_OUT`; names per R5). Confirmed our LE1BLOCK mask form
   (`word_xor (word_and CT mask) (word_and outprev (word_not mask))`) = Mila's `gcm_ctm_tail`
   blend; `MASK_BYTE_OUT`/`MASK_BYTE_OUT_XOR` cover both or/xor forms. Derived as a cheap
   postcond-weakening corollary of `AESV8_GCM_8X_ENC_256_LE1BLOCK` (no re-simulation). loadt
   ~757s, 3 axioms.
1b. **GENERAL N-block masked-tail bridge DONE (2026-06-19, spec-level).**
   `BYTE_LIST_AT_NBLOCK_CTR` (in `aes_ctr_spec.ml`) is the full **OUT_BRIDGE_GEN analog**:
   `nfull` full-block `bytes128` stores (= `EL k (aes_ctr ...)`) + one masked-tail store
   (block `nfull`, `1<=tail<=16`) ==> `byte_list_at (aes_ctr_full_tail_bytes ...) out_p len`
   for `val len = 16*nfull+tail`. Unifies the whole-block and partial-single-block bridges;
   proved by byte-index case split exactly like Mila's `OUT_BRIDGE_GEN`, reusing the ported
   `BYTE8_OF_BYTES128`/`MASK_BYTE_OUT_XOR`/`EL_*` sublemmas + new `EL_INT128_LIST_TO_BYTES`,
   `DIV16_STEP`/`MOD16_STEP`, `LENGTH_INT128_LIST_TO_BYTES_SUBLIST`. Spec-level (loadt 95s,
   3 axioms, no cheats) -- this is what the 17..32-byte band and the 4/8-block tail
   simulations consume directly. STILL OPEN: instantiate it on the binary for the 17..32-byte
   2-block band (1 full + masked partial); then 4/8 + main loop.
2. **D1 rename** `gcm_ctr_inc_iter -> gcm_ctr_iter` (cosmetic; defer to the shared-file merge).
3. **D2 spec-primitive convergence:** recommend Mila standardize her keystream on
   `aes256_encrypt` (the XTS primitive) so the two layers become ONE shared file with no
   `aes256_block_enc`. Until then our layer and hers differ only by that primitive.
4. **Scale to 4/8 blocks + the main loop** (Loop_mod2x_v8) -- unchanged from the plan.

## Spec layer built so far (ours, reusing XTS substrate)
`arm/proofs/utils/aes_ctr_spec.ml` now has BOTH layers:
- int128 block layer: `aes_ctr_block` / `aes_ctr_rec` / `aes_ctr` + `LENGTH_AES_CTR` /
  `EL_AES_CTR` (any N) / `AES_CTR_2_EL` / `AES_CTR_2_MAP_BREV`.
- byte-list layer (XTS-substrate, NO aes256_block_enc): `int128_list_to_bytes` +
  `LENGTH_INT128_LIST_TO_BYTES` + `aes_ctr_bytes` (= `int128_list_to_bytes (aes_ctr ...)`) +
  `LENGTH_AES_CTR_BYTES` + `AES_CTR_BYTES_2`. This is the value a `byte_list_at(out_p,32)`
  postcond unfolds to; whole-block (tail=16) only so far.
