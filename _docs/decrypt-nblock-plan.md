# AES-GCM decrypt: n-block plan (resumable handover)

**Purpose.** A self-contained, executable plan to extend AES-GCM **decrypt** from the
proven 1-block / ≤16-byte base up the band ladder to the full routine, mirroring the
encrypt build. Written so a **fresh session with no prior context can pick it up cold** —
follow the steps top to bottom, check the boxes, and update the RESUME pointer.

**Created:** 2026-06-22. **Branch:** `aes-gcm-nblock-tail`. **Permalinks pin commit `09fcb4c1`**
(s2n-bignum fork `nebeid/s2n-bignum`) unless noted.

---

## RESUME HERE (update this block every session)

- **Last completed step:** Step 0 (base proved: dec 1-block + LE1BLOCK). Plan doc created.
- **Next action:** Step 1 — build `AESV8_GCM_8X_DEC_256_2BLOCK` (dec analog of the enc 2-block).
- **Blocked on:** nothing.
- **Working file(s) in flight:** none yet (Step 1 will create `arm/proofs/aesv8_gcm_8x_dec_256_2block.ml`).
- **Backups:** none yet.

> When context gets heavy: write a `PROGRESS` comment block into the work file (what's proven,
> current subgoal, next steps, dead ends), do a numbered backup (bckNNNN), run `/compact`, read
> the work file back, and continue. Then update this RESUME block. A new session should read this
> doc top-to-bottom first, then the work file's PROGRESS block.
>
> **Git convention for this work: COMMIT freely, but do NOT push.** Commit each completed step
> (and progress checkpoints) so nothing is lost across `/compact` and session boundaries — commits
> are the durable handover. Pushing is left to the user: leave the branch ahead of origin and ask
> before `git push`. A fresh session continuing this plan should follow the same rule.
>
> **Default to NEW commits; do not amend unless the user explicitly asks.** Amending requires
> asking the user first (project rule), which means stopping — so to keep moving, just make a new
> commit for follow-up work rather than stopping to ask whether to amend. Amend only on an explicit
> user instruction (and never amend a pushed commit — that needs a force-push, also ask-first).
> It's fine if a step ends up as several small commits; that's preferable to interrupting.

---

## 0. Where we are (the base — DONE)

Proved end-to-end, no cheats, 3 core HOL axioms (`arm/proofs/aesv8_gcm_8x_dec_256_1block.ml`):

- [`AESV8_GCM_8X_DEC_256_1BLOCK`](https://github.com/nebeid/s2n-bignum/blob/09fcb4c1/arm/proofs/aesv8_gcm_8x_dec_256_1block.ml#L1843) (2026-06-11) — one whole block.
  Postcond: `out_p = word_xor cph (aes256_encrypt ctr0 keys)`, tag `= ghash_polyval_acc (byteswap128 h) (brev xi) [brev cph]`.
- [`AESV8_GCM_8X_DEC_256_LE1BLOCK`](https://github.com/nebeid/s2n-bignum/blob/09fcb4c1/arm/proofs/aesv8_gcm_8x_dec_256_1block.ml#L2385) (2026-06-13) — `bit_len = 8·bl`, `1 ≤ bl ≤ 16`.
- Both enter the body at `pc+0x18` (C_ARGUMENTS, XTS-style; prologue reorder).
- Methodology: [`_docs/aesv8-gcm-8x-dec-256-1block-methodology-20260611.md`](https://github.com/nebeid/s2n-bignum/blob/09fcb4c1/_docs/aesv8-gcm-8x-dec-256-1block-methodology-20260611.md) (read §0 "five things that make decrypt different", §1 "what is shared", §2 "s350 vs s351 bridge pitfall").

**Decrypt is leading-edge:** Mila's [`aes256_gcm_tail`](https://github.com/manastasova/s2n-bignum-dev/tree/004b1a06f621c514f73a37a303b9e1bd10d0827b) has **no GCM decrypt** — there is nothing to converge against, so we are not blocked on her. We *do* adopt her GHASH layer (Step 3).

**The one structural fact that makes this cheap (verified in the 1-block proof):** the decrypt
modulo reduction is **algebraically identical** to encrypt's (dec just splits each `eor3` into
two `eor`s), so `GMULT_FULL_CORRECT_BA` and the whole GHASH bridge transfer. CTR is symmetric:
the dec keystream is the same `aes256_encrypt (ctr) keys`; only the spec's "data" argument is the
**ciphertext `cph`** (dec) instead of plaintext (enc). **Everywhere the encrypt proof says
`plaintext` / `pt`, decrypt says `cph`, and the out_p store is the plaintext `word_xor cph keystream`.**

---

## The mirror principle (how every step works)

Each decrypt band is the encrypt band with: (1) `pt → cph` in the spec/abbreviations, (2) the
out_p store materialized as plaintext = `word_xor cph (aes256_encrypt ctr keys)` (enc stores the
ciphertext, the symmetric mirror), (3) the GHASH data block = `brev cph` (masked: `brev (word_and cph MK)`),
(4) the dec bridge at **s351 not s350** (dec splits the final `eor3`; see methodology §2), (5)
dec entry/exit PCs (dec routine is 4612 bytes; `nonoverlapping (word pc, 4612)` — NOT 4600).
Everything else — front CTR/AES sim, cascade control flow, mask collapse, reduction lane-blast —
is the same tactic block.

**Encrypt references to mirror (all at `09fcb4c1`):**
- enc 2-block: [`AESV8_GCM_8X_ENC_256_2BLOCK`](https://github.com/nebeid/s2n-bignum/blob/09fcb4c1/arm/proofs/aesv8_gcm_8x_enc_256_2block.ml) (`arm/proofs/aesv8_gcm_8x_enc_256_2block.ml`).
- enc 17–31 band: [`AESV8_GCM_8X_ENC_256_LE2BLOCK`](https://github.com/nebeid/s2n-bignum/blob/09fcb4c1/arm/proofs/aesv8_gcm_8x_enc_256_le2block.ml#L132) + [`..._BYTELIST`](https://github.com/nebeid/s2n-bignum/blob/09fcb4c1/arm/proofs/aesv8_gcm_8x_enc_256_le2block.ml#L401). Helper resolvers to copy: `USHR_128_8BL_LEMMA`, `X5_ZERO_LEMMA2`, `IVAL_WORD_LE32`, `IVAL_WSUB_LE32` (lines 31–67 of that file).
- shared spec bridges: [`BYTE_LIST_AT_NBLOCK_CTR`](https://github.com/nebeid/s2n-bignum/blob/09fcb4c1/arm/proofs/utils/aes_ctr_spec.ml#L406) (`arm/proofs/utils/aes_ctr_spec.ml`) — the N-1 full + masked-tail readback bridge; already generic, reuse directly.

---

## Steps (checklist — work top to bottom)

### [ ] Step 1 — `AESV8_GCM_8X_DEC_256_2BLOCK` (two whole blocks)
- **Create** `arm/proofs/aesv8_gcm_8x_dec_256_2block.ml`, mirroring `aesv8_gcm_8x_enc_256_2block.ml`.
  `needs "arm/proofs/aesv8_gcm_8x_dec_256_1block.ml"` (gives the dec mc/EXEC + GHASH bridge lemmas).
- Spec: `out_p` blocks 0,1 = `EL i (aes_ctr ...)` over **ciphertext** inputs; tag over `MAP brev (aes_ctr ...)`.
  Block-1 counter = `gcm_ctr_inc ctr0`; same htable preconds as enc 2block.
- GHASH: the 2-block batched fold closes via `GHASH_POLYVAL_ACC_2` exactly as enc (data blocks
  `brev cph0`, `brev cph1`). **Bridge at the dec state (s351-analog), not s350.**
- **Acceptance:** `loadt` clean, theorem binds, no `CHEAT_TAC`/`new_axiom`, `axioms()` = 3 core. Numbered backup.

### [ ] Step 2 — `AESV8_GCM_8X_DEC_256_LE2BLOCK` (17–31 byte band: 1 full + 1 masked partial)
- **Create** `arm/proofs/aesv8_gcm_8x_dec_256_le2block.ml`, mirroring `aesv8_gcm_8x_enc_256_le2block.ml`.
  `needs "arm/proofs/aesv8_gcm_8x_dec_256_2block.ml"`.
- `bit_len = 128 + 8·bl1`, `1 ≤ bl1 ≤ 16`. Swap LE1BLOCK's symbolic mask `MK = word(2 EXP (8*bl1)-1)`
  into block 1. Copy the four x5-cascade resolvers (`USHR_128_8BL_LEMMA`/`X5_ZERO_LEMMA2`/`IVAL_*`).
- masked block-1 out store = plaintext blend `word_xor (word_and ... MK) (...)` (dec mirror of enc's masked CT store).
- GHASH data block 1 = `brev (word_and cph1 MK)`.
- **Acceptance:** as Step 1. Also prove `..._LE2BLOCK_BYTELIST` (Step 5 form) if cheap here.

### [ ] Step 3 — adopt Mila's GHASH layer for the dec bands (do alongside/after Step 1–2)
- Per the **D7 measurement** (`_docs/gcm-spec-divergence-from-mila-handback.md`, "D7 — MEASURED"):
  Mila's `ghash_Nblock_karatsuba` + `GHASH_NBLOCK_KARATSUBA_EQ_PROP3` close the GHASH conjunct in
  ~0.05–0.10s vs our `MERGE_2BLK`/`FINISH_2BLK` ~73s/band, and scale flat.
- The spike `_spike/time_ghash_closure.ml` (+ `_spike/mila_nblock_layer.ml`) is the worked recipe;
  the closure for the dec bands is identical (the data block is `brev cph`, the rest unchanged).
- **Reconciliation recipe (from the spike):** the s367-analog Q19 is the inner `word_join g f`
  (her spec's outer `word_reversefields 8` = the ext+rev64 two steps later); htable lanes carry raw
  `h..h^N` with GHASH key `byteswap128 htw`; discharge `kara_quad_ok` via `BYTESWAP128_INVOLUTION`
  + `karatsuba_mid` symmetry; H-power preconds bridge to `GHASH_POLYVAL_ACC_N`; N≥3 needs one
  `AP_TERM_TAC THEN CONV_TAC WORD_RULE` for XOR-assoc.
- **Decision:** use Mila's layer for ≥3-block dec bands; for 2-block either route works (ours already proven).

### [ ] Step 4 — ≥2-full-block + masked tail bands (33+ bytes)
- Mirror the enc ≥2-full + tail bands using [`BYTE_LIST_AT_NBLOCK_CTR`](https://github.com/nebeid/s2n-bignum/blob/09fcb4c1/arm/proofs/utils/aes_ctr_spec.ml#L406) at `nfull = 2,3,...`.
  (At time of writing, the enc side has these as the next bands too; if enc lands them first, mirror that file.)
- GHASH via Step 3 (Mila's layer).

### [ ] Step 5 — byte-list output postcond for dec
- `byte_list_at (...) out_p len` form, analog of `AESV8_GCM_8X_ENC_256_LE2BLOCK_BYTELIST`.
  Derive as a **cheap postcond-weakening corollary** of each band theorem (no re-simulation), as enc does.

### [ ] Step 6 — whole-function `AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT`
- Wrap the dec body core (pc+0x18) with `ARM_ADD_RETURN_STACK_TAC` to prove the prologue/epilogue
  and produce a pc+0 whole-function theorem — the XTS pattern, see
  [`AES_XTS_ENCRYPT_SUBROUTINE_CORRECT`](https://github.com/nebeid/s2n-bignum/blob/bb2e2585/arm/proofs/aes_xts_encrypt.ml#L5563)
  (callee list `[D8;...;D15]`, 80-byte frame). This is the **D10** plan, shared with encrypt.
- Note: this and the prologue-reorder convention are pending the convergence message to Mila
  (`_docs/message-to-mila.md`); coordinate so dec + enc settle the same stack posture once.

### [ ] Step 7 — scale to 4/8 blocks + the main loop (`Loop_mod2x`)
- Mirror the enc 4/8-block + main-loop work once that lands on encrypt. GHASH via Mila's layer (general N).
- Then converge the dec spec onto the shared `aes256_encrypt` primitive (D2) — dec already uses it, so this is naming only.

---

## Reproduce / verify (any step)
```
# in HOL MCP, cwd = project root, base.ml preloaded:
loadt "arm/proofs/aesv8_gcm_8x_dec_256_<file>.ml";;
# then check: no CHEAT_TAC/new_axiom in the file; `axioms();;` shows only the 3 core HOL axioms.
```
Dec 1-block loads in ~239–256s; each band file `needs` the one below it, so a band loadt includes
that cost. Run `Gc.compact ();;` after heavy sims.

## Cross-references
- Encrypt n-block plan (the parent; decrypt was Task 6c there): `_docs/aesv8-gcm-nblock-generalization-plan-20260617.md`.
- Dec 1-block methodology (the hard-won tactics): `_docs/aesv8-gcm-8x-dec-256-1block-methodology-20260611.md`.
- GHASH approach + D7 timing: `_docs/gcm-spec-divergence-from-mila-handback.md`; spike `_spike/`.
- Convergence message to Mila (D2/D7/D8/D10): `_docs/message-to-mila.md`.
