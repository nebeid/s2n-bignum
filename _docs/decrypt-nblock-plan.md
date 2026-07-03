# AES-GCM decrypt: n-block plan (resumable handover)

**Purpose.** A self-contained, executable plan to extend AES-GCM **decrypt** from the
proven 1-block / ≤16-byte base up the band ladder to the full routine, mirroring the
encrypt build. Written so a **fresh session with no prior context can pick it up cold** —
follow the steps top to bottom, check the boxes, and update the RESUME pointer.

**Created:** 2026-06-22. **Last consolidated:** 2026-06-29 (folded in the
`dec-tail-more-bands-handoff` band detail + the `le3block_NOTES` what-worked/didn't
lessons + the readable-spec architecture). **Branch:** `aes-gcm-nblock-tail`.

---

## RESUME HERE (update this block every session)

- **Last completed:** the **≤4-block ladder is proved AND the chain is homogenized** —
  `LE1BLOCK` (nfull=0), `LE2BLOCK`(+`_BYTELIST`, nfull=1), `LE3BLOCK`(`_BODY`+readable, nfull=2),
  and **`LE4BLOCK`(`_BODY`+readable, nfull=3, 49–64 bytes)**, all in arm/proofs as committed proof
  files, cold-load-clean end-to-end, hyps=0, axioms()=3, no cheats. LE4BLOCK was promoted from the
  WIP to `arm/proofs/aesv8_gcm_8x_dec_256_le4block.ml`.
- **RECURSIVE SPEC DONE (2026-07-01, matches Mila's PR):** the readable LE3/LE4 wrappers now state
  their postcondition over the WHOLE input buffer `x` via recursive spec functions — the block
  expansion is hidden inside the definition (like Mila's `gcm_ghash_blocks`/`gcm_final_xi`/
  `aes256_gcm_encrypt` on branch `mila/aes256_gcm_tail`, tip 14154e49). New file
  `arm/proofs/utils/aes_gcm_dec_spec.ml`: `gcm_dec_ghash_blocks`/`gcm_dec_final_xi` (tag) +
  `gcm_dec_pt_bytes` (output, over `aes_ctr_full_tail_bytes`) + `gcm_dec_blocks_from` (recursive
  int128 block-list view of `x`), plus per-N unfold lemmas `GCM_DEC_GHASH_BLOCKS_1..8` /
  `GCM_DEC_PT_BYTES_1..8` (dec analogues of her `GHASH_BLOCKS_N`). Wrapper POST is now
  `byte_list_at (gcm_dec_pt_bytes (16*nfull+bl1) x ctr0 keys) out_p (word len) s` and
  `read xi_p = gcm_dec_final_xi (16*nfull+bl1) x xi h`; proof = `ASM_SIMP[gcm_dec_final_xi;
  GCM_DEC_GHASH_BLOCKS_(nfull+1); GCM_DEC_PT_BYTES_(nfull+1); MAP]` then the unchanged
  BYTE_LIST_AT bridges. GOTCHA: don't use `o` as a placeholder var in a HOL term — it's the
  composition operator ("Unparsed input following term"); use `ofs`. le1/le2 keep the per-block-cph
  presentation (foundational bands, unified later by dispatch).
- **HOMOGENIZATION DONE (2026-06-30):**
  - **Shared fast GMULTn builder** `common/gmult_nblock_lemmas.ml` (`build_GMULTn_fast n`) — used by
    2block (GMULT2), le3block (GMULT3), le4block (GMULT4). Replaced the per-band hand-written
    `decN_tL` + monolithic `CONV_TAC WORD_RULE` PACK (~30s at N=2, ~373s at N=3, never finished at
    N=4) with a ~0.3s structural build. Verified to reproduce GMULT2/GMULT3 concl EXACTLY.
  - **Whole-block theorems REMOVED** (covered by the LE bands at bl1=16, referenced nowhere):
    `AESV8_GCM_8X_DEC_256_1BLOCK` (→ LE1BLOCK), `2BLOCK` + `2BLOCK_BYTELIST` (→ LE2BLOCK). The
    1block/2block files are retained ONLY for their shared infra (EXEC rule, lemmas, MERGE/bridge
    tactics, GMULT2). Cold-load times dropped: 1block 527→324s, 2block 590→105s, le3block 1150→783s;
    full chain ~3400→~2650s.
  - **le3block LAYER 2 wrapper bug fixed**: the PRE branch used `INPUT_BRIDGE_3` (needs a raw
    `read(memory:>bytes(in_p,48))=num_of_bytelist x` that the wrapper PRE never supplies) and left
    "TAC_PROOF: Unsolved goals" on a genuine fresh load. Switched to `BYTE_LIST_AT_3BLOCKS` pos=0
    (the same shape le4 uses with `BYTE_LIST_AT_4BLOCKS`). Wrapper-PRE recipe is now uniform across bands.
- **Band coverage DESIGN ANSWER (objdump, b.gt strict cascade):** LE-N band (nfull) covers
  bytes [16·nfull+1, 16·(nfull+1)] INCLUSIVE; the bl1=16 endpoint = whole-(N+1)-block
  (all-ones mask ⇒ full block). So **LE4BLOCK INCLUDES the whole-4-block (64 byte) case**;
  whole-3-block (48 byte) is inside LE3BLOCK; whole-2/whole-1 inside LE2/LE1. **No separate
  whole-block theorems are needed for any band** — and the redundant ones have now been removed.
- **LE4BLOCK two root-cause fixes (the hard parts):** (1) opaque-Q7 masked-block keystream —
  v7=ctr+3=original-v3 keystream propagated by the tail shift movs; the bulk discard `[3;4;5;6;7]`
  killed original-v3. Fix: keep Q3 (`[4;5;6;7]`), ABBREV the 4 surviving keystreams at s269, step
  the cascade with PLAIN ARM_STEPS (VSTEPS OOMs). (2) collapse the masked GHASH input to `cphm` at
  s368 (after `and v9,v9,v0`) BEFORE the rev64 at s371, else the bridge's masked qq atom carries the
  raw form and won't merge. Bridge taken at s392 (after `eor v19,v19,v18`); exit pc+4580.
- **Next action:** Step 4 (≤3-block dispatch, cheap, no sim) and Step 5 nfull=4..6 (LE5..LE7) — each
  = +1 full GHASH round + `build_GMULTn_fast N` + the same front/stores/masked-tail/bridge templates.
- **Blocked on:** nothing.

> When context gets heavy: write a `PROGRESS` comment block into the work file (what's proven,
> current subgoal, next steps, dead ends), do a numbered backup (bckNNNN), run `/compact`, read
> the work file back, and continue. Then update this RESUME block.
>
> **Git convention for this work: COMMIT freely, but do NOT push.** Commit each completed step
> so nothing is lost across `/compact` and session boundaries — commits are the durable handover.
> Pushing is left to the user: leave the branch ahead of origin and ask before `git push`.
> **Default to NEW commits; do not amend unless the user explicitly asks** (amending = stopping
> to ask; a new commit keeps moving). Never amend/force-push a pushed commit without asking.
> **Keep junk out of commits:** stage only the deliverable proof file(s). Do NOT commit
> `_backups/`, `_tmp/`, checkpoints (`*.dmtcp`, `*.ckpt`), `cfg.*`, `hol-light-autoproof/`,
> `work.ml`, or `.pre_*`/`.bak*` scratch — a prior run accumulated ~300 MB of that and it had to
> be squashed back out.

---

## Readable-spec architecture (the two-layer pattern — USE THIS FOR EVERY BAND)

This is the single most important convention for new bands, settled 2026-06-29 and matching
Mila's open AES-256-GCM-encrypt PR (**awslabs/s2n-bignum #417**, her `_CONCRETE` / `_ABS` split).
le3block was first proved with an unreadable goal built by OCaml term-surgery
(`build_le3_body_goal()` patched `concl LE2BLOCK`); it was rewritten to this pattern. Do NOT
reintroduce goal-builders — write each band's Hoare triple out **explicitly in source**.

Each band gets **two theorems**, both with their `ensures arm {...}` statement written out longhand:

1. **`AESV8_GCM_8X_DEC_256_LE<N>BLOCK_BODY`** — the **literal per-block triple**, the ARM-simulation
   target. Input = the per-block ciphertext reads `read (bytes128 (in_p+16k)) s = cphk`; output =
   the per-block plaintext stores (`word_xor cphk keystream`, last block masked-blended with
   `outprev`) + the literal GHASH tag in `xi_p`. Concrete int128 lanes — this is what `ARM_STEPS`
   likes. Proved by the full symbolic simulation.

2. **`AESV8_GCM_8X_DEC_256_LE<N>BLOCK`** — the **readable public theorem** with `byte_list_at` for
   BOTH the input ciphertext buffer (`byte_list_at x in_p (word (16*N')) s`, N' = nfull+1) and the
   output plaintext buffer (`byte_list_at (aes_ctr_full_tail_bytes ...) out_p (word len) s`) + the
   GHASH tag. Derived **sim-free** from BODY.

   - **DO NOT inline `byte_list_at` into the simulation goal.** Carrying
     `byte_list_at`/`num_of_bytelist`/`SUB_LIST` terms through every ARM step reintroduces the
     lane/term bloat (Q8/Q16 blow-ups) the codebase fought off. Keep the sim on concrete lanes;
     confine all list↔word reasoning to the two reusable, ARM-free bridge lemmas, applied once.
   - **Input bridge** (byte_list_at → per-block lane reads): `INPUT_BRIDGE_3` (and the general
     `INPUT_BYTES_TO_BYTE128_LANES` / `INPUT_BYTES_FULL`, induction on N via the XTS
     `READ_BYTES_AND_BYTE128_MERGE`). For nfull=N use the N=nfull+1 lanes.
   - **Output bridge** (per-block stores → byte_list_at): `BYTE_LIST_AT_NBLOCK_CTR` (in
     `arm/proofs/utils/aes_ctr_spec.ml`, nfull-generic) + `AES_CTR_<N>_EL`.
   - **Wiring:** `MATCH_MP_TAC ENSURES_PRECONDITION_THM` (input) then, on the residual,
     `MATCH_MP_TAC ENSURES_POSTCONDITION_THM` (output), then `MATCH_MP_TAC ..._BODY`.
   - **GOTCHA (cost a few iterations):** `ENSURES_PRECONDITION_THM`'s `EXISTS_TAC` witness is the
     BODY **pre** P; `ENSURES_POSTCONDITION_THM`'s witness is the BODY **post** Q. Don't reuse one
     for both. Extract them from the SPECL-instantiated BODY: pre = `rand(rator(rator(rand(concl …))))`,
     post = `rand(rator(rand(concl …)))`.

Verifying transcription cheaply: the explicit BODY goal term must equal the old surgery output —
once true, the existing simulation tactic proves it verbatim, so you can validate the written-out
statement with `concl X = concl Y` (instant) before paying the ~780s sim.

XTS / Mila references for the presentation: AES-XTS `CIPHER_STEALING_CORRECT`
(`byte_list_at ct ct_ptr len` in, `byte_list_at (aes256_xts_decrypt ...) pt_ptr len` out); Mila
#417 `AES256_GCM_ENCRYPT_CORRECT` (the `_ABS` band, `byte_list_at pt_in in_ptr (word 128)` in).
The `byte_list_at` predicate + substrate (`bytes_to_int128`, `num_of_bytelist`,
`READ_BYTES_AND_BYTE128_MERGE`) live in `arm/proofs/utils/aes_xts_common.ml`, already shared and
loaded by the dec chain.

---

## 0. Where we are (DONE — committed, loadt-clean, axioms()=3, no cheats)

`common/gmult_nblock_lemmas.ml`: the shared fast `build_GMULTn_fast n` builder + `WORD_XOR_ACI`.
Every band's `GMULTn_FULL_CORRECT_BA` is built from this (GMULT2 in 2block, GMULT3 in le3block,
GMULT4 in le4block) — ~0.3s each, reproduces the old hand-written concl exactly.

`arm/proofs/aesv8_gcm_8x_dec_256_1block.ml`:
- `AESV8_GCM_8X_DEC_256_LE1BLOCK` — `bit_len = 8·bl`, `1 ≤ bl ≤ 16` (nfull=0, masked tail; enters
  the body at `pc+0x18`, C_ARGUMENTS, XTS-style prologue reorder). bl=16 endpoint = whole-1-block.
- Carries the reusable GHASH machinery: `GMULT_FULL_CORRECT_BA`, `GMULT_REDUCE_PROP3`,
  `PMUL_KARATSUBA`, `KARATSUBA_LIMBS`, EXEC rule, length/flag lemmas (INSERT2_JOIN, MASK_LEMMA,
  BLEND_OR_XOR, …).
- **whole-1-block `AESV8_GCM_8X_DEC_256_1BLOCK` REMOVED** (covered by LE1BLOCK bl=16, referenced
  nowhere, LE1BLOCK re-sims independently).

`arm/proofs/aesv8_gcm_8x_dec_256_2block.ml`: **SHARED bridge infrastructure only** — GMULT2 (via the
builder) + MERGE/mask/lane tactics (JOIN_EQ_SPLIT, RF8_SUBWORD, SUBW_* lemmas, MERGE_2BLK_TAC,
mk_discard2, MASK_COLLAPSE_CPH1_TAC, FINISH_2BLK_TAC, DEC_2BLK_GMULT2_BRIDGE_TAC, LANE_CLOSE_TAC),
used by le2/le3/le4. **whole-2-block `2BLOCK` + `2BLOCK_BYTELIST` REMOVED** (covered by LE2BLOCK bl1=16).

`arm/proofs/aesv8_gcm_8x_dec_256_le2block.ml`: `AESV8_GCM_8X_DEC_256_LE2BLOCK` (nfull=1, 17–31
bytes) + `_BYTELIST`, and the proven `DEC_LE2BLOCK_DISPATCH` (≤2-block dispatch, 1..32 bytes,
`ASM_CASES` on `val len ≤ 16` to LE1BLOCK_BYTELIST / LE2BLOCK_BYTELIST).

`arm/proofs/aesv8_gcm_8x_dec_256_le3block.ml`: **`AESV8_GCM_8X_DEC_256_LE3BLOCK`** (nfull=2, 33–47
bytes) in the readable two-layer form (BODY + readable byte_list_at), `GMULT3_FULL_CORRECT_BA` (via
builder) + input bridges.

`arm/proofs/aesv8_gcm_8x_dec_256_le4block.ml`: **`AESV8_GCM_8X_DEC_256_LE4BLOCK`** (nfull=3, 49–64
bytes, incl whole-4-block at bl1=16) in the readable two-layer form (BODY + readable byte_list_at),
`GMULT4_FULL_CORRECT_BA` (via builder) + the 4-term bridge close.

**Decrypt is leading-edge:** Mila's `aes256_gcm_tail` (PR #417) has **no GCM decrypt** — there is
nothing to converge against on the dec side, so we are not blocked on her. We *do* reuse her GHASH
layer and the XOR-AC `bubble_fix` canonicaliser (see below).

---

## The mirror principle (how every band works)

Each decrypt band is the encrypt band with: (1) `pt → cph` in the spec/abbreviations, (2) the
out_p store materialized as plaintext = `word_xor cph (aes256_encrypt ctr keys)` (enc stores the
ciphertext — the symmetric mirror), (3) the GHASH data block = `brev cph` (masked tail:
`brev (word_and cph MK)`, `MK = word(2 EXP (8*bl1) - 1)`), (4) the dec GHASH bridge taken **after**
the final closing `eor v19,v19,v18` (dec splits enc's `eor3` into two `eor`s; see "what didn't
work"), (5) dec entry/exit PCs (dec routine is **4612 bytes**; `nonoverlapping (word pc, 4612)` —
NOT enc's 4600). Everything else — front CTR/AES sim, cascade control flow, mask collapse,
reduction lane-blast — is the same tactic block.

Encrypt files to mirror: `aesv8_gcm_8x_enc_256_2block.ml`, `aesv8_gcm_8x_enc_256_le2block.ml`
(helper resolvers `USHR_128_8BL_LEMMA`, `X5_ZERO_LEMMA2`, `IVAL_WORD_LE32`, `IVAL_WSUB_LE32`).

---

## The tail structure (from objdump of aesv8_gcm_8x_dec_256.o)

The tail is a `b.gt` cascade into separate `more_than_K` entry blocks, each doing K full-block
GHASH rounds then falling into `less_than_1` (the masked tail). Entry PCs:
  `more_than_7 = 0xf98, _6 = 0xfc8, _5 = 0x1000, _4 = 0x103c, _3 = 0x1074, _2 = 0x10b8, _1 = 0x10f4`.
b.gt cascade (`x5 = word(16*nfull + bl1)` for the band):
  `edc #112→f98, f0c #96→fc8, f2c #80→1000, f48 #64→103c, f60 #48→1074, f78 #32→10b8, f88 #16→10f4`.
So a band's nfull = number of FULL blocks; LE1BLOCK = nfull 0, LE2BLOCK = nfull 1, LE3BLOCK = nfull 2.
H-powers: `more_than_K` reads H^(K+1) at `[x6,#16(K+1)]` down to H; e.g. more_than_2 reads
`q23 = htbl_p+48 = h3` (H^3). The closing reduction (`less_than_1 … eor v19,v19,v18 … rev64 … st1`)
is SHARED across all bands.

**Htable Karatsuba-mid packing (matters from nfull≥2):** the register at `[x6,#16k]` is PACKED —
its low 64 bits is H^k's pmull (.1d) mid key, its high 64 bits is H^(k+1)'s pmull2 (.2d) mid key.
So at nfull=3, `[x6,#64]` (le3block's `h3k`) carries h3's mid in the low half AND **h4's mid in the
high half** (`word_subword h3k (64,64) = h4_lo ⊕ h4_hi`), and `[x6,#80]` = h4. Each new band adds one
H-power read + one high-half mid-key constraint on the previous band's top htable register.

## Whole-block theorems: REMOVED (covered by the LE bands)

The whole-N-block theorems (`AESV8_GCM_8X_DEC_256_1BLOCK`, `2BLOCK`, `2BLOCK_BYTELIST`, exact
128/256 bit_len, non-masked path) have been **removed** (2026-06-30): each LE-N band's bl1=16
endpoint already IS the whole-(N+1)-block case (all-ones mask ⇒ the masked `less_than_1` path
collapses to the full-block forms), they were referenced nowhere outside their own files, and the
LE proofs re-simulate independently (they never used the whole-block theorems via ENSURES_TRANS).
This saved ~450s of redundant ARM-sim and makes the chain uniform (only band theorems remain).

The lower band **files** stay — they are the **definition sites** for the shared
`AESV8_GCM_8X_DEC_256_EXEC` machine-code rule, the GHASH/Karatsuba machinery
(`GMULT_FULL_CORRECT_BA`, `GMULT_REDUCE_PROP3`, length/flag lemmas in 1block; the MERGE/mask/lane
bridge tactics + `GMULT2_FULL_CORRECT_BA` in 2block), and the chain `le4→le3→le2→2block→1block` is
load-bearing. The GMULTn lemmas now all come from `common/gmult_nblock_lemmas.ml`.

---

## Steps (checklist — work top to bottom)

### [x] Step 0 — shared `common/gmult_nblock_lemmas.ml` + remove redundant whole-block thms — DONE
- `build_GMULTn_fast n` is the single GMULTn source for 2block/le3block/le4block. Whole-1-block and
  whole-2-block theorems removed (covered by LE1/LE2 at bl=16). le3 LAYER 2 PRE switched to
  `BYTE_LIST_AT_3BLOCKS`. Whole chain cold-load-clean.
### [x] Step 1 — `AESV8_GCM_8X_DEC_256_2BLOCK` (two whole blocks) — DONE, then REMOVED (≡ LE2BLOCK bl1=16)
### [x] Step 2 — `AESV8_GCM_8X_DEC_256_LE2BLOCK` (17–31 bytes: 1 full + 1 masked) — DONE (+ `_BYTELIST`)
### [x] Step 2.5 — `DEC_LE2BLOCK_DISPATCH` (≤2-block dispatch, 1..32 bytes) — DONE
- ONE public theorem, generic byte_list_at postcond, `ASM_CASES_TAC` on `val len ≤ 16` →
  LE1BLOCK_BYTELIST (nfull=0) / LE2BLOCK_BYTELIST (nfull=1). Footprints reconciled to the 32-byte
  precondition (LE16 nonoverlap-shrink). Model: Mila's `AES256_GCM_ENCRYPT_CORRECT` cascade.
### [x] Step 3 — `AESV8_GCM_8X_DEC_256_LE3BLOCK` (33–47 bytes: 2 full + 1 masked, nfull=2) — DONE
- Readable two-layer form (see "Readable-spec architecture"). The ONE new piece vs LE2BLOCK was the
  3-term GHASH bridge `GMULT3_FULL_CORRECT_BA` (see below). Front/cascade/stores mirror LE2BLOCK with
  `byte_len = 256 + 8*bl1`, `x5 = word(32+bl1)`, bound `32+bl1 ≤ 48`.
### [ ] Step 4 — ≤3-block DISPATCH (extend Step 2.5 with a third branch) — cheap, no sim
- Add a `val len ≤ 48` branch dispatching to `LE3BLOCK` (now byte_list_at-native). Reconcile to the
  48-byte footprint. Same `ASM_CASES` cascade shape.
### [x] Step 5a — `AESV8_GCM_8X_DEC_256_LE4BLOCK` (49–64 bytes: 3 full + 1 masked, nfull=3) — DONE
- Readable two-layer form, committed to `arm/proofs/aesv8_gcm_8x_dec_256_le4block.ml`,
  cold-load-clean, hyps=0, axioms=3. The two hard parts (opaque-Q7 masked keystream; collapse to
  cphm before the rev64) and the 4-term bridge are documented in the file header + RESUME block.
### [ ] Step 5b — nfull=4..6 bands (LE5BLOCK … LE7BLOCK) — NEXT
- Each = LE(N-1) + one extra full GHASH round (`more_than_K` at the next cascade entry), one extra
  H-power read + high-half mid-key constraint, `GMULT(N)_FULL_CORRECT_BA = build_GMULTn_fast N`,
  `spec_to_byteform_N`, and the same front(keep the right keystream)/stores/masked-tail/bridge
  templates with shifted state numbers. `byte_len = 16*nfull + bl1`, `x5 = word(16*nfull+bl1)`,
  the `#16*(nfull+1)` b.gt now TAKEN. The 4612-byte routine has `more_than_7` so LE5..LE8 all fit.
### [ ] Step 6 — whole-function `AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT`
- Wrap the dec body core (pc+0x18) with `ARM_ADD_RETURN_STACK_TAC` (XTS pattern,
  `AES_XTS_ENCRYPT_SUBROUTINE_CORRECT`; callee `[D8;…;D15]`, 80-byte frame). Shared with encrypt;
  coordinate the prologue-reorder/stack posture with Mila (`_docs/message-to-mila.md`).
### [ ] Step 7 — scale to the main loop (`Loop_mod2x`) + 8-block bulk
- Mirror enc once it lands. GHASH via Mila's general-N layer.

---

## The 3-term GHASH bridge (GMULT3) — the per-band "one new piece"

`more_than_K` accumulates K+1 Karatsuba products (block0·H^(K+1), …, masked·H) into Q17/18/19, then
ONE Prop3 reduction. `GMULT<N>_FULL_CORRECT_BA` = the N-block fused multiply+reduce, built the same
way every band (GMULT3 is the worked instance, in the le3block file):
- `dec<N>_tL` = XOR of N pmul-Karatsuba packs;
- `PACK<N>_ID` folds them into the packed product. **Build it the FAST way (~0.3s), NOT the old
  monolithic `CONV_TAC WORD_RULE` (~373s for N=3; N=4 never finished — WORD_RULE bit-blasts).**
  Fast = `decN_tL = XOR_k dec1[k]` via `REWRITE[WORD_ZX_XOR;WORD_SHL_XOR]` then `AC WORD_XOR_ACI`
  (structural XOR-AC over opaque pmul atoms, no bit-blast), then rewrite each `dec1[k]` by a
  per-block PACK1 (`PMUL_KARATSUBA`, 0.02s). The reusable `build_GMULTn_fast n` now lives in the
  shared `common/gmult_nblock_lemmas.ml` (verified to reproduce `GMULT2`/`GMULT3` concl exactly);
  every band does `let PACKn_ID, GMULTn_FULL_CORRECT_BA = build_GMULTn_fast n`.
- `SPEC dec<N>_tL (… GMULT_REDUCE_PROP3)` then `TRANS + AP_TERM polyval_reduce_prop3 PACK<N>_ID`.
- **NOTE the packed RHS must be LEFT-associated** (`(p0⊕p1)⊕p2…`) to match `GHASH_POLYVAL_ACC_<N>`'s
  output, and the H-power byteswap preconds for N≥4 must be **left-nested** `polyval_dot` (e.g.
  `byteswap128 h4 = polyval_dot(polyval_dot(polyval_dot(bsw h)(bsw h))(bsw h))(bsw h)`) — that's
  what ACC_4 produces. le3block's H^3 precond is right-nested and matched ACC_3, but ACC_4 forces
  left-nested; re-state the H^3 precond left-nested for le4block (or bridge it).
Spec side: `GHASH_POLYVAL_ACC_<N>` (already in `common/ghash_nblock_karatsuba.ml`) + the H-power
byteswap preconds (e.g. `byteswap128 h3 = polyval_dot (bsw h) (polyval_dot (bsw h) (bsw h))`).

Bridge-close tactic (the `BRIDGE_CLOSE_TAC` in the le3block file): fold spec → GMULT<N> byteform;
`ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC` (MERGE only UNIFIES the LHS/RHS qq names — it does NOT
split `cross`); fold the residual middle-block mids to `qq8`-style atoms (`PMUL_CONG_128`); unify the
two W-rounds (`wa` by `PMUL_CONG_128`+`WORD_RULE`; `wv` by a ~1.8s `BITBLAST_RULE` input-equality
lifted with `AP_THM(AP_TERM word_pmul in_eq) W`); `ABBREV` both W-pmuls opaque; `QQ0SPLIT` +
`JOIN_EQ_SPLIT`; each 64-bit lane closes by `WORD_SIMPLE_SUBWORD_CONV` + `SJ_COLLAPSE`/`SJ_COLLAPSE2`
+ **`bubble_fix`** (XOR-AC canonicaliser, ported from Mila's `gcm_aesgcm_nblock_helpers.ml`) + `REFL`.

---

## What WORKED (durable, reusable)

- **`bubble_fix`** (XOR-AC multiset canonicaliser from Mila) is what closes the per-lane identity
  where `WORD_RULE` diverges and `WORD_BLAST` blows up — but ONLY once the bridge goal is actually
  true (right state). It's flat in term count, so it scales to more qq atoms unchanged.
- **The opaque-W abbreviation**: after unifying the two W-rounds, `ABBREV` both W-pmuls so the lane
  close is pure subword normalization + XOR-AC, not GF reasoning.
- **Discard discipline**: scrub the old huge register-Q19 assumption after the bridge and
  `DISCARD_OLDSTATE` before any `RULE_ASSUM` scrub, else a 40 MB term / `tryfind` blowup. In the
  front, `mk_discard2` keep-lists must keep the block keystreams (LE3BLOCK keeps Q0,Q1,Q2).
- **Re-assert the masked tail store value BEFORE the `st1`** and carry it through discards;
  `MASK_LEMMA`/`BLEND_OR_XOR` give the masked-blend = `word_xor (word_and ct MK) (word_and outprev (~MK))`.

## What did NOT work (dead ends — do not retry)

- **Term-surgery goal builders** (`build_le3_body_goal`): make the spec invisible in source. Banned —
  write the triple explicitly (see "Readable-spec architecture").
- **Inlining `byte_list_at` into the simulation goal**: reintroduces lane/term bloat. Use the two-layer
  split.
- **Taking the bridge one state too early** (le3block: s380 vs the correct **s381**, after
  `eor v19,v19,v18`): Q19 there is the INCOMPLETE reduced value (missing the high-reduction term), so
  the bridge goal is subtly FALSE → every close diverges. This off-by-one (the dec "s350 vs s351" /
  2block "s370" pitfall) was the real root cause of ~8 failed le3block attempts — NOT any GF-algebra
  wall, "u=0" residual, or lane unsoundness (all artifacts of the false goal).
- **The r1/u/r2 hand-staged W-reduction ladder** (`PMUL_W_64_128` expand + manual shift-triple folds):
  works for 1/2 blocks but at ≥3 blocks the per-lane residual is a genuine GF relation over abstract
  qq products that `WORD_RULE` can't and `WORD_BLAST` diverges on. Use `GMULT_REDUCE_PROP3` over the
  combined product + `bubble_fix` instead.
- **Per-lane `WORD_RULE`/`WORD_BLAST`/`LANE_CLOSE_TAC` on opaque qq**: the lane is false for opaque qq
  (true only via the carryless-product structure). `bubble_fix` is the tool, once the goal is true.

## Architecture vs Mila (corrected hindsight)

- Mila proves the GF reduction **once inductively** (`GHASH_NBLOCK_KARATSUBA_EQ_PROP3`,
  `common/ghash_nblock_karatsuba.ml`), then each band just instantiates it (~0.05–0.10s, flat in N).
  Our dec close is more bespoke: `GMULT_REDUCE_PROP3` over the combined product, matched to the
  register by `MERGE_2BLK` + wa/wv unification + per-lane `bubble_fix` (a few minutes/band). **Mila's
  is the cleaner, more scalable architecture**; ours is what was already proven for dec 1/2-block and
  extended. For nfull=3..7 strongly consider adopting her inductive layer for the close.
- What we genuinely borrowed: (a) `bubble_fix`; (b) the `common/ghash_nblock_karatsuba.ml` layer
  (`GHASH_POLYVAL_ACC_N`, the Karatsuba substrate); (c) the XTS byte-list substrate (`byte_list_at`,
  `READ_BYTES_AND_BYTE128_MERGE`, `bytes_to_int128`, `num_of_bytelist`) for both byte_list_at bridges;
  (d) the two-layer `_CONCRETE`/`_ABS` presentation (PR #417) — our BODY / readable theorem.

---

## Scaling to nfull=3..7

No fundamental obstacle. The dec tail bands are structurally identical per block (objdump: each
`more_than_K` = one full-block GHASH round vs H^(K+1); the closing reduction is shared). LE4BLOCK
(nfull=3, 49–63 bytes) = LE3BLOCK + one more full round:
- front/cascade: `#48` b.gt now TAKEN → more_than_3 (0x1074); `byte_len = 384 + 8*bl1`,
  `x5 = word(48+bl1)`, bound `48+bl1 ≤ 64` (USHR_384 / X5_ZERO_LEMMA4 / IVAL_*_LE64, same proofs);
- stores: pt0..pt2 full + pt3 masked; pt3 counter = `gcm_ctr_inc^3 ctr0` (`GCM_CTR_INC3_LANES`,
  analog of `_INC2`);
- BODY: written out explicitly with one more in/out block read/store + the H^4 precond/read
  (h4 at htbl_p+? , `byteswap128 h4 = polyval_dot (bsw h) (…h^3)`);
- bridge AT `s(381 + round_len)` = AFTER the `eor v19,v19,v18` (the SAME off-by-one fix);
- `GMULT4_FULL_CORRECT_BA` built exactly like GMULT3 (`dec4_tL` = XOR of 4 packs, `PACK4_ID`,
  `GMULT_REDUCE_PROP3`); `GHASH_POLYVAL_ACC_4` already exists; `BRIDGE_CLOSE_TAC` shape unchanged
  (more qq atoms; `bubble_fix` flat);
- readable LE4BLOCK: input bridge at N=4 lanes (`INPUT_BYTES_FULL`), output `BYTE_LIST_AT_NBLOCK_CTR`
  at nfull=3 + `AES_CTR_4_EL`.

Cost driver per band: `PACK_N_ID` (~373s one-time WORD_RULE) + ~1 GHASH-round sim span + the bridge
close. **Recommended for nfull=3..7: a `GMULTn` builder** (parameterize `dec_N_tL` over the block
list) **+ a band-generic driver** (parameterize the front-cascade resolvers + store count + the
bridge state `s(381 + round_len*(nfull-2))` over nfull) to avoid 5 near-copies — OR adopt Mila's
inductive close layer outright.

---

## Reproduce / verify (any band)
```
# in HOL MCP, cwd = PROJECT ROOT (so define_assert_from_elf finds arm/aes-gcm/*.o),
# base.ml preloaded:
loadt "arm/proofs/aesv8_gcm_8x_dec_256_<file>.ml";;
# check: no CHEAT_TAC/new_axiom in the file; `axioms();;` shows only the 3 core HOL axioms;
# the band theorems have hyps=0.
```
Each band file `needs` the one below it, so a band loadt includes that cost (the full le3block
chain is ~2900s cold; the le3block file alone on top of cached le2block ~1150s — PACK3_ID + the
~780s BODY sim; the readable LAYER-2 theorem is sim-free ~0.2s). Run `Gc.compact ();;` after heavy
sims. NOTE: a stale checkpoint may list these files as "already loaded" without their bindings
actually present — if `needs` skips a file you need, clear it from `loaded_files` and reload.

## Cross-references
- Readable-spec / two-layer convention: this doc's "Readable-spec architecture" section.
- Dec 1-block methodology (hard-won tactics): `_docs/aesv8-gcm-8x-dec-256-1block-methodology-20260611.md`.
- GMULT2 recipe + "scales to N blocks": `_docs/gmult2-fused-reduce-lemma.md`.
- GHASH layer + D7 timing (Mila vs ours): `_docs/gcm-spec-divergence-from-mila-handback.md`; spike `_spike/`.
- Mila's encrypt PR (the `_CONCRETE`/`_ABS` model, byte_list_at presentation): awslabs/s2n-bignum **#417**.
- Encrypt n-block plan (parent): `_docs/aesv8-gcm-nblock-generalization-plan-20260617.md`.
- Shared bridges: `arm/proofs/utils/aes_ctr_spec.ml` (`aes_ctr_full_tail_bytes`,
  `BYTE_LIST_AT_NBLOCK_CTR`), `arm/proofs/utils/aes_xts_common.ml` (`byte_list_at` substrate).
- Superseded: `_docs/dec-tail-more-bands-handoff.md` (folded into this doc), `_docs/le3block_NOTES.md`
  (its lessons folded in here).
