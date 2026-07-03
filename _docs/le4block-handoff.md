# LE4BLOCK (AES-GCM-256 decrypt, nfull=3, 49–64 byte band) — session handoff

**Status (2026-06-30): NOT proven.** The algebra + the full-block forward simulation are done and
validated; the **masked-block (pt3) store** and the **4-term GHASH bridge** remain. This doc is a
self-contained pickup point for a fresh session.

**Band:** bit_len = 384 + 8·bl1, 1 ≤ bl1 ≤ 16. THREE full ciphertext blocks 0,1,2 + one MASKED
partial tail block 3 (mask `MK = word(2 EXP (8·bl1) − 1)`). nfull = 3.

**Design answer (settled, from objdump — strict `b.gt` cascade):** an LE-N band covers bytes
[16·nfull+1, 16·(nfull+1)] **inclusive**; the bl1=16 endpoint = whole-(N+1)-block (all-ones mask =
full block). So **LE4BLOCK INCLUDES the whole-4-block (64-byte) case**; whole-3-block is already in
LE3BLOCK. No separate whole-block theorems are needed for any band.

---

## Working files

- **`_docs/le4block_WIP.ml`** — the canonical WIP script. **loadt-clean (~2s on top of a loaded
  le3block), axioms()=3, no cheats.** Contains ALL of the proven algebra + the validated front/stores
  tactics + the goal builder. `needs "arm/proofs/aesv8_gcm_8x_dec_256_le3block.ml"`.
  (Identical to the session's `work.ml` at handoff; backups `_docs/work.le4block.bck0001..0014.ml`.)
- **`memory/project_le4block_wip.md`** — the running root-cause log (most detail; read the TOP
  entries first, they supersede earlier ones).
- This doc — the curated summary.

Resume: load le3block (heavy, see "Timing"), then `loadt "_docs/le4block_WIP.ml";;`, then
`set_goal([], build_le4_body_goal());; e(full_le4_tac_front THEN full_le4_tac_stores);;` lands you
at **s350** with pt0/pt1/pt2 captured, ready for the masked tail.

---

## DONE — proven & verified (in le4block_WIP.ml)

1. **Fast GMULTn builder** (`build_GMULTn_fast n`) — the optimization + back-port deliverable.
   Builds `PACK<N>_ID` + `GMULT<N>_FULL_CORRECT_BA` in **~0.3s** vs the old hand-written ~373s
   monolithic `CONV_TAC WORD_RULE` (which bit-blasts and never finished for N=4). Method:
   `decN_tL = XOR_k dec1[k]` via `REWRITE[WORD_ZX_XOR;WORD_SHL_XOR]` then `AC WORD_XOR_ACI`
   (structural, opaque pmul atoms, NO bit-blast), then per-block PACK1 (`PMUL_KARATSUBA`, 0.02s).
   Verified to reproduce `GMULT3_FULL_CORRECT_BA` exactly. **`GMULT4_FULL_CORRECT_BA` is built.**
   NOTE: left-assoc packed RHS (`mk_packed_L`) is required to match `GHASH_POLYVAL_ACC_N`.
2. **`spec_to_byteform_4`** — GHASH_POLYVAL_ACC_4 → GMULT4 byteform. REQUIRES the h2/h3/h4 byteswap
   preconds in **LEFT-NESTED** `polyval_dot` form (h4 = pd(pd(pd(bsw h)(bsw h))(bsw h))(bsw h)).
   (le3's h3 was right-nested; ACC_4 forces left-nested — the BODY goal hyps use left-nested.)
3. **Cascade/counter helpers** (all proven): `USHR_384_8BL_LEMMA`, `X5_ZERO_LEMMA4`,
   `IVAL_WORD_LE64`, `IVAL_WSUB_LE64`, `X1_MOD128_BRIDGE4`, `GCM_CTR_INC3_LANES`, `AES_CTR_4_EL`.
4. **`build_le4_body_goal ()`** — the explicit BODY goal (type-checks; 37 vars; cph3/h4/h3k-hi added,
   byte_len 384, buffers 64, outprev at out_p+48, h-power preconds left-nested). This is the
   _CONCRETE/_BODY goal; the final band file writes it out explicitly (no surgery), per the
   readable two-layer convention (see `_docs/decrypt-nblock-plan.md`).
5. **`full_le4_tac_front`** — VALIDATED: drives the real ARM sim through prologue + AES bulk +
   the full `b.gt` cascade to **s303 = more_than_3 (pc+4212, 0x1074)**. Resolvers:
   #112/96/80 fall (dec_bl4_resolve 270/282/290), #64 boundary (bl4_resolve_pc_bdy 297), #48 TAKEN
   (bl4_resolve_pc48_taken 303 4212).
6. **`full_le4_tac_stores`** — VALIDATED: from s303, captures the 3 FULL plaintext stores cleanly
   to **s350**: pt0 (out_p, auto-folds at s312), pt1 (out_p+16, s327), pt2 (out_p+32, s350).
   Per-block capture: `FIRST_X_ASSUM(MP_TAC o SPEC <word_xor cphK (aes256_encrypt (gcm_ctr_inc^K
   ctr0) keys)> o Q12-trick)` with ANTS `GCM_CTR_INC{,2}_LANES + ONCE WORD_XOR_ASSOC + aes256_encrypt
   expand + WORD_XOR_ASSOC + WORD_BLAST` (the eor3 = word_xor(word_xor cphK KS)k14, hence the
   WORD_XOR_ASSOC before+after), then ABBREV ptK, then the store readback auto-folds.

`full_le4_tac_front THEN full_le4_tac_stores` runs as ONE tactic (~405s) reaching s350.

---

## NOT DONE — the remaining work

### A. The masked-block (pt3) store — BLOCKED, root cause known

The masked block is block 3: eor3 `v12,v9,v7,v29` at 0x1120 (≈s347) computes the UNMASKED pt3 into
Q12; the mask is built (`and v9,v9,v0`, ~s368); the **bif** `v12,v26,v0` at **0x117c (s370)** blends
pt3 with `outprev`; the masked plaintext is stored to out_p+48 by `st1` at **0x11b8**.

`read Q12 s369 = word_xor (word_xor cph3 (read Q7 s346)) k14` — i.e. pt3 in keystream form, but the
keystream is `read Q7 s346` which is **OPAQUE** (no defining equation). Hence capturing
`read Q12 s369 = pt3` (= `word_xor cph3 (aes256_encrypt (gcm_ctr_inc^3 ctr0) keys)`) fails: WORD_BLAST
can't fold the opaque `read Q7 s346`.

**Why opaque:** v7's keystream is routed through the tail-prologue SHIFT-REGISTER (per cascade
fall-through level: `mov v7,v6; v6,v5; v5,v4; v4,v3; v3,v_in` at 0xee0–0xf80). After the 4
fall-throughs for the more_than_3 path, v7 holds block-3's keystream — but it arrived via `mov`s the
simulator does NOT fold into a `read`-equation, and the AES-bulk `mk_discard2` dropped the source
keystream readbacks.

**Confirmed via experiments (all in the log):**
- RESOLVE_SIMD over the masked eor3 region (335–347): read Q12 s347 STILL opaqueQ7=true.
  (RESOLVE_SIMD DID inline the bif's *mask* operand at s370, but not the Q12 s369 keystream.)
- Keeping Q7 in the front bulk discards ([3;4;5;6;7]→[3;4;5;6] and →[3;4]): Q5/Q6 survive as aese
  equations at s303, **Q7 does not** (Q7 is only WRITTEN by the mov, never READ at s303, so no
  `read Q7 s303` equation is created).
- `read Q1 s303 = aese(ctr+1)` survives; the mov chain v7←v6←…←v1 means v7's value derives from it,
  but the chain isn't materialized.

**CORRECTNESS (verified, so the eventual proof is sound):** v5 s309 = ctr+1, v6 s309 = ctr+2 (read
off live), pt0 = ctr+0; so by the pattern v7 = ctr+3 = `aes256_encrypt (gcm_ctr_inc^3 ctr0)`. The
BODY postcond's pt3 form is therefore correct — the blocker is purely *availability*, not soundness.
(Still: a continuation should re-confirm v7's counter once the keystream is materialized, before
trusting the capture.)

**FIX TO TRY (next session), in priority order:**
1. **Resolve the mov-chain:** interleave `ARM_VSTEPS_RESOLVE_SIMD_TAC` on the cascade `mov` steps
   (the v7←v6←…←v1 shift at ~s310, region 0xee0–0xf80) so the sim materializes `read Q7 = read Q1`
   (or the surviving aese form), while keeping Q1 (don't discard it). Then `read Q7 s346` folds and
   the masked store closes via le3's exact masked-store tactic:
   `SPEC word_xor(word_and pt3 MK)(word_and outprev ~MK)` + ANTS `EXPAND pt3 + GCM_CTR_INC3_LANES +
   aes256_encrypt expand + INSERT2_JOIN + MASK_LEMMA + BLEND_OR_XOR + WORD_BLAST`.
2. **Or capture the keystream right after it's written:** after the AES bulk (before any discard),
   assert `read Q<n> = aes256_encrypt(gcm_ctr_inc^3 ctr0) keys` for the register that becomes v7,
   and carry it. Requires identifying that register (the shift-register net result for the
   more_than_3 path — trace the 4 fall-through shifts).
3. The Q9 masked-input collapse already works: `SPEC word_and cph3 MK o Q9-trick` + `INSERT2_JOIN`
   + `ASM_SIMP[MASK_LEMMA]` + `WORD_RULE` (validated live — Q9 s368 collapses to word_and cph3 MK).
   And the bif-mask is already inlined by RESOLVE_SIMD. So ONLY the keystream fold is missing.

Model the masked store + the tail exactly on `full_le3_tac_tail`
(arm/proofs/aesv8_gcm_8x_dec_256_le3block.ml L438-486), shifted by the H^4 round and using
pt3/cph3/GCM_CTR_INC3_LANES/cphm = word_and cph3 MK.

### B. The 4-term GHASH bridge — not started

After the masked store, at the post-`eor v19,v19,v18` state (0x11d4):
`read Q19 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
  [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cphm]`.
Close via `spec_to_byteform_4` (have it) + `GSYM GMULT4_FULL_CORRECT_BA` (have it) + an adapted
`BRIDGE_CLOSE_TAC` (le3block's, L383-406): MERGE_2BLK to share products, fold the THREE middle-block
mids (qq8-style, one per full middle block), unify the two W-rounds (wa by PMUL_CONG_128, wv by a
BITBLAST input-equality), abbreviate both W-pmuls opaque, QQ0SPLIT + JOIN_EQ_SPLIT, per-64-bit-lane
close by WORD_SIMPLE_SUBWORD + SJ_COLLAPSE + **bubble_fix** (XOR-AC). The bridge is the historically
HARD part (le3's 3-term took ~8 attempts to get the s380/s381 off-by-one and the lane close right);
budget a dedicated effort. The shape generalizes (more qq atoms; bubble_fix is flat in term count).

### C. The readable two-layer wrapper — straightforward once BODY is proved

After `AESV8_GCM_8X_DEC_256_LE4BLOCK_BODY` is proved, derive the readable `AESV8_GCM_8X_DEC_256_LE4BLOCK`
(byte_list_at in/out) sim-free, exactly as le3block does: ENSURES_PRECONDITION_THM + `INPUT_BYTES_FULL`
at N=4 (4 lane reads) for the input; ENSURES_POSTCONDITION_THM + `BYTE_LIST_AT_NBLOCK_CTR` at nfull=3
+ `AES_CTR_4_EL` for the output. Witness gotcha: PRE witness = BODY pre, POST witness = BODY post;
apply PRE then POST.

---

## PC / state map (objdump of arm/aes-gcm/aesv8_gcm_8x_dec_256.o; pc = entry − 0x18)

- Cascade `b.gt` (#112→f98 … #48→1074 … #16→10f4); for nfull=3, #48 TAKEN → more_than_3 (0x1074=pc+4212, s303).
- more_than_3 eor3/st order: st pt0 @0x108c, eor3 v5→pt1 @0x1090; st pt1 @0x10d0, eor3 v6→pt2 @0x10d4;
  st pt2 @0x110c, eor3 v7→pt3(masked) @0x1120; less_than_1 @0x1138.
- masked tail: `and v9,v9,v0` ~s368; bif `v12,v26,v0` @0x117c (s370); masked st1 @0x11b8;
  H-round pmulls vs H (v20=[x6,#0]); `eor v19,v19,v18` @0x11d4 (BRIDGE state); ext+rev64 @0x11dc; st1 xi @0x11e0.
- htable: h@+0, hk@+16, h2@+32, h3@+48, h3k@+64 (PACKED: low=h3 mid, **high=h4 mid**), **h4@+80**.
  more_than_3 reads q25=[x6,#80]=h4, q24=[x6,#64] (uses its HIGH half as h4's pmull2 mid key).
- Validated front/store states: s254=pc+1040, s265=pc+3788, s303=pc+4212 (more_than_3),
  s312 (pt0 store), s327 (pt1 store), s350 (pt2 store), s370 (bif).

## Timing / environment

- HOL MCP cwd MUST be the project root (else define_assert_from_elf can't find the .o).
- Loading the le3block dependency is heavy (~2900s cold; the le3block file alone ~1150s on cached
  le2block — PACK3_ID + the ~780s BODY sim). NOTE the stale-checkpoint gotcha: the polyval-aes
  checkpoint may list the gcm dec files as "loaded" without their bindings actually present — if
  `needs` skips a file you need, clear it from `loaded_files` (filter by substring) then loadt.
- Per-step VSTEP in the masked region is slow (GHASH accumulator is multi-MB); each full
  front+stores re-run is ~400s.

## Cross-refs
- `_docs/decrypt-nblock-plan.md` — the tracked plan (readable two-layer convention, GMULTn builder,
  htable packing, band-coverage; Step 5 = LE4 in progress).
- `arm/proofs/aesv8_gcm_8x_dec_256_le3block.ml` — the LE3 template (front/stores/tail/BRIDGE_CLOSE).
- `memory/project_le4block_wip.md` — full running root-cause log (read top entries first).
