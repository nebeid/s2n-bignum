# LE5BLOCK handoff — step map + what's proven (2026-07-01)

**File:** `arm/proofs/aesv8_gcm_8x_dec_256_le5block.ml`. Band: bit_len=512+8*bl1, 1<=bl1<=16,
nfull=4 (4 full blocks 0..3 vs H^5,H^4,H^3,H^2 + masked block 4 vs H). 65–80 bytes; bl1=16 =
whole-5-block. Mirror of le4 with one extra full block + 5-term GHASH bridge.

## PROVEN & in the file (all no-cheat, verified in-session)
- PART 0: `PACK5_ID, GMULT5_FULL_CORRECT_BA = build_GMULTn_fast 5` (instant).
- PART 1: `USHR_512_8BL_LEMMA`, `X5_ZERO_LEMMA5`, `X1_MOD128_BRIDGE5`, `GCM_CTR_INC4_LANES`,
  `AES_CTR_5_EL`, `GHASH_POLYVAL_ACC_5` (also added to common/ghash_nblock_karatsuba.ml),
  `spec_to_byteform_5`.
- Also proved in-session but need adding: `IVAL_WORD_LE80`, `IVAL_WSUB_LE80` (bound 80).
- PART 2 resolvers: `bl5_resolve_pc`, `bl5_resolve_pc_bdy`, `bl5_resolve_pc64_taken`,
  `dec_bl5_resolve_stale = dec_bl4_resolve_stale`, `dec_bl5_resolve`.  NOTE: `bl5_resolve_pc*`
  use IVAL_WORD_LE80/IVAL_WSUB_LE80 — those must be defined BEFORE PART 2 in the file (currently
  proved in-session only; ADD them to PART 1).
- PART 3 `full_le5_tac_front`: VALIDATED interactively end-to-end to s297 = more_than_4 (pc+4156).
- PART 3 `full_le5_tac_stores`: pt0/pt1/pt2 stores + pt1/pt2/pt3 captures VALIDATED to the pt3
  ABBREV (through s336); the `ALL_TAC` at the end is the cut point.

## DISCOVERED STEP MAP (le5, this binary)
- s0..s5 prologue; USHR_512 rewrite; 6..30 CTR/AES per-step (discard [4;5;6;7]);
  31..84, 85..173, 174..177 (GCM_SIMD), 178..184, 185..254 (discard [4;5;6;7;30]).
- s254 = pc+1040, X5=word_add(word_and(word_sub(word(64+bl1))1)...)in_p, Q19=reversefields xi.
- X5_ZERO_LEMMA5; [255] branch (INT_SUB_REFL); 256..265; USHR_512 again + WORD_RULE
  `word_sub(word_add in_p(word(64+bl1)))in_p = word(64+bl1)`; 266..269.
- s269 = pc+3804: Q0..Q3=ks0..ks3, Q12=pt0(block0), Q9=cph0, Q20=h5, Q21=h5k, X5=word(64+bl1).
  ABBREV ks0..ks3, pt0.
- Cascade: (270) dec_bl5_resolve 270 112 3808; (271-282) 96 3856; (283-290) bl5_resolve_pc_bdy 290 80 3888;
  (291-297) bl5_resolve_pc64_taken 297 4156.  s297 = more_than_4.
- STORES: (298-312) -> out_p store pt0 @ s312 (pc+4216); [313] Q12->pt1; (314-320) out_p+16=pt1 @ s320
  (pc+4248); Q12->pt2; (321-336) out_p+32=pt2 @ s336 (pc+4312); Q12->pt3 (block3, ctr+3).
- s344 = pc+4344 (inside more_than_1 region 0x10f4): Q9=cph3, Q12=pt3, X2=out_p+48 (pt3 not yet
  stored), X1=word(512+8*bl1).  pt3 store lands a few steps AFTER s344.
- (337-352) block-3 GHASH vs H^3 + pt3 store: out_p+48 = pt3 @ s352 (pc+4376). VALIDATED. At s352:
  Q9=cph4, Q12=pt3, X0=in_p+80, X2=out_p+64; htable RE-loaded for less_than_1: Q20=h5, Q21=hk,
  Q22=h2, Q23=h3, Q24=h3k, Q25=h4. Q17/Q18/Q19 = 4-block partial GHASH accumulator (H^5..H^2 lanes).
  pt3 store asserted+discarded; pt3 ABBREV in assumptions.
  *** DO NOT capture pt4 at s352 — block-4 plaintext eor3 happens later in less_than_1. ***
- NEXT from s352: mirror le4 full_le4_tac_tail (its ARM_VSTEPS_FOLD (351--357)-equivalent):
  X1_MOD128_BRIDGE5; step masked GHASH; collapse Q9 -> cphm=word_and cph4 MK BEFORE the rev64;
  capture pt4=word_xor cph4 (aes256_encrypt (gcm_ctr_inc^4 ctr0) keys) via GCM_CTR_INC4_LANES at the
  eor3; masked-blend store out_p+64; ABBREV cphm; step to bridge state (shared eor v19,v19,v18 @ pc+4564).
  Store cadence recap: pt0@s312, pt1@s320, pt2@s336, pt3@s352.  full_le5_tac_stores in the file is
  VALIDATED through the pt3 ABBREV (its trailing ALL_TAC is the cut point; replace with pt3 store
  assert+discard which is s352 not s350).

## MASKED-TAIL LANDMARKS (VALIDATED interactively, s352 -> Q9 collapse)
- less_than_1 entry ~pc+4408 (s360).  X1_MOD128_BRIDGE5 applied after pt3 store.
- (353--361) ARM_VSTEPS_RESOLVE_SIMD -> s361 pc+4412.  (362--368) -> s368 pc+4440 (Q9 still cph4).
- (369--375) ARM_VSTEPS_RESOLVE_SIMD -> s375 pc+4468 (the `and v9,v9,v0`, Q9 still cph4 pre-step).
  NOTE: (369--375) can be SLOW (~>60s, MCP may report timeout but it completes; re-query goal_state).
- (376--376) -> s376 pc+4472: Q9 = word_and(word_insert...(mask))cph4.  COLLAPSE Q9 here (NOT s375):
  `FIRST_X_ASSUM(MP_TAC o SPEC \`word_and cph4 (word (2 EXP (8*bl1)-1)):int128\` o MATCH_MP
   (MESON[] \`read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'\`)) THEN REWRITE_TAC[INSERT2_JOIN] THEN
   ANTS_TAC THENL [ASM_SIMP_TAC[MASK_LEMMA] THEN CONV_TAC WORD_RULE; DISCH_TAC]`  -- VALIDATED.
- REMAINING from here: step rev64+masked-GHASH round; capture pt4 (block-4 eor3, Q12) =
  word_xor cph4 (aes256_encrypt (gcm_ctr_inc^4 ctr0) keys) via GCM_CTR_INC4_LANES + MASK_LEMMA +
  BLEND_OR_XOR (le4 lines 338-345 analog); masked-blend store out_p+64 (le4 s385 analog);
  ABBREV cphm = word_and cph4 MK; step to bridge state (shared eor v19,v19,v18 @ pc+4564).
  Bridge state sN: le4 was s392; le5 has +1 full GHASH round earlier in body but same tail => find
  empirically (the state right AFTER pc+4564's eor).  Then BRIDGE_CLOSE_TAC_5 (see below) + post-bridge.

## BLOCK-4 PLAINTEXT + STORE (VALIDATED through s381)
- s377 (pc+4476): Q12 = `word_xor (word_xor cph4 (read Q7 s354)) k14` — block-4 plaintext, where
  `read Q7 s354` is the OPAQUE block-4 keystream (= ctr+4 keystream; the aes256_encrypt (gcm_ctr_inc^4
  ctr0) form).  This is the le4 "opaque-Q7" subtlety (header note 1): the eor3 uses v7 = ctr+3 in le4,
  here v7 = ctr+4.  To capture pt4: SPEC Q12 to
  `word_xor (word_and (pt4) MK) (word_and outprev (word_not MK))` and discharge with EXPAND pt4 +
  aes256_encrypt unfold + MASK_LEMMA + BLEND_OR_XOR + WORD_BLAST, exactly as le4 lines 338-345,
  where pt4 = word_xor cph4 (aes256_encrypt (gcm_ctr_inc(gcm_ctr_inc(gcm_ctr_inc(gcm_ctr_inc ctr0)))) keys).
  NOTE: the aes256_encrypt for the masked block must be shown equal to `word_xor cph4 (read Q7 s354) ...`;
  in le4 this worked because Q7's keystream was proven = the ctr+3 encrypt via the GCM_CTR_INC3_LANES
  rewrite baked into the eor3 ANTS.  For le5 use GCM_CTR_INC4_LANES.  If `read Q7 s354` stays opaque,
  first establish `read Q7 s354 = aes256_encrypt (gcm_ctr_inc^4 ctr0) keys` (it should already be an
  abbreviated/derivable keystream from the front bulk — check the front's Q4->Q7 shift-register movs;
  le4 kept the keystreams and the fall-through shift landed v7=ctr+3, so for le5 v7=ctr+4).

  *** CONFIRMED BLOCKER (this is the one genuinely band-specific hard part): at s377 Q12's masked
  block uses `read Q7 s354` and Q7 is NOT in the assumption list (its keystream definition was
  discarded by the front's `mk_discard2 [4;5;6;7;30]`).  This is EXACTLY le4's opaque-Q7 trap
  (le4 header note 1).  FIX (adapt le4): in full_le5_tac_front, do NOT discard the register that
  ends up as the masked-block keystream — le4 kept Q3 (discarded only [4;5;6;7]) and ABBREVed the
  4 surviving keystreams at s269, then stepped the tail cascade with PLAIN ARM_STEPS (not VSTEPS)
  so the shift-register movs (0xee0..0xf5c) materialize `read Q7 sN = ctr+4 keystream`.  For le5
  the 5-block fall-through shift lands v4=ctr+0..v7=ctr+3? -> re-derive by inspection: with 4 full
  + 1 masked, the masked block is block 4 = ctr+4; trace which Q the shift leaves it in and keep
  that Q (plus abbreviate 5 keystreams ks0..ks4 at s269, not 4).  Then pt4 capture discharges like
  le4.  THIS front-discard adjustment is the main remaining change vs the committed full_le5_tac_front.
- s378-381: Q12 = masked-blend `word_or (word_and (word_xor(word_xor cph4 ..)) MK)(...)`; X2=out_p+64.
  Masked-blend store to out_p+64 lands at pc+4536 (a few steps past s381).  Assert store readback =
  word_xor (word_and pt4 MK)(word_and outprev (word_not MK)); ABBREV cphm = word_and cph4 MK.
- s381 = pc+4492.  Bridge eor v19,v19,v18 @ pc+4564 = ~18 bytes later.

## REMAINING (mirror le4 full_le4_tac_tail + full_le4_tac_bridge)
1. Find pt3 store step (out_p+48 = pt3); assert + DISCARD.  (le4 stored pt2 at s350; le5's block-3
   store is the 4th full store — step just past s344.)
2. MASKED BLOCK 4 (less_than_1 @ 0x1138): X1_MOD128_BRIDGE5; collapse Q9 -> cphm =
   word_and cph4 (word(2 EXP(8*bl1)-1)) BEFORE the rev64 that feeds the masked round (le4: s368,
   before rev64 @ s371 — find le5 analog); masked-blend store out_p+64 = word_xor(word_and pt4 MK)
   (word_and outprev (word_not MK)); ABBREV cphm.  pt4 = word_xor cph4 (aes256_encrypt (ctr+4) keys)
   via GCM_CTR_INC4_LANES.
3. 5-TERM BRIDGE: bridge state = the shared `eor v19,v19,v18` @ pc+4564 (0x11d4).  Assert
   read Q19 (sBRIDGE) = ghash_polyval_acc (bsw h)(brev xi)[brev cph0;..;brev cph3; brev cphm].
   BRIDGE_CLOSE_TAC_5: copy le4's BRIDGE_CLOSE_TAC_4 but with GMULT5_FULL_CORRECT_BA (8-arg SPECL:
   word_xor(brev xi)(brev cph0), bsw h5, brev cph1, bsw h4, brev cph2, bsw h3, brev cph3, bsw h2,
   brev cphm, bsw h) and spec_to_byteform_5; THREE FOLD_MID_TAC middles (cph1.h4, cph2.h3, cph3.h2)
   — need fresh qq names (find via goal_state after ABBREV_INNER_PMULS_TAC; le4 used qq12/qq13).
4. POST-BRIDGE: rev64 + st1 xi_p; ENSURES_FINAL_STATE; MONOTONE_MAYCHANGE.  Exit pc+4580 (shared tail).
5. BODY statement is already set as the interactive goal (matches the intended
   AESV8_GCM_8X_DEC_256_LE5BLOCK_BODY); write it into the file + wire full_le5_tac_front THEN
   full_le5_tac_stores THEN full_le5_tac_tail THEN full_le5_tac_bridge.
6. LAYER 2 wrapper: copy le4's, s/48+bl1/64+bl1/, s/BYTE_LIST_AT_4BLOCKS/BYTE_LIST_AT_5BLOCKS/,
   GCM_DEC_*_5 unfold lemmas, AES_CTR_5_EL, word 80, kk<4 case-split, `16*4=64`.
   le5_body_spec_args: add cph4/h5/h5k slots.

## COLD-LOAD ORDER GOTCHA
Checkpoint does NOT preload the dec chain, and 2block's needs lists gmult_nblock_lemmas
(references GMULT_REDUCE_PROP3) before 1block (defines it).  Must `hol_load 1block.ml` FIRST,
then the target.  Also `Sys.chdir` to project root after any restart.  le5 `needs le4block`.

## SESSION 2 UPDATE (keep-Q4 fix applied; ~98% complete, residual Not_found in bridge wiring)
The opaque-keystream blocker is SOLVED: front now discards [5;6;7] (keeps Q4), abbreviates
ks0..ks4 at s269. All step indices REDISCOVERED & VERIFIED with keep-Q4 (identical to discard-Q4):
- front -> s297 (pc+4156, more_than_4). VERIFIED (e() clean).
- stores pt0..pt3 -> s352 (pc+4376). VERIFIED (e() clean).  Cadence pt0@s312/pt1@s320/pt2@s336/pt3@s352.
- tail: X1_MOD128_BRIDGE5 after (353--357); masked GHASH (358--376); Q9->cphm collapse @ s376
  (after `and v9,v9,v0`); **block-4 eor3 forms Q12 @ s377** -> capture pt4 THERE (NOT before stepping;
  Q12 is still pt3 at s352, so the pt4 capture MUST come after (377--377)). blend-capture @ s381;
  masked store readback out_p+64 @ **s393** (NOT s392; s392=old outprev, store visible s393);
  step (394--400).  ALL VERIFIED interactively.
- bridge eor v19,v19,v18 @ **s400** (pc+4568, post-eor Q19). BRIDGE_CLOSE_TAC_5 body VERIFIED to
  discharge interactively (qq mids auto-discovered; the merged mid atoms were qq16/qq17/qq18 in one
  run but FOLD_MID_TAC5 now AUTO-DISCOVERS the qq by matching the pmul's hpower — no hardcoded name).
- post-bridge: Q19 rev64 result @ **s402** = `word_join(word_reversefields 8 ..)(..)` (proper BREV
  form, BREV_JOIN_REV8 matches); st1 xi_p; exit pc+4580. VERIFIED Q19 s402 form.

**RESIDUAL BUG (only open item):** running `full_le5_tac_front THEN ...stores THEN ...tail THEN
...bridge` end-to-end raises `Not_found` in the bridge phase, even though every sub-tactic works when
run individually/interactively from the same post-tail state.  The `Not_found` is a bare `List.find`
(BRIDGE_CLOSE_TAC_5's q19asm/h{2..5}asm, or the post-bridge).  Hypothesis: the tail's final
`DISCARD_OLDSTATE_TAC "s400"` or an earlier discard removes the `read Q19 s400` machine assumption
before BRIDGE_CLOSE looks for it; OR the ABBREV of cphm/gval reorders assumptions.  NEXT: run
front+stores+tail, then `top_realgoal()` and check `List.exists (lhs=read Q19 s400)`; if absent, take
the bridge at the pre-discard state or assert Q19 s400 fresh.  All MATH is proven; this is pure wiring.

**File has all fixes applied** (keep-Q4 front, reordered tail, s393 store, s400 bridge, s402 post,
auto-discover FOLD_MID_TAC5).  NOT yet loadt-clean due to the Not_found.

## SESSION 3 UPDATE (2026-07-01): VERIFIED loadt-clean — DONE
A fresh COLD load resolves the SESSION-2 `Not_found`: it was a stale interactive-state
artifact, not a bug in the file.  Full cold-load sequence (from a checkpoint with nothing
preloaded): `Sys.chdir` project root; `needs 1block.ml` (324s); `needs le4block.ml` (2333s);
`needs aes_gcm_dec_spec.ml`/`gmult_nblock_lemmas.ml` (cached); `needs le5block.ml` (**1476s,
clean**).  Post-load checks: `AESV8_GCM_8X_DEC_256_LE5BLOCK_BODY` and
`AESV8_GCM_8X_DEC_256_LE5BLOCK` both bound; `axioms() = 3` (baseline); `hyp = []` for both;
no CHEAT_TAC / new_axiom in the file.  **LE5BLOCK is complete and loadt-clean.**  The
committed d7f9dfd9 message ("not yet loadt-clean") is superseded by this verification.
NEXT band: LE6BLOCK (nfull=5, 81–96B) — mirror le5 with one more full block + 6-term bridge.
