# LE2BLOCK (17-31 byte band) scaffold — validated close, pending binary sim

**Date:** 2026-06-21. Goal: `AESV8_GCM_8X_ENC_256_LE2BLOCK_BYTELIST` — bit_len = 128 + 8*bl1,
1<=bl1<=16 (one FULL block 0 + one MASKED partial block 1), out_p postcond as the single
`byte_list_at (aes_ctr_full_tail_bytes ctr0 [pt0;pt1] keys 1 bl1) out_p (word (16+bl1))` clause.

## Control-flow finding (confirmed from the .S dispatch + the two existing proofs)
- 17-31 bytes: tail dispatch `cmp x5,#16; b.gt` is TAKEN (x5 = 16+bl1 > 16) -> `more_than_1`
  (full block 0, GHASH vs H^2) -> falls through to `less_than_1` (block 1).
- This is the SAME path the whole-block 2BLOCK takes (x5=32). The ONLY divergence is in
  `less_than_1`: mask is all-ones (whole) vs `word(2 EXP (8*bl1)-1)` (partial).
- So: front + block-0 (steps ~1-325) = whole-block 2BLOCK VERBATIM modulo the symbolic
  bit_len cascade (use LE1BLOCK's bl_resolve_pc / USHR_8BL_LEMMA / X5 machinery, retargeted
  to the 2-block tail PCs). less_than_1 tail = LE1BLOCK symbolic-mask stepping
  (MASK_LEMMA, BLEND_OR_XOR, Q9 mask collapse before rev64). Bridge = GHASH_POLYVAL_ACC_2
  with block-1 element = word_bytereverse (word_and ct1 MK).

## NOT ENSURES_SEQUENCE_TAC (re-confirmed)
The le-1block theorem cannot be plugged in as the `less_than_1` segment: at that PC the
accumulators already hold block 0's H^2 contribution (vs just folded xi in the standalone
1-block), so the intermediate state doesn't match; plus ENSURES_SEQUENCE_TAC is frame-
incompatible with our 4-region stack frame. Reuse = shared tactics/lemmas, not nested theorems.

## VALIDATED (cheap, mock-checked 2026-06-21): the byte_list_at close
Given the strong-ensures theorem `...LE2BLOCK` (EL 0 full block-0 read + masked-blend block-1
read + xi_p), the byte_list_at corollary closes via ENSURES_POSTCONDITION_THM +
BYTE_LIST_AT_NBLOCK_CTR (nfull=1). The 6 bridge antecedents discharge as:
  1<=bl1; bl1<=16; val(word(16+bl1))=16*1+bl1 (VAL_WORD_EQ, bl1<2^64);
  1<LENGTH[pt0;pt1] (=2); (!k<1. read = EL k ...) [k=0, WORD_ADD_0, 16*0];
  masked read [16*1 -> 16].
This is the same cheap postcond-weakening pattern as 2BLOCK_BYTELIST / LE1BLOCK_BYTELIST.

## DONE (2026-06-22): the strong-ensures binary simulation + byte_list corollary
`AESV8_GCM_8X_ENC_256_LE2BLOCK` (masked-blend postcond) AND
`AESV8_GCM_8X_ENC_256_LE2BLOCK_BYTELIST` (byte_list_at, nfull=1) PROVED end-to-end.
Final proof: `arm/proofs/aesv8_gcm_8x_enc_256_le2block.ml` (loadt-clean, no cheats,
3 standard axioms; ~8.4 min with the 2block dep cached).  Key pieces realised:
- Front 1-259 = 2BLOCK verbatim; X9 via USHR_128_8BL_LEMMA, s260 tail branch via X5_ZERO_LEMMA2.
- Tail cascade: x5 = word(16+bl1) symbolic.  New resolvers (LE32 ival lemmas):
  bl2_resolve_pc (fall-through #112..#48), bl2_resolve_pc_bdy (#32, boundary 16+bl1=32
  allowed), bl2_resolve_pc16_taken (#16 b.gt TAKEN -> more_than_1 pc+4340).
- Block-0 GHASH vs H^2 + block-1 GHASH vs H: 2BLOCK verbatim, EXCEPT less_than_1 mask.
- less_than_1 mask: X1 = (128+8*bl1) AND 0x7f, bridged to (8*bl1) AND 0x7f by the new
  X1_MOD128_BRIDGE so LE1BLOCK's MASK_LEMMA applies with bl:=bl1; Q9 collapses to
  word_and ct1 MK (MK = word(2 EXP (8*bl1)-1)); masked-blend out_p store via BLEND_OR_XOR.
- Bridge: 2BLOCK GHASH_POLYVAL_ACC_2 route, block-1 element = word_bytereverse(word_and ct1 MK).
- byte_list close: VALIDATED ENSURES_POSTCONDITION_THM + BYTE_LIST_AT_NBLOCK_CTR nfull=1
  (k<1 -> k=0 read EL 0; masked read EL 1; val(word(16+bl1))=16*1+bl1; 1<LENGTH[pt0;pt1]).
- Step-index note: the symbolic cascade single-steps each b.gt, so LE2BLOCK reaches
  more_than_1 at s313 (2BLOCK: s315), a -2 offset; downstream PCs identical (same code).

## PROGRESS 2026-06-22 — front replayed + helper lemmas proved

Confirmed (live, on the loaded 2block dep): the whole-block 2BLOCK front replays VERBATIM for
the symbolic 17-31 band through step s259 (prologue 1-5, CTR setup 6-30, AES bulk 31-178,
GHASH fold 179-259) — these are length-agnostic. The ONLY front changes are the symbolic
bit_len resolutions, for which two helper lemmas are now PROVED and should be pasted into the
LE2BLOCK proof (or aes_ctr_spec.ml):

```
let USHR_128_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (128 + 8 * bl1):int64) 3 = word (16 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (128 + 8 * bl1):int64) = 128 + 8 * bl1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let X5_ZERO_LEMMA2 = prove
 (`!bl1. 1 <= bl1 /\ bl1 <= 16
        ==> word_and (word_sub (word (16 + bl1)) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [WORD_RULE `word_sub (word (16 + bl1):int64) (word 1) = word (15 + bl1)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `j < 7` THENL
   [REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `~bit j (word 18446744073709551488:int64)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `j < 7` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[BIT_WORD] THEN
    SUBGOAL_THEN `15 + bl1 < 2 EXP j` (fun th -> SIMP_TAC[th; DIV_LT; ODD; DE_MORGAN_THM]) THEN
    TRANS_TAC LTE_TRANS `2 EXP 7` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;
```

WHERE THEY GO in the front (replacing 2BLOCK's concrete-32 handling):
- After the prologue (s5), X9 = `word_ushr (word(128+8*bl1)) 3`; rewrite with USHR_128_8BL_LEMMA
  to `word (16+bl1)` (analog of 2BLOCK using `word 32`).
- At the s260 branch `cmp x0,x5; b.ge`: x5 = `((byte_len-1)&~127)+in_p`. Rewrite x5's
  `word_and (word_sub (word(16+bl1)) (word 1)) (word ...80)` to `word 0` via X5_ZERO_LEMMA2 +
  USHR_128_8BL_LEMMA, then WORD_ADD_0 -> x5=in_p, so in_p-in_p=0 -> tail (INT_SUB_REFL like 2block).

## X1_MOD128_BRIDGE — PROVEN 2026-06-24 (was REFERENCED BUT NEVER DEFINED — enc le2block bug)
`arm/proofs/aesv8_gcm_8x_enc_256_le2block.ml` (committed e2393c1e) USES X1_MOD128_BRIDGE at
line 292 but it is **defined nowhere in the repo** -> that file does NOT loadt standalone
(Unbound value). The memory "enc le2block loadt-clean" note was inaccurate. Proven now:
```
let X1_MOD128_BRIDGE = prove
 (`!bl1. bl1 <= 16
    ==> word_and (word (128 + 8 * bl1):int64) (word 127) =
        word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (128 + 8 * bl1):int64) = 128 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `128 + 8 * bl1 = 8 * bl1 + 1 * 128`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;
```
Use after the front, before the Q9 mask collapse:
`MP_TAC(SPEC bl1 X1_MOD128_BRIDGE) THEN ASM_REWRITE_TAC[] THEN
 DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))`, then MASK_LEMMA applies with bl:=bl1.

## CASCADE divergence (the one real difference from 2BLOCK, still TODO in the script)
2BLOCK has x5=32 (concrete); LE2BLOCK has x5 = word(16+bl1), symbolic. The tail cascade
`cmp x5,#112/.../16; b.gt` must resolve: for 17<=byte_len<=31, all b.gt for thresholds 112..32
are NOT taken, and `cmp x5,#16; b.gt` IS taken -> more_than_1 (block 0 full). Need a
`bl_resolve`-style resolver for x5=16+bl1 at the 2block tail PCs (LE1BLOCK's bl_resolve_pc is
for x5=bl with ALL falling through; here the #16 compare is TAKEN). Build a small variant:
val(word(16+bl1)) = 16+bl1 (VAL_WORD_EQ), and 16+bl1 > 16 (since bl1>=1), 16+bl1 <= 31 < 32.

## REMAINING (script it, loadt-iterate; do NOT live-step — 370 steps, b() reverts everything)
1. Front 1-259 verbatim from 2BLOCK + the two helper lemmas above for X9/X5.
2. Cascade 260-~315: resolve to more_than_1 (block 0 full, x5=16+bl1>16) then less_than_1.
3. block-0 more_than_1 GHASH vs H^2: verbatim from 2BLOCK.
4. less_than_1 block-1: MIRROR LE1BLOCK symbolic mask (Q9 collapse to word_and ct1 MK before
   rev64, MASK_LEMMA, BLEND_OR_XOR), GHASH vs H. mask MK = word(2 EXP (8*bl1)-1).
5. bridge: GHASH_POLYVAL_ACC_2 with block-1 element = word_bytereverse (word_and ct1 MK)
   (2BLOCK bridge, but block1 masked). then ext+rev64+store, ENSURES_FINAL_STATE.
6. byte_list_at corollary: VALIDATED close (ENSURES_POSTCONDITION_THM + BYTE_LIST_AT_NBLOCK_CTR
   nfull=1) — see scaffold above.

## DEC LE2BLOCK cascade — VERIFIED step→PC map (2026-06-24, live)
Dec routine (4612 bytes). Front 1-265 = dec 2BLOCK verbatim + USHR_128_8BL_LEMMA (X9 at s5,
X4/X5 at s265) + X5_ZERO_LEMMA2 (s254→s255 tail branch via INT_SUB_REFL). Then tail eor3 →
Q12=pt0 at s266-269 (abbrev pt0). Symbolic tail cascade (x5 = word(16+bl1)), b.gt PCs from
objdump of aesv8_gcm_8x_dec_256.o:
  s270 b.gt #112 (PC pc+3804, conditional) -> resolve fall pc+3808
  s282 b.gt #96  -> fall pc+3856
  s290 b.gt #80  -> fall pc+3888
  s297 b.gt #64  -> fall pc+3916
  s303 b.gt #48  -> fall pc+3940
  s309 b.gt #32  -> fall pc+3964   (use bl2_resolve_pc_bdy: 16+bl1=32 boundary at bl1=16)
  s312 cmp #16 (PC pc+3976 concrete) ; STEP s313 -> b.gt #16 conditional -> TAKEN pc+4340 = more_than_1
(Step numbers MATCH enc le2block exactly: 270/282/290/297/303/309/313.)
KEY GOTCHA: each b.gt at sN leaves PC as a symbolic `if cond then TAKEN else FALL`. Resolve with
bl2_resolve_pc sN k fall (proves =fall, COND false) THEN DISCARD the stale conditional PC
(it has >1 `word(pc+..)` subterm). The #16 is the ONLY taken branch: must STEP s313 first to
get the conditional, THEN bl2_resolve_pc16_taken 313 4340 + discard stale.
At s313 PC=pc+4340 the state EQUALS the dec 2BLOCK whole-block proof at its s313 more_than_1
(Q12=pt0, Q17/18/19=0, X5=word(16+bl1)). From here: block-0 full GHASH vs H^2 (dec 2BLOCK
verbatim) + block-1 MASKED (X1_MOD128_BRIDGE so MASK_LEMMA bl:=bl1; Q9->word_and cph1 MK;
masked-blend store) + DEC_2BLK_GMULT2_BRIDGE_TAC bridge (block1 = brev(word_and cph1 MK)).

## DEC LE2BLOCK — FULL FRONT VERIFIED to s370 bridge (2026-06-24 session, live)
Reached the bridge state s370 (pc+4568 analog) end-to-end, symbolic bl1. Working step sequence
(all on the dec 2block dep loaded; helpers USHR_128_8BL_LEMMA/X5_ZERO_LEMMA2/IVAL_WORD_LE32/
IVAL_WSUB_LE32/X1_MOD128_BRIDGE + bl2_resolve_pc/_bdy/_16_taken + MASK_COLLAPSE_CPH1_SYM_TAC
defined in-session):
1. REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE[C_ARGUMENTS;SOME_FLAGS] THEN ENSURES_INIT s0 THEN
   RULE_ASSUM[C_ARGUMENTS] THEN ARM_STEPS 1--5 THEN MP_TAC USHR_128_8BL_LEMMA (fold X9->word(16+bl1)).
2. CTR 6--30 (per-step GCM_SIMD_SIMPLIFY + mk_discard2[2..7]); AES 31--84,85--173; tag 174--177
   (+SIMD), 178--184, 185--254 (all mk_discard2[2..7;30]).
3. MP_TAC X5_ZERO_LEMMA2 (X5 mask->0) THEN RULE_ASSUM[WORD_ADD_0]; ARM_VSTEPS [255]
   (+INT_SUB_REFL); ARM_STEPS 256--265 (+mk_discard2[2..6;30]); MP_TAC USHR_128_8BL_LEMMA;
   RULE_ASSUM(CONV_RULE(TRY_CONV(REWR_CONV(WORD_RULE `word_sub(word_add in_p(word(16+bl1)))in_p=word(16+bl1)`)))) -> X5=word(16+bl1).
4. ARM_STEPS 266--269 (tail eor3 -> Q12); SPEC pt0 + ANTS aes256_encrypt-expand + WORD_BLAST; ABBREV pt0.
5. Cascade: ARM_STEPS 270--270 then dec_bl2_resolve 270 112 3808 (=bl2_resolve_pc + discard stale
   conditional PC, where stale = >1 word(pc+) subterm). Then ARM_STEPS to each next b.gt and resolve:
   271--282 -> 282 96 3856; 283--290 -> 290 80 3888; 291--297 -> 297 64 3916; 298--303 -> 303 48 3940;
   304--309 -> bl2_resolve_pc_bdy 309 32 3964 (+discard). Then ARM_STEPS 310--312 (s312 PC=pc+3976,
   the #16 cmp); ARM_STEPS 313--313 (b.gt #16 -> conditional); bl2_resolve_pc16_taken 313 4340 (TAKEN
   -> more_than_1) + discard stale.  [step #s MATCH enc le2block exactly.]
6. more_than_1 block-0 full: ARM_VSTEPS_FOLD 314--320; SUBGOAL read(out_p)s320=pt0 [ASM_REWRITE then
   on the readback subgoal EXPAND pt0 + aes256_encrypt-expand + WORD_BLAST]; DISCARD_OLDSTATE s320.
7. block-1 eor3 -> pt1: ARM_VSTEPS_FOLD 321--328; SPEC pt1 (GCM_CTR_INC_LANES + aes expand + WORD_BLAST);
   ABBREV pt1; DISCARD_OLDSTATE s328.
8. into less_than_1: ARM_VSTEPS_FOLD 329--335 THEN DISCARD_OLDSTATE s335 THEN mk_discard2[1..7].
   X1 = word_sub(word_and(word(128+8*bl1))(word 127))(word 128). MP_TAC X1_MOD128_BRIDGE ->
   X1 = word_sub(word_and(word(8*bl1))(word 127))(word 128) (matches LE1BLOCK MASK_LEMMA form).
9. mask region: ARM_VSTEPS_RESOLVE_SIMD 336--350. SPEC Q9 := word_and cph1 MK + REWRITE[INSERT2_JOIN]
   + ANTS[ASM_SIMP[MASK_LEMMA] THEN WORD_RULE] (collapse Q9). MK = word(2 EXP (8*bl1)-1).
10. GHASH multiply over masked block: ARM_VSTEPS_FOLD 351--363 (+DISCARD s363), 364--369(+DISCARD s369),
    [370](+DISCARD s370).  *** The rev64 at 351 consumes the ORIGINAL Q9 (the SPEC-collapse at s350
    does NOT propagate through the symbolic simulator), so Q17/18/19 carry the un-collapsed mask
    `word_reversefields 8 (word_and (word_insert..(if..)) cph1)`.  FIX (works): after s370,
    MASK_COLLAPSE_CPH1_SYM_TAC — finds the single `word_and <symbolic-mask> cph1` in the assumptions,
    proves it = word_and cph1 MK via REWRITE[INSERT2_JOIN] THEN ASM_SIMP[MASK_LEMMA] THEN WORD_RULE,
    rewrites everywhere. Q19 then = clean GMULT byteform over block-1 = word_and cph1 MK. (Pile
    drops 746k->72k.)
REMAINING from s370: (a) out_p+16 masked-blend store readback was NOT captured during 351-363 —
need to capture `read(out_p+16) = word_xor(word_and pt1 MK)(word_and outprev(word_not MK))` (mirror
dec LE1BLOCK s340/s344 store capture, or recapture by stepping the st1). (b) Bridge:
DEC_2BLK_GMULT2_BRIDGE_TAC with block-1 = brev(word_and cph1 MK) — GMULT2 is operand-generic so
SPECL the masked a1. (c) ext+rev64 371-372 -> word_bytereverse gval; store xi_p 373; close.
(d) _BYTELIST corollary via BYTE_LIST_AT_NBLOCK_CTR nfull=1 tail=bl1. (e) single dispatch theorem.

## DEC LE2BLOCK — bridge + close VERIFIED except out_p+16 masked store capture (2026-06-24)
MAJOR PROGRESS: full proof drives end-to-end to the exit (s373, pc+4580=0x11e4). Bridge CLOSED:
- KEY TRICK for the masked bridge: ABBREV_TAC `cphm = word_and cph1 (word(2 EXP(8*bl1)-1))` AFTER
  MASK_COLLAPSE_CPH1_SYM_TAC, so Q19 becomes the GMULT byteform over the OPAQUE atom cphm — now
  structurally IDENTICAL to the whole-block 2BLOCK bridge with cph1:=cphm. Then the parameterized
  bridge `dec2_gmult2_bridge_tac cphm` (= DEC_2BLK_GMULT2_BRIDGE_TAC with a1=brev cphm, and
  GHASH_POLYVAL_ACC_2 SPECL'd with brev cphm) closes in ~45s. Without the cphm abstraction the
  final LANE_CLOSE WORD_RULE FAILS (the word_and wrapper breaks the qq-atom MERGE pairing).
- spec over cphm: ghash_polyval_acc (bsw h)(brev xi)[brev cph0; brev cphm]; gval ABBREV over it;
  ext+rev64 371-372 -> word_bytereverse gval (WORD_BLAST); store xi_p 373; ENSURES_FINAL_STATE.
- close: ASM_REWRITE closes PC, out_p=pt0, xi_p=word_bytereverse gval (gval/cphm defs expand back
  to brev(word_and cph1 MK)).

REMAINING (ONE issue): the out_p+16 MASKED store readback was NOT captured — I DISCARD_OLDSTATE'd
s363/s369 without first asserting `read(memory:>bytes128(word_add out_p(word 16))) sN = <masked blend>`.
So ENSURES_FINAL_STATE leaves `read(out_p+16)s373 = word_xor(word_and pt1 MK)(word_and outprev(word_not MK))`
unsubstituted. FIX (mirror dec LE1BLOCK s340/s344 + dec 2BLOCK s320 capture): when stepping the
block-1 less_than_1 region, BEFORE discarding, SUBGOAL_THEN
  `read(memory:>bytes128(word_add out_p(word 16))) s<store> =
     word_xor (word_and pt1 MK)(word_and outprev (word_not MK))`
proved by: expand aes256_encrypt towers, ASM_REWRITE[INSERT2_JOIN], ASM_SIMP[MASK_LEMMA],
REWRITE[BLEND_OR_XOR], CONV_TAC WORD_RULE (= dec LE1BLOCK lines 2575-2593 for Q12, then carry the
store readback through the discards via MP_TAC/DISCH like dec 1block s344/s351). The block-1 store
is the `st1 v12,[x2]` around s361-363 (x2=out_p+16). Capture it, carry to s373, then the close's
out_p+16 conjunct matches. Everything else is DONE and verified live.
