# k=4 (WB_FUSED_4BLOCK) EXACT step map — session 133, traced from d5r_dis.txt

Validated: the SAME trace method reproduces the PROVEN k=3 milestones EXACTLY
(pt0@s80, pt1@s123, bridge@s170, xi@s177, ivec@s180, pt2@s182, b@s183).

## k=4 control flow (nblk=4 => x9 = 16*nblk = 0x40)
- front 0x20..0x3c: `b.le 1368` TAKEN (0x40 <= 0x40). steps 1..8.
- 0x1368..0x13a8 setup: steps 9..25.
- dispatch: s26=0x13ac cmp x9,0x20; s27=0x13b0 b.gt->13c0 (TAKEN); s28=0x13c0 cmp x9,0x30;
  s29=0x13c4 b.eq (NOT taken, 0x40!=0x30); s30=0x13c8 `b 13cc`.
- preamble @0x13cc: s31 ldr q24,[x6,#80]=h4; s32 ldr d25,[x6,#72]=fold(h4);
  s33 ext v21; s34 eor v21; s35 pmull2 v17 (blk0 hi); s36 pmull v19 (blk0 lo);
  s37 pmull v18 (blk0 mid); s38 `b 144c`.
- shared tail: s39=0x144c (window0 start).

## SIM windows (matching k=3 template structure exactly)
| region | k=3 (PROVEN) | k=4 (this session) |
|---|---|---|
| plain steps | (1--30) | **(1--30)** |
| window0 blk0×H^k KEEPGHALL | (31--80) pt0@s80 | **(31--81) pt0@s81** |
| window1 blk1×H^(k-1) KEEPGHALL | (81--123) pt1@s123 | **(82--124) pt1@s124** |
| window2 blk2×... KEEPGHALL | (124--170) bridge@s170 | **(125--167) pt2@s167** |
| window3 blk3×H+reduce KEEPGHALL | n/a | **(168--214) bridge@s214** |
| tail brev xi (rev64 v19) | s174 | **s218** |
| xi store st1{v19} | s177 | **s221** |
| ivec store str q30 | s180 | **s224** |
| last-block store str q0 | s182 | **s226** |
| rejoin `b 11d0` | s183 | **s227** |

NOTE the plain region is (1--30) for BOTH — the extra dispatch branch (k4 s30=`b 13cc`)
lands so that the preamble pmulls fall at s35-37, INSIDE window0's KEEPGHALL (31--81),
exactly like k=3's preamble pmulls at s34-36 inside its (31--80). So window0 = (31--81).

## Per-block store PCs (shared tail; each str q0,[x2],#16)
- blk0 store 0x14f4 (k4 s81); blk1 store 0x15a0 (k4 s124); blk2 store 0x164c (k4 s167);
- xi st1{v19},[x3] 0x1724 (k4 s221); ivec str q30,[x16] 0x1730 (k4 s224);
- blk3 store 0x1738 (k4 s226); b 11d0 0x173c (k4 s227).

## H-power reads per window (from disasm)
- preamble/window0 (blk0 × H^4): q24=[x6,#80]=h4, d25=[x6,#72]=fold(h4)  [UNSPLIT h3k@64 hi]
- window0 also re-loads @0x1460 q24=[x6,#80], @0x1464 d25=[x6,#72] (blk0 slot at 0x144c uses H^4)

WAIT: 0x144c slot (s39..s81) ALSO reads [x6,#80]/[x6,#72] (h4/fold h4) at s44/s45.
So window0 = block-0 × H^4 (the FIRST ciphertext block, highest power). Good.
- window1 slot 0x14f8 (s82..): @0x150c q24=[x6,#48]=h3, @0x1510 d25=[x6,#64]=fold(h3)
- window2 slot 0x15a4 (s125..): @0x15b8 q24=[x6,#32]=h2, @0x15bc d25=[x6,#24]=fold(h2)
- window3 slot 0x1650 (s168..): @0x1664 q24=[x6]=h, @0x1668 d25=[x6,#16]=fold(h) + reduce

## htable reads needed (UNSPLIT + address norms)
htbl layout: +0=h, +16=hk=[fold(h)@16, fold(h2)@24], +32=h2, +48=h3, +64=h3k=[fold(h3)@64, fold(h4)@72], +80=h4
k=4 reads: h4@80 (q24), fold(h4)@72 (d25), h3@48, fold(h3)@64, h2@32, fold(h2)@24, h@0, fold(h)@16.
So UNSPLIT: hk@16 (gives fold(h)@16 lo, fold(h2)@24 hi) AND h3k@64 (gives fold(h3)@64 lo, fold(h4)@72 hi).
Precondition needs h4 read: `read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4`.
Address norms: htbl+16+8=htbl+24 (fold h2), htbl+64+8=htbl+72 (fold h4).

## BRIDGE (VALIDATED by wb4_diag.ml stage-1 run, RESTORE_EXIT=0, 2026-08-19)
Full 4-window SIM reaches s214 self-contained; after `ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC`
the goal has the SAME shape as k=3 (only block-0 x H^4 mid/hi/lo need distribution; blocks 1/2/3
mids matched by MERGE_2BLK). The 3 block-0(H^4) distributions (from QQDEF dump, wb4diag_clean.txt):
  qq14 = pmul(brev xi_hi (+) brev cph0_hi, h4_hi); qq9=xi_hi*h4_hi, qq1=cph0_hi*h4_hi
    => `qq14 = word_xor qq9 qq1`   (HI — WORD_XOR_ACI, k=3's qq11 slot)
  qq13 = pmul(brev xi_lo (+) brev cph0_lo, h4_lo); qq8=xi_lo*h4_lo, qq0=cph0_lo*h4_lo
    => `qq13 = word_xor qq8 qq0`   (LO — WORD_XOR_ACI, k=3's qq10 slot)
  qq20 = pmul((xi(+)cph0) mid, h4 mid); qq15=xi_mid*h4mid, qq16=cph0_mid*h4mid
    => `qq20 = word_xor qq15 qq16` (MID — PMUL_CONG_128+WORD_BLAST, k=3's qq16 slot)
BRIDGE_CLOSE_4_CPH3_TAC = BRIDGE_CLOSE_3_CPH2_TAC with spec_to_byteform_wb4 (CONJ h2 (CONJ h3 h4)),
GMULT4_FULL_CORRECT_BA, dec_bridge_specl_4_cph3, and these 3 distributions.

## Remaining for the CLOSE run
1. block-3 store @s226 needs gcm_ctr_inc^3 closer (GCM_CTR_INC3_LANES, in ckpt via le4block).
   ivec = gcm_ctr_inc_iter 4 (needs GCM_CTR_INC4_LANES; le5block:107 — DEFINE IN-FILE if absent).
2. MAYCHANGE frame WB4_FRAME_SUBSUMED/WB4_FRAME_IMP: k=3's is ~52 single-comp; k=4 adds
   mem :> bytes128 (out_p+48). stage-2 DUMPs the exact frame, then final run builds the lemma.
Tail: brev v19 @s218 (0x1718). Split s227 bytes128 stores to bytes64; norms +16+8=+24,+32+8=+40,+48+8=+56.

## STAGE-2 RESULT (wb4_close.ml, RESTORE_EXIT=0, 2026-08-19 13:57)
- BRIDGE-CLOSED-s214 FIRED => qq14=qq9(+)qq1, qq13=qq8(+)qq0, qq20=qq15(+)qq16 are CORRECT.
- Full tail SIM to s227 OK; ENSURES_FINAL goal-len=16112 nasl=1303.
- HARNESS ARTIFACT: interactive e() applies each tactic only to the FIRST subgoal, so after
  REPEAT CONJ_TAC only the first conjunct (block-1 hi-half, RHS aes256_encrypt (gcm_ctr_inc ctr0))
  was seen; my closers are guarded (blk0=bare ctr0, blk2=inc^2, blk3=inc^3, ivec) and NONE match
  inc^1 => it fell through to the MC dump. NOT a real failure.
- FIX for final prove(): (a) write as prove() with THEN-chained closers (apply to ALL conjuncts),
  (b) ADD a block-1 (inc^1) closer: guard `gcm_ctr_inc ctr0` AND NOT inc^2/inc^3, body
  GCM_CTR_INC_LANES + aes expand + WORD_BLAST (like blk2/blk3). block-1 does NOT auto-close here
  (unlike k=3 where pt1 capture folded it) — needs its own closer.
- MAYCHANGE frame NOT yet captured cleanly (the dump caught the block-1 goal instead). Options:
  (i) build WB4_FRAME_SUBSUMED by extending k=3's (add mem:>bytes128(out_p+48), and store byte
      count 48->64) and let SUBSUMED_MAYCHANGE_TAC prove it at file top; the accumulated single-comp
      frame should be k=3's + the out_p+48 store + block-3 Q-regs;
  (ii) OR in the final prove(), close MAYCHANGE the staggered-WB_TAIL_4 way:
      DISCARD non-maychange THEN REWRITE[ABI] THEN REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC
      (s130 showed this spins post-SIM on bloated heap; WB3_FRAME_IMP avoided it). Prefer (i).
