# k=4 (WB_FUSED_4BLOCK) disassembly facts — gathered s132 for the next session

## Headline from s132: the fused-block proofs are SLOW BUT FINITE.
k=3 (WB_FUSED_3BLOCK, session-130-work/wb3_v11_lemma.ml == session-132-work/WB_FUSED_3BLOCK_PROVEN.ml)
proves hyps=0 no-CHEAT; the `prove` closure takes ~777s CPU (~13min) on top of ~7min SIM. Use the
45-min-timeout vehicle **/tmp/restore_fused_long.sh <check.ml> <TAG> 2700** (NOT restore_fused.sh,
whose 1800s timeout kills the k=3+ replay early — that is what fooled s128-131). ps-check for a
>50%-CPU DMTCP:ocaml-hol first; kill restores by high-CPU pid ONLY; base MCP is separate.

## Fused dispatch (from /tmp/s108work/d5r_dis.txt), entry 0x13ac:
    13ac: cmp x9,#0x20 ; 13b0: b.gt 13c0
    13b4: cmp x9,#0x10 ; 13b8: b.eq 142c (nblk=1 section)
    13bc: b 140c       (nblk=2 section)
    13c0: cmp x9,#0x30 ; 13c4: b.eq 13ec (nblk=3 section)
    13c8: b 13cc       (nblk=4 section = FALL-THROUGH, x9=0x40)

## nblk=4 section preamble @ 0x13cc (reads H^4 table entries, block-0 x H^4 GHASH round):
    13cc: ldr q24,[x6,#80]   <- h4  (htbl+80)
    13d0: ldr d25,[x6,#72]   <- fold(h4) hi-half of h3k  (htbl+72; needs (htbl+64)+8=htbl+72 norm)
    13d4: ext v21,v16,v16,#8
    13d8: eor v21.8b,v21,v16
    13dc: pmull2 v17,v16,v24  (block-0 x h4, hi)
    13e0: pmull  v19,v16,v24  (block-0 x h4, lo)
    13e4: pmull  v18,v21,v25  (block-0 x fold(h4), mid)
    13e8: b 144c             <- merges into the SHARED tail at 0x144c (same tail k=1/2/3 join)
Compare nblk=3 @ 0x13ec reads q24=[x6,#48]=h3, d25=[x6,#64]=fold(h3), then b 14f8.
So k=4 uses **htbl+80=h4 and htbl+72=fold(h4)** (h3k hi-half). UNSPLIT h3k@64 gives lo=fold(h3)@64,
hi=fold(h4)@72. Also still need hk@16 (fold(h)) + hk@24 (fold(h2)) + h2@32 + h3@48 for the 4 windows.

## Store PCs (shared tail; each `str q0,[x2],#16` advances out_p by 16):
Same shared tail as k=3. k=3 stores were @0x14f4/0x15a0/0x164c (block 0/1/2) then
xi st1{v19}@0x1724, ivec str q30@0x1730, block-3 str q0@0x1738, b 11d0.
For k=4 there is one MORE block store; read exact PCs from d5r_dis.txt around 0x144c..0x1738.

## Bridge assets (ALL EXIST — do not re-derive):
- spec_to_byteform_wb4  (wb.ml:1942) — define in-file (NOT in ckpt). Body copied below.
- GMULT4_FULL_CORRECT_BA = snd(build_GMULTn_fast 4) (wb.ml:1941) — IN CKPT (le-chain builds it).
- k=4 bridge specl (wb.ml:2631-2634): [word_xor(brev xi)(brev cph0); byteswap128 h4;
    brev cph1; byteswap128 h3; brev cph2; byteswap128 h2; brev cph3; byteswap128 h].
- GCM_CTR_INC4_LANES (le5block.ml:107) — need it; le5block may NOT be in the fused ckpt
  (ckpt loads up to le4block per restore_fused.sh comment). VERIFY: if absent, copy its
  proof body into the check file (it's a WORD_BLAST-style lane lemma).
- 3 block-0 (H^4) mid distributions: same shape as k=3's qq11/qq10/qq16 (index-shifted). The
  s127 diagnostic pattern (BRIDGE_CLOSE_3_CPH2_TAC lines 103-114 of WB_FUSED_3BLOCK_PROVEN.ml)
  generalizes; adapt for 4 blocks with cph3 unmasked.

## Route (same as k=3, one more window):
4 KEEPGHALL windows (g4/blk0 x H^4, g3/blk1 x H^3, g2/blk2 x H^2, g1/blk3 x H + reduce), then
bridge @ s214 (per STATE continuation: "k=4 bridge s214"), then tail stores + xi + ivec +
MAYCHANGE (via a WB4_FRAME_IMP built at file top, same pattern as WB3_FRAME_IMP lines 20-52).
Window step numbers: k=3 was (1--30),(31--80),(81--123),(124--170), tail 171-183. k=4 dispatch
is 1 branch longer (the 0x13c8 `b 13cc` fall-through). Verify the g-stride (~43 steps/window) and
pt0 store step from a step-trace or by reading d5r_dis.txt; STATE session-128 note said
"pt0@s81, verify from d5r_dis.txt g-stride 43".

## MAYCHANGE frame for k=4:
Add one more out-block region: memory :> bytes(out_p,64) (vs 48 for k=3), and the exit
postcond gets a 4th out store `word_xor cph3 (aes256_encrypt (gcm_ctr_inc_iter 3 ctr0) keys15)`.
Build WB4_FRAME_SUBSUMED/WB4_FRAME_IMP at file top exactly like WB3 (lines 20-52), extending the
single-component `,,` list with the extra out+48 region + block-3 Q-regs actually written.

## spec_to_byteform_wb4 (copy verbatim into the check file — deps: GHASH_POLYVAL_ACC_4 in ckpt):
    let spec_to_byteform_wb4 = prove
     (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
       byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
       byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
       ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
            [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3] =
           polyval_reduce_prop3
            (word_xor (word_xor (word_xor
              (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h4))
              (word_pmul (word_bytereverse cph1) (byteswap128 h3)))
              (word_pmul (word_bytereverse cph2) (byteswap128 h2)))
             (word_pmul (word_bytereverse cph3) (byteswap128 h)))`,
      STRIP_TAC THEN
      REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
        (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
                `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
                `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`] GHASH_POLYVAL_ACC_4)] THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;
