(* ========================================================================= *)
(* AES-256-GCM encrypt, the genuine 2-block path of aesv8_gcm_8x_enc_256.     *)
(*                                                                            *)
(* Mirror/extension of the 1-block proof arm/proofs/aesv8_gcm_8x_enc_256_1block *)
(* (theorem AESV8_GCM_8X_ENC_256_1BLOCK).                                       *)
(*                                                                            *)
(* No CHEAT_TAC, no new axioms.                                               *)
(*                                                                            *)
(* STATUS (2026-06-17): DONE.  loadt-clean, binds AESV8_GCM_8X_ENC_256_2BLOCK,  *)
(* no cheats, 3 (standard) axioms.  FULL postcondition: out_p block-0 = ct0,    *)
(* out_p block-1 = word_xor plaintext1 (aes256_encrypt ctr1 keys), and          *)
(* xi_p = word_bytereverse (ghash_polyval_acc (byteswap128 h)(brev xi)          *)
(* [brev ct0; brev ct1]).  The block-1 AES counter ctr1 is exposed as a spec    *)
(* var pinned by the precond ctr1 = gcm_ctr_inc ctr0 (the rev32+ADD+rev32 of    *)
(* the top 32-bit lane); GCM_CTR_INC_LANES bridges it to the lane-byte form.    *)
(* The 2-product GHASH bridge closes via the targeted MERGE_2BLK_TAC (products  *)
(* paired by free-var/lane signature, W-reduction pmuls by shared word-const,    *)
(* operand equalities closed by FAST_OPERAND_TAC: flatten lanes + WORD_BITWISE,  *)
(* ~1s vs ~90s WORD_BLAST) + FINISH_2BLK_TAC; bridge ~73s, ~16 min total loadt   *)
(* incl. the 1-block dep.  Direct C_ARGUMENTS entry at pc+0x18 (no ENSURES_TRANS *)
(* wrapper), exit pc+0x11d8.  See _docs/2block_handoff/BRIDGE.md for history.    *)
(* ========================================================================= *)

(* -------------------------------------------------------------------------
   PROGRESS / PLAN
   -------------------------------------------------------------------------
   GOAL: prove the real binary's 2-block (bit_len = 256) path, exit pc TBD,
   with the GHASH list [brev ct0; brev ct1] and key byteswap128 h.

   CONTROL FLOW (confirmed from the .S, 2026-06-15):
     byte_len = 32 -> x5 = ((32-1) & ~127) + x0 = x0, so x0 >= x5 at pc+0x163
     (line 354/355) => branch to .L256_enc_tail (NOT the 8-way main_loop).
     In the tail: x5 = x4 - x0 = 32; cmp x5,#112/96/.../16 all fall to the
     `b.gt .L256_enc_blocks_more_than_1` (x5=32 > 16) => process ONE full
     block via the more_than_1 body, then fall into less_than_1 for the last
     block.  So 2 blocks = more_than_1 (block 0, GHASH vs H^2-... actually vs
     the per-block htable power) + less_than_1 (block 1).

     => NO trn1/trn2 (that is only Loop_mod2x_v8, which 2 blocks does NOT
     reach).  The cascade uses htable-loaded karatsuba mids (ins/pmull),
     matching GHASH_POLYVAL_ACC_2's shape.  This is the FAVORABLE path: the
     2-block extension doc (ghash-2block-extension-and-mila-comparison) feared
     Loop_mod2x_v8; the real 2-block path avoids it.

   GHASH at 2 blocks (aggregate-then-reduce-once, per the tail):
     more_than_1 GHASHes brev(ct0) into hi/mid/lo accumulators (against the
     H^2 power loaded from htable), less_than_1 GHASHes brev(ct1) (against H),
     XORs into the same hi/mid/lo, then ONE Prop3 reduction (MODULO block).
     Spec closes via GHASH_POLYVAL_ACC_2:
       ghash_polyval_acc h a [b;c] =
         prop3(pmul(a XOR b, polyval_dot h h) XOR pmul(c, h))
     (already proved in common/polyval_ghash.ml).

   KEY CONVENTION: byteswap128 h (verified consistent; see methodology §6c).
     2-block htable preconditions add H^2 slot and its mid:
       read (htbl_p+32) = byteswap128(polyval_dot h h)   [H^2, lanes-exch]
       and the karatsuba mid for h^2 from the packed mid slot at htbl_p+16
       (hi lane) -- need to check the exact lane the more_than_1 path reads.

   PCs (confirmed by objdump of the .o, 2026-06-15):
     body entry           pc+0x2c   (same as 1-block)
     branch cascade       pc+0xf08 .. 0xf88 (cmp x5,#0x60/0x50/.../0x10; b.gt)
       x5 = 32 (0x20): cmp #0x20 b.gt 0x10b8 -> 32>32 FALSE (fall);
                       cmp #0x10 b.gt 0x10f4 -> 32>16 TRUE  -> more_than_1.
     more_than_1 body     pc+0x10f4 .. 0x1134  (block 0 GHASH vs H^2 power)
       0x10f8 ldr q22,[x6,#32]  = byteswap128(h_power h 1)   [the H^2 slot]
       0x1124 ldr q21,[x6,#16]  = packed mid (mid(h^1)|mid(h^2)), uses hi lane
       hi=pmull2 v28, lo=pmull v26, mid=pmull2 v27 -> accumulate v17/v19/v18
     less_than_1 body     pc+0x1138 .. 0x11d4  (block 1 GHASH vs H, + reduce)
       (same as the 1-block less_than_1; here the hi/mid/lo already hold
        block-0 contributions, so the final reduction folds BOTH blocks)
     exit (str q19,[x3])  pc+0x11d4, stop pc+0x11d8.

   STEPS:
     [x] 1. Confirm exit PC and the precise instruction indices (DONE above).
     [ ] 2. Write the spec (precondition: 2 plaintext blocks, htable H + H^2 +
            mids; postcondition: 2 ciphertext blocks + GHASH [brev ct0;brev ct1]).
     [ ] 3. Reuse the 1-block AES/front stepping (it already steps CTR blocks
            v0,v1; only v0 was used at 1 block).  Abbreviate ct0, ct1.
     [ ] 4. Step the more_than_1 body (block 0 GHASH multiply into hi/mid/lo).
     [ ] 5. Step the less_than_1 body (block 1 GHASH multiply + accumulate +
            single reduction).
     [ ] 6. Bridge the pre-reduction Q-state to GHASH_POLYVAL_ACC_2 RHS, then
            to ghash_polyval_acc ... [brev ct0; brev ct1] (mirror 1-block
            bridge GMULT route, generalized to 2 products).
     [ ] 7. Close; verify loadt, no cheats.

   DEAD ENDS / NOTES:
   - KEY NEW OBSTACLE (found 2026-06-15 by stepping the front): the 1-block
     proof's `DISCARD_COUNTER_REGS_TAC` discards `read Q1` (block-1's CTR /
     keystream) whenever it exceeds 500 chars.  2-block NEEDS Q1 preserved
     (it is block-1's AES keystream input = CTR block 1 = rev32 of the
     once-incremented Q30).  So the front CANNOT reuse the 1-block discard
     calls verbatim — must keep Q1 (and Q9/Q8 for the 2nd ciphertext+GHASH)
     alive.  Plan: write a 2-block DISCARD_COUNTER_REGS_TAC variant that keeps
     Q1 (and the regs the more_than_1/less_than_1 GHASH uses: Q8,Q9,Q16,Q17,
     Q18,Q19,Q26,Q27,Q28), or step with finer granularity and abbreviate ct0
     (Q9 at the block-0 store ~0x10f4) and ct1 (the 2nd block result).
   - The block-0 ciphertext is stored by `st1 {v9},[x2],#16` at 0x10f4 (start
     of more_than_1) and out_p advances by 16; block-1 stored at 0x1184-ish in
     less_than_1.  Spec out_p region is 32 bytes (two blocks).
   - CTR increment: block 1's counter = rev32(rev32(ctr0)+ (1<<96-lane)).  The
     1-block never needed ct1, so this byte-arithmetic was never modeled here.
     Either expose ct1 = aes256_encrypt ctr1 keys with ctr1 a fresh var + a
     precond pinning ctr1, OR derive ctr1 symbolically in the sim (heavier).
     Mila's extraction sidesteps this; we must do it for binary faithfulness.

   STATUS 2026-06-15: spec drafted + front stepped interactively to s265
   (target PC pc+0x10f4 = more_than_1).  Findings at s265:
     read Q9 s265 = ct0 = word_xor plaintext0 (aes256_encrypt ctr0 keys)  [block-0 ciphertext]
     read Q8 s265 = plaintext0   (the loaded block, pre-XOR copy)
     read Q0 s265 = aes tower over ctr0 (block-0 keystream)
     read Q19 s265 = folded GHASH tag word_join(rev xi_lo)(rev xi_hi)  [survives]
     read X0 s265 = in_p+16 (block-0 consumed; block-1 not yet loaded)
   Step 255 needs ARM_VSTEPS_TAC [255] THEN RULE_ASSUM_TAC(REWRITE_RULE
     [INT_SUB_REFL; INT_OF_NUM_EQ]) to resolve the `in_p - in_p = 0` branch
     to the tail (pc+3768), same idiom as 1-block.

   TAIL DATAFLOW (read from .S 0x1199+):
     .tail: ldr q8,[x0] (block-0 PT); eor3 v9,v8,v0,v29 (ct0 via Q0 keystream).
       Then a CASCADE of `mov v7,v6; mov v6,v5; ... mov v_k,v1` (lines 1216-1277)
       that SHIFTS the keystream registers so the correct per-path keystream
       lands in the slot the more_than_N/less_than_1 body consumes.
     For 2 blocks (x5=32): falls to more_than_1 (block-0 GHASH) then less_than_1
       (block-1: `eor3 v9,v9,v7,v29` at .S 1442 uses v7 = block-1 keystream).
     => block-1 keystream (originally CTR block 1 in Q1) IS needed; the `mov`
        cascade routes Q1->...->v7.  The 1-block proof discarded Q1-Q7 because
        the 1-block path uses ONLY Q0's keystream.  2-block MUST keep the
        block-1 keystream alive through the front AND through the mov cascade.

   *** INVESTIGATION (2026-06-15): even with DISCARD_COUNTER_REGS2_TAC (keeps
   Q1) from step 1, Q1 is ABSENT at step 50 (only Q0,Q26,Q27,Q28,Q31 present).
   So Q1's absence is NOT simply the discard filter.  Two candidate causes to
   check next session:
     (a) block-1's keystream is only fully formed after all 15 AES rounds
         (~step 250+); at step 50 it is mid-round and may be carried under a
         different intermediate register, or
     (b) ARM_STEPS' per-step simplifier only keeps the latest write and the
         block-1 CTR/keystream chain isn't being asserted/abbreviated, so it
         evaporates.
   RESOLVED (2026-06-15, 2nd session): the Q1-Q7 "absence" was the COUNTER
   ARITHMETIC EXPLODING, not the discard.  Root cause found by single-stepping:
     - rev32 v30,v0 (0x50, step ~16): Q30 = rev32(ctr0), small (~19 chars).
     - add v30.4s,v30.4s,v31.4s (0x54, step 17): the 4-lane 32-bit CTR
       increment over the symbolic rev32 tree BLOWS Q30 to ~25677 chars.
     - GCM_SIMD_SIMPLIFY_TAC collapses it back to ~727 chars: a clean
       word_join byte-shuffle of ctr0 with `word_add (...) (word 1)` =
       the incremented counter.  The block-N CTR rev32 v_N,v30 then stays
       bounded.
   So the FRONT RECIPE for 2-block: step the CTR setup (0x50..0x8c) folding
   with GCM_SIMD_SIMPLIFY_TAC after each `add v30.4s` so Q30 (and the derived
   block CTRs Q1..Q7) stay bounded; keep Q1 (block-1 keystream src) and Q7
   (the reg the more_than_1 path consumes after `mov v7,v1`).  Do NOT discard
   Q30 mid-setup (the 1-block can because it only needs block 0 = Q0=ctr0;
   2-block needs the increment chain).  After the rounds, abbreviate ct0 (Q9)
   AND ct1 (block-1 result) as atoms, mirroring the 1-block ct abbreviation.
   ctr1 (block-1 AES input) = the folded once-incremented counter; can expose
   as a spec var pinned by the GCM_SIMD_SIMPLIFY normal form, or carry inline.

   *** WORKING FRONT RECIPE (validated interactively 2026-06-15, reaches the
   tail at pc+3772 with Q0,Q1,Q19 all bounded):
     REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
     define DK1  = DISCARD_ASSUMPTIONS_TAC (drop read Q2..Q7,Q30 when >500),
            DK1b = same (keeps Q0,Q1,Q19 implicitly by not listing them).
     ARM_STEPS (1--11)  THEN DK1
     ARM_STEPS (12--16) [reaches 0x50 rev32 v30,v0]  (then the increment chain)
     -- key: after the `add v30.4s` (step 17) Q30 blows to ~25k; FOLD with
        GCM_SIMD_SIMPLIFY_TAC -> ~727 chars, then rev32 v1 (step ~19) gives
        Q1 ~1365 (block-1 counter).  Step in SMALL batches (<=10) with DK1 so
        Q2..Q7,Q30 are dropped before the next increment explodes.
     Continue ARM_STEPS in 1-block-style batches with DK1: (24--30)(31--50)
        (51--84)(85--173) -- Q0,Q1 grow slowly into AES towers (~219/2178 ch).
     At the GHASH tag load (~step 183): Q19 -> 49102 ch; GCM_SIMD_SIMPLIFY_TAC
        folds it to ~122 ch (word_join(rev xi_lo)(rev xi_hi)); use DK1b after.
     (177--184) THEN GCM_SIMD_SIMPLIFY_TAC THEN DK1b ; (185--254) THEN DK1b.
     ARM_VSTEPS [255] THEN RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL;INT_OF_NUM_EQ]).
     (256--262) THEN DK1b THEN RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL;
        INT_OF_NUM_EQ]) ; ARM_STEPS [263] resolves the `in_p-in_p=0` branch to
        pc+3772 (the TAIL, .L256_enc_tail at 0xeb8).
   STATE AT TAIL ENTRY (s263, pc+3772): Q0=block-0 AES tower (aes...ctr0),
     Q1=block-1 AES tower (aes...ctr1 where ctr1 = folded once-incremented
     counter), Q19=folded GHASH tag.  ALL BOUNDED, no explosion.  ~10s total.

   TAIL CASCADE (validated to more_than_1 @ pc+0x10f4 = pc+4340, step ~315):
     - At tail entry need X5 = word 32: RULE_ASSUM_TAC(REWRITE_RULE
       [WORD_RULE `word_sub (word_add in_p (word 32)) in_p = word 32`]) so the
       cmp x5,#112/96/.../16 b.gt cascade auto-resolves (32 not >32, >16 only).
     - eor3 v9,v8,v0,v29 (~step 272, pc+3808) gives Q9=ct0 (block-0 ciphertext,
       ~467 chars: plaintext0 XOR keystream0 XOR v29).
     - The cascade zeroes Q17/Q18/Q19 (GHASH accumulators) and runs the keystream
       mov-shuffle; the in_p-in_p branch at the tail entry resolves via INT_SUB_REFL.
     *** Q7 FIX: the cascade does `mov v7,v1` (.S 1269) so Q7 := block-1 keystream;
       more_than_1 reads v7 for block-1's ciphertext (eor3 v9,v9,v7).  DK1b DROPS
       Q7 (>500) -> simulator can't run that eor3.  FIX: in the tail/cascade
       region use a discard that KEEPS Q7 too (call it DK1c: drop Q2..Q6,Q30 only,
       keep Q0,Q1,Q7,Q19).  Q7 will be ~2666 chars (= Q1).  Switch DK1b->DK1c
       at the tail entry (step ~264 onward).

   FRONT FOLD-TUNING — SOLVED (deterministic, 2026-06-15):
   The CTR setup (steps 1-25, through 0x50..0x8c) must keep Q30 alive while
   folding the increment.  DETERMINISTIC RECIPE (validated, ~15s):
     define mk_discard keepset = DISCARD_ASSUMPTIONS_TAC(>500 AND matches any
       `read Q<n> ` for n in keepset);
     DKctr = mk_discard [2;3;4;5;6;7]   (* keep Q0,Q1,Q30 *)
     DK1   = mk_discard [2;3;4;5;6;7;30] (* keep Q0,Q1; drop Q30 too *)
     DK1b  = DK1   (* keeps Q0,Q1,Q19 in the GHASH-tag region *)
     -- CTR setup: step 1-AT-A-TIME 1..25 with GCM_SIMD_SIMPLIFY_TAC THEN DKctr
        after EACH step (a `for i=1 to 25 do e(ARM_STEPS (i--i) THEN
        GCM_SIMD_SIMPLIFY_TAC THEN DKctr) done`).  Result s25: Q0(18),
        Q1(1365)=block-1 CTR, Q30(754) all bounded.  KEY: DKctr keeps Q30 so
        rev32 v1..v7 evaluate; folding each step keeps the increment ~754ch.
     -- AES bulk: ARM_STEPS (26--84) THEN DK1 ; (85--173) THEN DK1.  Q0,Q1 grow
        to ~219/2178 (towers).  Q30 now safely dropped (CTR setup done).
     -- GHASH tag: (174--184) THEN GCM_SIMD_SIMPLIFY_TAC THEN DK1b -> Q19~122ch.
     -- (185--254) THEN DK1b.
     -- ARM_VSTEPS [255] THEN RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL;
        INT_OF_NUM_EQ]) -> resolves the cmp x0,x5 / b.ge tail branch; PC jumps
        to pc+3768 (TAIL .L256_enc_tail @ 0xeb8).  State: Q0(391),Q1(2666),
        Q19(122).  (NB: with per-step folding the step->pc map shifts; the tail
        branch fires at step 255 here, not 263 as in coarse runs.)

   TAIL CASCADE — SOLVED (reaches more_than_1 GHASH multiply):
   - At the tail (the cmp x0,x5 / b.ge branch fires at step 255 -> pc+3768),
     step the tail's `sub x5,x4,x0` (~step 256-260) then set X5 = word 32 via
     RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
       `word_sub (word_add in_p (word 32)) in_p = word 32`]).  After that the
     cmp x5,#112/.../#16 b.gt cascade AUTO-RESOLVES (no special resolver needed;
     X5=word 32 makes ARM_CONV decide each branch by ground arithmetic).
   - Use DK1c = mk_discard [2;3;4;5;6;30] (keeps Q0,Q1,Q7,Q19) through the
     cascade so Q7 survives (the cascade's `mov v7,v1` routes block-1 keystream
     to Q7; verified Q7(2666) present at pc+4348).  Reaches more_than_1
     (pc+0x10f4=pc+4340) with Q9(467)=ct0, Q7=block-1 keystream, Q19/Q17/Q18
     zeroed accumulators, Q16=partial tag, Q22=H^2 htable load.

   GHASH MULTIPLY — IN PROGRESS (the algebraic core, next):
   - *** MUST abbreviate ct0 to an atom BEFORE the rev64+pmull (else the GHASH
     multiply blows Q8/Q27/etc to ~1M chars).  At pc+4348 (s310, after the
     block-0 st1, before rev64 v8,v9): ABBREV_TAC ct0 = <the Q9 tower>.  Then
     Q9 -> ct0 (18ch).  Same for ct1 when block-1's eor3 forms it inside
     more_than_1 (ldr q9,[x0]; eor3 v9,v9,v7).  Mirror the 1-block's ct
     abbreviation at s265.  (NB even with ct0 atom, rev64 v8,v9 expands it to a
     ~27k byte tree -> the GHASH pmull products are big but tractable, exactly
     like the 1-block; they get bridged at the end, NOT computed.)
   - more_than_1 (0x10f4-0x1134): block-0 GHASH: rev64 v8,v9; eor v8,v8,v16
     (feed tag); pmull2 v28 (hi), pmull v26 (lo) vs H^2=Q22; ins/eor/pmull2 v27
     (mid) vs the H^2 mid lane of Q21=[x6,#16]; accumulate into v17/v19/v18.
   - less_than_1 (0x1138-0x11d4): block-1 GHASH vs H (Q20=[x6,#0]) + accumulate
     into the SAME v17/v19/v18, then ONE Prop3 reduction (MODULO block), then
     ext+rev64 -> store xi_p.  Use ARM_VSTEPS_FOLD_TAC over this region like the
     1-block tail (fold to keep accumulators bounded over the ct0/ct1 atoms).
   - BRIDGE: assert read Q19 (pre-store) = the GHASH_POLYVAL_ACC_2 RHS
       prop3(pmul(brev xi XOR brev ct0, byteswap128 h2_key) XOR pmul(brev ct1, byteswap128 h))
     then REWRITE[GSYM GHASH_POLYVAL_ACC_2] to get
       ghash_polyval_acc (byteswap128 h) (brev xi) [brev ct0; brev ct1].
     (h2_key = polyval_dot(byteswap128 h)(byteswap128 h); check byteswap128 h2 =
      that, per the htable reconciliation already machine-checked above.)
   - spec postcond + ctr1: expose ctr1 as var (cleanest) vs inline (ct1's
     keystream input = the folded once-incremented counter).

   SESSION-2 REACHED: more_than_1 GHASH multiply, BOTH ciphertexts abbreviated.
   - ct0 abbreviated at pc+4348 (s310, before rev64 v8,v9): ABBREV_TAC
     ct0 = <Q9 block-0 tower = word_xor (word_xor plaintext0 (aes...ctr0)) v29-ish>.
   - block-0 GHASH multiply stepped with ARM_VSTEPS_FOLD_TAC (316--320): keeps
     the pmull products bounded (Q27~892, Q17~488, Q28~455 vs ~1M unfolded).
   - ct1 abbreviated at s320 (after more_than_1's ldr q9,[x0]; eor3 v9,v9,v7):
     ABBREV_TAC ct1 = <Q9 block-1 tower>.  IMPORTANT: ct1's keystream input is
     aes256_encrypt over the byte-shuffled ONCE-INCREMENTED counter:
       word_join(...)(word_add (word_join (subword ctr0 96,8)(...)) (word 1))...
     i.e. ctr1 = rev32(rev32(ctr0) + 1) at the lane level.  For the spec, expose
     `ctr1:int128` as a variable and either (a) add a precond pinning Q1's
     keystream to aes256_encrypt ctr1 keys, or (b) prove the byte-shuffle = ctr1
     once via a counter lemma.  ct1 atom now carries it opaquely through GHASH.
   - NEXT: finish more_than_1 (block-0 mid pmull vs Q21=[x6,#16] hi lane) +
     less_than_1 (block-1 GHASH vs H, accumulate, 1 Prop3 reduction), folding;
     DISCARD_OLDSTATE before the bridge; then the GHASH_POLYVAL_ACC_2 bridge.

   *** KEY (session 2, reached less_than_1 @ pc+0x1138): at less_than_1 entry
   read X1 = word 128 (NOT 256) — the cascade decremented bit_len by 128 for the
   one block more_than_1 processed.  So less_than_1 sees a FULL last block
   (x1=128), mask v0 = ALL-ONES, `and v9,v9,v0 = v9 = ct1`.  => less_than_1 for
   the 2-block is IDENTICAL to the proven full-block 1-block less_than_1
   (AESV8_GCM_8X_ENC_256_1BLOCK), EXCEPT the GHASH accumulators Q17/Q18/Q19/
   Q26/Q27/Q28 already hold block-0's contribution, so the single Prop3 reduction
   at the end folds BOTH blocks.  STRATEGY: replay the 1-block less_than_1
   stepping (mask collapse to all-ones, rev64 v8,v9, block-1 pmull vs H=Q20,
   accumulate, MODULO reduction, ext+rev64, store xi_p) — but the pre-reduction
   Q19 will be the 2-block aggregate.  Bridge it via GHASH_POLYVAL_ACC_2 instead
   of the 1-block's single GMULT_FULL_CORRECT_BA.
   State at s340 (pc+0x1174): Q20=H load, Q9=masked ct1, block-0 accumulators
   in Q17/18/19/26/27/28 (~500-900ch each, bounded), ct0/ct1 atoms.

   IMMEDIATE SUB-TASK (mask collapse on Q9, the dec/enc LE1BLOCK pattern):
   At s340 read Q9 = word_and (word_insert (word_insert (aese-tower...))) — the
   `and v9,v9,v0` mask re-expanded ct1's tower (the abbreviation didn't survive
   the AND because the AND operand was the underlying value).  For x1=128 the
   mask v0 is ALL-ONES, so this = ct1.  Re-assert read Q9 = ct1 like the
   full-block 1-block does (its step 325-326): after the AND, do
     FIRST_X_ASSUM(MP_TAC o SPEC `ct1` o MATCH_MP (MESON[] `read Q9 s = a ==>
       !a'. a = a' ==> read Q9 s = a'`)) THEN ANTS_TAC THENL
       [<prove word_and allones tower = ct1>; DISCH_TAC]
   The 1-block proves the ANTS with CONV_TAC WORD_BLAST (expanding the tower).
   For 2-block, ct1 is an atom = that tower, so the ANTS goal is
   `word_and <allones> <tower> = ct1` = (EXPAND_TAC "ct1" THEN identity);
   since mask is all-ones use a MASK-allones lemma or WORD_BLAST after
   EXPAND_TAC "ct1".  Verify the mask Q0 is actually all-ones for x1=128 first
   (the csel x13/x14 with bit_len 128: x1&127=0 -> mask top/bottom = 0xff..ff).
   THEN proceed exactly as the 1-block less_than_1: VSTEPS the store window,
   GHASH tail (rev64 v8,v9; pmull vs Q20=H; accumulate into the block-0-loaded
   v17/v19/v18; MODULO single reduction), bridge via GHASH_POLYVAL_ACC_2.

   *** SIMULATION COMPLETE (session 2 end) — reached pc+0x11d0 (rev64 v19, one
   step before the xi_p store st1 v19,[x3] @ 0x11d4; exit pc+0x11d8=pc+4568).
   The mask collapse on Q9 (all-ones, x1=128) was done via the 1-block trick
   (FIRST_X_ASSUM MP_TAC o SPEC ct1 ... ANTS [EXPAND_TAC "ct1" THEN WORD_BLAST]).
   Then ARM_VSTEPS_FOLD_TAC through the store window + block-1 GHASH multiply
   (vs Q20=H) + the single MODULO reduction (which folds BOTH blocks since the
   accumulators held block-0).  DISCARD_OLDSTATE_TAC between fold groups keeps it
   bounded.  Step numbering: mask collapse ~s340; multiply/reduce s341-363.

   ALL THAT REMAINS = THE GHASH BRIDGE (algebraic core) + close:
   - The reduced GHASH result is in Q19 just before the ext(0x11c8)+rev64(0x11d0).
     Assert read Q19 (pre-ext state, ~s361) = the 2-block aggregate.  Per
     GHASH_POLYVAL_ACC_2 with key K=byteswap128 h, a=brev xi, b=brev ct0,
     c=brev ct1:  ghash_polyval_acc K a [b;c] = polyval_reduce_prop3(
       word_xor (word_pmul (word_xor a b) (polyval_dot K K)) (word_pmul c K)).
     The assembly computed exactly this (block-0 vs H^2=polyval_dot K K from
     htbl+32, block-1 vs H=K from htbl+0, aggregated pre-reduction).  Bridge the
     byte-form Q19 to that RHS (reuse the 1-block bridge machinery PMUL_KARATSUBA
     /KARATSUBA_LIMBS/PMUL_W_64_128/ABBREV_INNER_PMULS/MERGE_PMUL_ATOMS/lane-fold,
     now over TWO products), then GSYM GHASH_POLYVAL_ACC_2 -> the list-of-2 form.
   - htable keys: byteswap128 h2 = polyval_dot K K (machine-checked above);
     byteswap128 h = K.  The mids: subword hk (0,64)=mid(K) [block1/H],
     subword hk (64,64)=mid(H^2) [block0] — confirm the exact lanes from the
     more_than_1 pmull2 v27 (uses Q21=[x6,#16] hi lane) vs less_than_1 (lo lane).
   - then ext+rev64 -> word_bytereverse(gval); store; ENSURES_FINAL_STATE; close
     (EXPAND ct0,ct1; the spec postcond GHASHes [brev ct0; brev ct1]).
   - SPEC still needs finalizing: expose ctr1 var + its precond (ct1 keystream).
   ------------------------------------------------------------------------- *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
needs "common/karatsuba_pmul.ml";;
needs "common/polyval_ghash.ml";;
(* Counter-mode spec layer: gcm_ctr_inc + GCM_CTR_INC_LANES (+ inc32 bridge and *)
(* the gcm_ctr_inc_iter iterator) now live in the shared utils file.            *)
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;
(* Recursive list-based CTR ciphertext spec (aes_ctr) + its 2-block reductions  *)
(* AES_CTR_2_EL / AES_CTR_2_MAP_BREV, used to state the out_p / GHASH postcond.  *)
needs "arm/proofs/utils/aes_ctr_spec.ml";;

(* The machine code + EXEC rule are shared with the 1-block proof; load that
   file so aesv8_gcm_8x_enc_256_mc / _EXEC and all helper lemmas are in scope.
   (We only ADD the 2-block theorem; we never edit the 1-block file.) *)
needs "arm/proofs/aesv8_gcm_8x_enc_256_1block.ml";;

(* -------------------------------------------------------------------------
   SPEC (draft).  bit_len = 256 (two whole blocks).  Entry pc+0x2c (the body,
   after the prologue arg-setup), exit pc+0x11d8 -- same entry/exit as the
   1-block body, but x1 = 256 and X9 = 32 so the cascade takes more_than_1
   then less_than_1.

   Plaintext: two blocks at in_p, in_p+16.  CTR blocks: ctr0 (block 0) and
   ctr1 (block 1); the front derives Q0=rev32-ctr for block 0 and Q1 for
   block 1 from Q30.  We follow the 1-block style and pass ctr0 as the block-0
   AES input; ctr1 is the block-1 AES input (the simulation fixes ctr1 in
   terms of ctr0 via the CTR increment -- TODO: confirm exact symbolic form
   and whether to expose ctr1 as a variable with a precond or derive it).

   htable preconditions: h = read htbl_p (= byteswap128 H), hk = packed mid at
   +16 ; ADD h2 = read (htbl_p+32) (= byteswap128 H^2) used by more_than_1.
   Relations needed for the bridge:
     subword hk (0,64) = mid(h)       [block-1 / H,  as in 1-block]
     subword hk (64,64) = mid(byteswap128 h2 ... )  [block-0 / H^2; TODO check lane]
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   SESSION 3 (2026-06-16): DIRECT C_ARGUMENTS entry (pc+0x18, NO wrapper) works.
   Prologue 0x18-0x28 (lsr x9; mov x16; mov x11; mov x5,#0xc2..; stp x5,xzr,[sp,64])
   steps inline as steps 1-5: establishes X9=word 32, X16=ivec_p, X11=key_p, and
   the Prop3 constant at [sp+64] -- no precondition needed for the constant (the
   prologue writes it).  Entry registers: X0=in_p,X1=word 256,X2=out_p,X3=xi_p,
   X4=ivec_p,X5=key_p,X6=htbl_p (the 7 C args), Q30=ctr0.  The (sp,80) stack
   disjointness in the precond covers the stp store (same as 1-block LE1BLOCK).
   Body front then runs with +5 step offset.  Reached the FINAL reduced GHASH
   result read Q19 s367 (pc+0x11cc, ~18433ch byte-form) -- the bridge LHS,
   analog of the 1-block s348.  Two htable-mid preconds added:
     subword hk (0,64) = mid(h)   [block1/H, less_than_1 pmull low lane]
     subword hk (64,64) = mid(h2) [block0/H^2, more_than_1 pmull2 high lane]
   ct1's keystream input = lane-shuffled once-incremented counter (captured;
   = aes256_encrypt over word_join(...)(word_add (top-lane) (word 1))...).
   REMAINING: the GHASH bridge -- assert read Q19 s367 =
     ghash_polyval_acc (byteswap128 h) (brev xi) [brev ct0; brev ct1]
   via GHASH_POLYVAL_ACC_2 + the 1-block Karatsuba/Prop3 machinery over TWO
   products (block0 vs polyval_dot K K = byteswap128 h2, block1 vs K=byteswap128 h);
   then ext+rev64, store, ENSURES_FINAL_STATE, close.  Then finalize the spec
   postcond + write the whole thing as one prove(...).
   ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* The AES-GCM counter increment (block-1's CTR input) + its lane-byte form    *)
(* now live in the shared utils file arm/proofs/utils/gcm_ctr_helpers.ml       *)
(* (needs'd above): gcm_ctr_inc, GCM_CTR_INC_LANES (used by the ctr1 fold), the *)
(* NIST inc32 bridge GCM_CTR_INC_INC32, and the gcm_ctr_inc_iter iterator.      *)
(* They were lifted byte-identically out of this file; nothing else changes.   *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Helper lemmas for the 2-product GHASH bridge (session 3).                 *)
(* ========================================================================= *)

(* word_join lane split: reduces a 128-bit word_join equality to two 64-bit   *)
(* lane equalities (so the final close is two small flat XOR identities).      *)
let JOIN_EQ_SPLIT = prove(
  `!(a:(64)word) (b:(64)word) (c:(64)word) (d:(64)word).
     ((word_join a b:(128)word) = word_join c d) <=> (a = c /\ b = d)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th ->
      MP_TAC(REWRITE_RULE[JOIN_SUBWORD_RULES]
        (BETA_RULE(AP_TERM `\x:(128)word. word_subword x (64,64):(64)word` th))) THEN
      MP_TAC(REWRITE_RULE[JOIN_SUBWORD_RULES]
        (BETA_RULE(AP_TERM `\x:(128)word. word_subword x (0,64):(64)word` th))) THEN
      MESON_TAC[]);
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* per-lane reversefields: word_reversefields 8 on a full int128 commutes with *)
(* the 64-bit lane projection (with a lane swap).                              *)
let RF8_SUBWORD = prove(
  `(!x:int128. word_subword (word_reversefields 8 x) (0,64):64 word =
               word_reversefields 8 (word_subword x (64,64):64 word)) /\
   (!x:int128. word_subword (word_reversefields 8 x) (64,64):64 word =
               word_reversefields 8 (word_subword x (0,64):64 word))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* subword lane extraction through word_zx / word_shl of the 256-bit Karatsuba *)
(* assembly (for a 64-bit source).                                             *)
let SUBW_ZX_256 = prove(
  `(!x:64 word. word_subword (word_zx x:256 word) (0,64):64 word = x) /\
   (!x:64 word. word_subword (word_zx x:256 word) (64,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_zx x:256 word) (128,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_zx x:256 word) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL64_256 = prove(
  `(!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (0,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (64,64):64 word = x) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (128,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL128_256 = prove(
  `(!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (0,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (64,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (128,64):64 word = x) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
(* and for a 128-bit source (the qq atoms). *)
let SUBW_ZX128_256 = prove(
  `(!x:128 word. word_subword (word_zx x:256 word) (0,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_zx x:256 word) (64,64):64 word = word_subword x (64,64)) /\
   (!x:128 word. word_subword (word_zx x:256 word) (128,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_zx x:256 word) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL64_128_256 = prove(
  `(!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (0,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (64,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (128,64):64 word = word_subword x (64,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL128_128_256 = prove(
  `(!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (0,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (64,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (128,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (192,64):64 word = word_subword x (64,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_XOR_256 = prove(
  `!x y:256 word. !lo. word_subword (word_xor x y) (lo,64):64 word =
     word_xor (word_subword x (lo,64)) (word_subword y (lo,64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR]);;

(* Collapse a 64-bit lane of subword(subword(join a a)(64,128)) -- the duplicated *)
(* mid-half the wv W-reduction operand produces -- to a plain lane of a.  Lets the *)
(* wv operand equality close as a flat WORD_BITWISE identity instead of a ~90s     *)
(* WORD_BLAST (see FAST_OPERAND_TAC / the merge speedup note below).               *)
let SUBSUB_JOIN_DUP = prove(
  `(!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (0,64) :64 word
                 = word_subword a (64,64)) /\
   (!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (64,64) :64 word
                 = word_subword a (0,64))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Abbreviate EVERY `word_subword (a:int128) (lo,64)` subterm occurring in the goal
   (a any term, typically a qqN atom or its lane) to a fresh 64-bit var.  After this
   no `word_subword`-over-int128 survives, so the residual is a flat word_xor
   identity over 64-bit vars that WORD_BITWISE_TAC closes.  (Used by both
   FAST_OPERAND_TAC for the merge and FINISH_2BLK_TAC for the final close.) *)
let ABBREV_ALL_SUBWORDS_TAC : tactic = fun (asl,w) ->
  let is_sw64 t = try fst(dest_const(rator(rator t)))="word_subword" &&
                      type_of t = `:(64)word` &&
                      type_of (rand(rator t)) = `:int128` with _->false in
  let sws = setify(find_terms is_sw64 w) in
  let used = ref 0 in
  let tac = itlist (fun t acc ->
      let n = !used in used := n+1;
      ABBREV_TAC (mk_eq(mk_var("zw"^string_of_int n,`:64 word`), t)) THEN acc)
    sws ALL_TAC in
  tac (asl,w);;

(* Fast closer for a merge's operand-equality subgoal.  Both operands are the SAME *)
(* GF product's structural lane form (word_zx/word_shl/word_subword over the qq    *)
(* atoms, NO pmul), so collapse the 256-bit Karatsuba lanes to 64-bit (the SUBW_*  *)
(* lemmas + SUBSUB_JOIN_DUP), abbreviate the residual atom-lanes, and close by      *)
(* WORD_BITWISE_TAC (<1s).  This replaces a ~90s WORD_BLAST per W-reduction operand. *)
let FAST_OPERAND_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; SUBSUB_JOIN_DUP; WORD_SUBWORD_SUBWORD;
              JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  WORD_BITWISE_TAC;;

(* Targeted pmul-atom merge for the 2-block bridge.  The post-Karatsuba goal   *)
(* has matched LHS/RHS word_pmul atoms (same GF(2^128) product in different    *)
(* arg-order / lane nesting).  The generic all-pairs MERGE_PMUL_ATOMS_TAC is   *)
(* O(pairs) WORD_BLASTs and too slow here (~30 min) because each FAILED         *)
(* PMUL_CONG WORD_BLAST on the big W-reduction operands costs ~90s.  Instead we *)
(* pick exactly ONE structurally-determined pair per call and blast only it.    *)
(*                                                                              *)
(* Two atom classes, each paired without trial-blasting non-matches:            *)
(*  (a) PRODUCT atoms (operand 2 = a key lane: word_subword h/h2, or an XOR of  *)
(*      two such): the LHS (assembly) and RHS (spec) forms of the same GF       *)
(*      product agree on the set of non-key free vars of operand 1, on the set  *)
(*      of free vars of operand 2, and on operand 2's subword lane index.       *)
(*      Key vars k0..k14 are excluded from operand 1's signature because the    *)
(*      assembly's `ins` leaves a spurious k13 in one mid-term form.            *)
(*  (b) W-REDUCTION atoms (operand 2 = the same word-CONSTANT 0xc200...): the   *)
(*      two forms (wa round, then wv round) differ structurally in operand 1    *)
(*      but multiply the same constant, so they are paired by `operand 2 is the *)
(*      identical word-constant`.                                               *)
(* On success the merge equality is propagated into the hypotheses (RULE_ASSUM) *)
(* so later atom DEFINITIONS that reference the merged-away atom are updated to  *)
(* the canonical one -- essential for the 2-round W-reduction pmuls (the wv      *)
(* atom's def references the wa atom we merged the round before).  Fails         *)
(* (failwith) if no structurally-matched pair remains.                          *)
let MERGE_ONE_2BLK_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  (* only consider atoms actually occurring in the goal conclusion *)
  let goalvars = setify(map (fun t->fst(dest_var t))
    (find_terms (fun t->is_var t && type_of t=`:int128` &&
      (let n=fst(dest_var t) in String.length n>=2 && String.sub n 0 2="qq")) w)) in
  let defs = filter (fun (_,th)->let c=concl th in is_eq c && is_var(rhs c) &&
    is_pmul(lhs c) && mem (fst(dest_var(rhs c))) goalvars) asl in
  let fvnames t = sort (<) (filter (fun n -> not(is_keyvar n))
                              (map (fun v->fst(dest_var v)) (frees t))) in
  let lane_tag op2 =
    if is_comb op2 && is_comb(rator op2) &&
       (try fst(dest_const(rator(rator op2)))="word_subword" with _->false)
    then string_of_term(rand op2) else "X" in
  let info th =
    let p = lhs(concl th) in
    let (_,args) = strip_comb p in
    let op1 = el 0 args and op2 = el 1 args in
    (rhs(concl th), op2, (fvnames op1, fvnames op2, lane_tag op2)) in
  let items = map (fun (_,th)-> info th) defs in
  let rec find_pair = function
    | [] -> None
    | (v,op2,sg)::rest ->
        let cand =
          if is_wordconst op2
          then filter (fun (v2,op2b,_)-> v2<>v && is_wordconst op2b && op2b=op2) rest
          else filter (fun (v2,op2b,sg2)-> v2<>v && not(is_wordconst op2b) && sg2=sg) rest in
        (match cand with (v2,_,_)::_ -> Some(v,v2) | [] -> find_pair rest) in
  (match find_pair items with
  | None -> (fun _ -> failwith "MERGE_ONE_2BLK_TAC: nothing to merge")
  | Some(v1,v2) ->
      (* Close each operand equality with FAST_OPERAND_TAC (flatten lanes +
         WORD_BITWISE, <1s) and only fall back to WORD_BLAST if that doesn't apply.
         The W-reduction (wv) operand is ~90s under WORD_BLAST but ~1s under the
         flatten route -- this is the bridge's dominant cost, see FAST_OPERAND_TAC. *)
      let close_op = FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST in
      SUBGOAL_THEN (mk_eq(v1,v2))
        (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
       THENL [EXPAND_TAC(fst(dest_var v1)) THEN EXPAND_TAC(fst(dest_var v2)) THEN
              ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op)
               ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op));
              ALL_TAC]) (asl,w);;

(* Repeat the single-merge to a fixpoint. *)
let MERGE_2BLK_TAC : tactic = REPEAT MERGE_ONE_2BLK_TAC;;

(* Discard helpers for the front (keep block-0/1 keystreams + GHASH tag). *)
let mk_discard2 keepset =
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let s = string_of_term (concl th) in
    String.length s > 500 &&
    (let has sub = let sl=String.length s and bl=String.length sub in
      let rec ck j = if j>sl-bl then false else if String.sub s j bl=sub then true else ck(j+1) in ck 0 in
     List.exists (fun n -> has ("read Q"^string_of_int n^" ")) keepset));;

(* Tactic: abbreviate the current read Q9 (a ciphertext tower) to the given atom var. *)
let ABBREV_Q9_TAC vname state =
  fun (asl,w) ->
    let pat = "read Q9 "^state^" =" in
    let th = find (fun (_,t)->let s=string_of_term(concl t) in
      String.length s >= String.length pat && String.sub s 0 (String.length pat) = pat) asl in
    ABBREV_TAC (mk_eq(mk_var(vname,`:int128`), rhs(concl(snd th)))) (asl,w);;

(* The flatten-and-blast close for the 2-product reduction structural identity:
   collapse the 256-bit Karatsuba assembly to 64-bit lanes, abbreviate atom halves,
   split the word_join equality lane-wise, finish each lane with WORD_BITWISE_TAC.
   (ABBREV_ALL_SUBWORDS_TAC is defined above, shared with FAST_OPERAND_TAC.) *)
let FINISH_2BLK_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_SUBWORD_SUBWORD] THEN
  (* expose all lanes via QQ0SPLIT + JOINMID, THEN abbreviate every residual
     word_subword-over-int128 so the goal is flat 64-bit before WORD_BITWISE *)
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN
  REPEAT CONJ_TAC THEN WORD_BITWISE_TAC;;

(* ========================================================================= *)
(* The 2-block theorem.  Direct C_ARGUMENTS entry at pc+0x18 (NO wrapper):    *)
(* the 5 prologue setup instructions (0x18..0x28) are stepped inline.          *)
(* bit_len = 256, two whole blocks; exit pc+0x11d8 (epilogue not simulated).   *)
(* ========================================================================= *)

(* The spec variable ctr1 is the block-1 AES counter: the lane-level
   once-incremented ctr0 (rev32 of the byte-shuffled top 32-bit lane + 1), as
   produced by the front's CTR setup; pinned by the precond below. *)

let AESV8_GCM_8X_ENC_256_2BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    plaintext0 plaintext1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4600) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4600) (out_p:int64, 32) /\
    nonoverlapping (word pc, 4600) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (xi_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 32) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 240) /\
    nonoverlapping (out_p, 32) (htbl_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = plaintext0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = plaintext1 /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 0x11d8) /\
          read (memory :> bytes128 out_p) s =
          EL 0 (aes_ctr ctr0 [plaintext0;plaintext1]
                 [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          EL 1 (aes_ctr ctr0 [plaintext0;plaintext1]
                 [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              (MAP word_bytereverse
                (aes_ctr ctr0 [plaintext0;plaintext1]
                  [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* The out_p / GHASH postcond is stated via the shared list spec aes_ctr:
       out_p block i = EL i (aes_ctr ctr0 [pt0;pt1] keys)
       GHASH input    = MAP word_bytereverse (aes_ctr ctr0 [pt0;pt1] keys).
     Reduce those to the concrete per-block ciphertext forms (block 0 uses
     ctr0, block 1 uses gcm_ctr_inc ctr0) via the proven reductions, then
     re-introduce the spec atom ctr1 = gcm_ctr_inc ctr0 by abbreviation (flipped
     to lhs = ctr1) so the rest of the proof body runs verbatim as before. *)
  REWRITE_TAC[AES_CTR_2_EL; AES_CTR_2_MAP_BREV] THEN
  ABBREV_TAC `ctr1:int128 = gcm_ctr_inc ctr0` THEN
  FIRST_X_ASSUM(fun th ->
    if (try rhs(concl th) = `ctr1:int128` with _ -> false)
    then ASSUME_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  (* prologue 0x18..0x28 (5 instrs): X9=32, X16, X11, Prop3 const at [sp+64] *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (1--5) THEN
  (* CTR setup (6..30): step 1-at-a-time, fold each, keep Q0,Q1,Q30 (DKctr). *)
  EVERY (map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (i--i) THEN
              GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [2;3;4;5;6;7]) (6--30)) THEN
  (* AES bulk: keep Q0,Q1 (block-0/1 keystreams), drop Q2-Q7,Q30. *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (31--89) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (90--178) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  (* GHASH tag load + fold (keeps Q19 the byteswapped xi tag). *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (179--189) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (190--259) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  (* cmp x0,x5 / b.ge tail: in_p - in_p = 0 -> branch to .tail (pc+3768). *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [260] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  (* tail entry: sub x5,x4,x0; set X5 = word 32; cascade auto-resolves; keep Q7. *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (261--265) THEN mk_discard2 [2;3;4;5;6;30] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word 32)) in_p = word 32:int64`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (266--315) THEN mk_discard2 [2;3;4;5;6;30] THEN
  (* abbreviate ct0 (block-0 ciphertext) to the SPEC FORM word_xor plaintext0
     (aes256_encrypt ctr0 keys) BEFORE the rev64+pmull, so the out_p postcond
     closes by ASM_REWRITE (1-block s265 MESON-SPEC idiom). *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor plaintext0 (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]; DISCH_TAC] THEN
  ABBREV_TAC
    `ct0:int128 = word_xor plaintext0 (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (316--325) THEN
  (* abbreviate ct1 (block-1 ciphertext) to its SPEC FORM word_xor plaintext1
     (aes256_encrypt ctr1 keys) -- same MESON-SPEC idiom as ct0.  The ANTS
     rewrites the spec var ctr1 to gcm_ctr_inc ctr0 (its precond) and then to
     the explicit lane-byte form (GCM_CTR_INC_LANES) the Q9 readback carries,
     then expands aes256_encrypt to the raw aese/aesmc tower. *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor plaintext1 (aes256_encrypt (ctr1:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try lhs(concl th) = `ctr1:int128` with _ -> false)
      then GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th] else NO_TAC) THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]; DISCH_TAC] THEN
  ABBREV_TAC
    `ct1:int128 = word_xor plaintext1 (aes256_encrypt (ctr1:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (326--333) THEN
  DISCARD_OLDSTATE_TAC "s333" THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (334--345) THEN
  (* less_than_1 sees X1=128 -> mask all-ones; re-assert Q9 = ct1. *)
  FIRST_X_ASSUM(MP_TAC o SPEC `ct1:int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL [EXPAND_TAC "ct1" THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (346--353) THEN
  (* capture the block-1 ciphertext store (st1 v9,[x2] @ 0x1188, x2=out_p+16)
     BEFORE discarding the store state; mask v0 is all-ones (x1=128) so the
     stored masked/bif value is exactly ct1.  Carry it to the final state. *)
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s353:armstate) = ct1`
    ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s353" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (354--367) THEN
  DISCARD_OLDSTATE_TAC "s367" THEN
  (* === GHASH bridge: read Q19 s367 = ghash_polyval_acc (byteswap128 h)(brev xi)[brev ct0;brev ct1] *)
  SUBGOAL_THEN
    `read Q19 (s367:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse ct0; word_bytereverse ct1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s367`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s367` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
   FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `byteswap128 h2` with _ -> false)
     then GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th] else NO_TAC) THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [polyval_reduce_prop3] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
     [REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
   REWRITE_TAC[byteswap128] THEN
   REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_LIMBS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   REWRITE_TAC[WORD_XOR_0; SUBWORD0_LEMMAS] THEN REWRITE_TAC[WORD_XOR_0] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   FINISH_2BLK_TAC;
   ALL_TAC] THEN
  (* === ext+rev64 (368-369): Q19 -> word_bytereverse gval; store (370). === *)
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse ct0; word_bytereverse ct1]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (368--369) THEN
  SUBGOAL_THEN `read Q19 (s369:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s369`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s369` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [370] THEN
  (* === close ===
     The postcondition has four conjuncts: out_p block-0 ciphertext, out_p
     block-1 ciphertext, xi_p GHASH tag, and the MAYCHANGE frame.  After
     ENSURES_FINAL_STATE_TAC + ASM_REWRITE_TAC the block-1 (= ct1 via its store
     readback) and xi_p (= word_bytereverse gval, with gval = the spec GHASH over
     brev ct0/ct1, and ct0/ct1 now in spec form) goals close by ASM; only the
     block-0 goal needs the ct0 spec-form expansion (its store predates the ct0
     abbreviation, so the readback is the RAW aese/aesmc tower) and the MAYCHANGE
     frame needs MONOTONE_MAYCHANGE_TAC. *)
  ENSURES_FINAL_STATE_TAC THEN
  (* Fold `ctr1 = gcm_ctr_inc ctr0` UNIFORMLY into the goal AND the ct0/ct1
     spec-form def hypotheses, so ctr1 is eliminated consistently everywhere.
     (Discarding the precond is wrong -- the postcond's block-1 clause carries
     gcm_ctr_inc ctr0 in the final state, so the ct1-def must too for them to
     match; just unfolding the goal but not the def hypotheses leaves a residual.) *)
  FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `ctr1:int128` with _ -> false)
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC) THEN
  (* block-1 (= ct1 via its store readback) and xi_p (= word_bytereverse gval,
     gval = the spec GHASH over brev ct0/ct1) now match ct1's spec-form def under
     ASM_REWRITE (both sides in terms of gcm_ctr_inc ctr0). *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  (* the only remaining goal is out_p block-0: <raw aese/aesmc tower> = ct0
     (the block-0 store predates the ct0 abbreviation).  Rewrite ct0 to its
     spec form (GSYM the ct0 def) and expand aes256_encrypt to the same tower. *)
  TRY(FIRST_X_ASSUM(fun th ->
        if (try rhs(concl th) = `ct0:int128` with _ -> false)
        then GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [SYM th] else NO_TAC) THEN
      ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]));;
