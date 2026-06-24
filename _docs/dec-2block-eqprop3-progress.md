# dec 2-block EQ_PROP3 rewire — session progress

## State
- Branch aes-gcm-nblock-tail. File arm/proofs/aesv8_gcm_8x_dec_256_2block.ml
- Added `needs "common/ghash_nblock_karatsuba.ml"` (DONE, in file).
- Backup bck0001 made (pre-edit).
- HOL session: deps loaded (1block ~528s, layer, gcm_ctr_helpers, aes_ctr_spec).
  Front driven to bridge state s370 via `e(...)` (interactive goalstack), MASK_COLLAPSE done.
  Defined in session: mk_discard2, MASK_COLLAPSE_CPH1_TAC, BYTESWAP128_INVOLUTION, unfold_tower.

## Genuine `read Q19 s370` pmul atoms (block1=cph1 htw=h ; block0=xor(brev xi)(brev cph0) htw=h2)
Extracted op2 (key lane) of the 6 non-reduction pmuls:
  PMUL0 op2 = subword h 0      (block1 pl)
  PMUL1 op2 = subword h 64     (block1 ph)
  PMUL3 op2 = subword h2 0     (block0 pl)
  PMUL4 op2 = subword h2 64    (block0 ph)
  PMUL5 op2 = word_xor(subword h 0)(subword h 64)   = karatsuba_mid h  (block1 pm)
  PMUL7 op2 = word_xor(subword h2 0)(subword h2 64)  = karatsuba_mid h2 (block0 pm)
Genuine block-input forms (op1) are rev64 lane forms:
  block1 input = subword(join (rf8 cph1)(rf8 cph1))(64,128) = lane_swap(rf8 cph1)
  block0 input = subword(join (rf8 cph0)(rf8 cph0))(64,128) xor'd with brev xi lane form

## KEY RECONCILIATION FACTS (verified)
- subword(join a a)(64,128) = word_join(subword a 0)(subword a 64) = lane_swap(a)  [WORD_BLAST]
- karatsuba_mid h = word_xor(subword h 0)(subword h 64); karatsuba_mid(byteswap128 h)=karatsuba_mid h
- BYTESWAP128_SUBWORD_LO: subword(byteswap128 h)0 = subword h 64 ; HI: subword(byteswap128 h)64 = subword h 0
- single packed hk: subword hk 0 = mid h (asm23 RHS); subword hk 64 = mid h2 (asm24 RHS)
  => block0 mid available via subword(byteswap128 hk)0 = subword hk 64 = mid h2

## SPIKE recipe (worked at N=2 in _spike/time_ghash_closure.ml) — INST:
  in0 = word_xor(brev xi)(brev cph0), in1 = brev cph1 ; htw0=h2, htw1=h ; quad 4th elt block0=byteswap128 h2, block1=byteswap128 h
  but spike used SEPARATE hk0=hk2, hk1=hk. We have ONE packed hk.

## PLAN for bridge close (replacing ABBREV_INNER_PMULS+MERGE_2BLK x3+FINISH_2BLK):
1. SUBGOAL: read Q19 s370 = word_reversefields 8 (ghash_Nblock_karatsuba [TRIPLES])
   TRIPLES = [(word_xor(brev xi)(brev cph0), h2, byteswap128 hk); (brev cph1, h, hk)]
   prove by: rewrite read Q19 hyp; REWRITE[unfold_tower TRIPLES backwards i.e. tower_inst]
   + WORD_REVERSEFIELDS_REVERSEFIELDS + lane normalization + CONV_TAC WORD_BLAST/WORD_RULE.
   *** OPEN QUESTION: does genuine == spike raw exactly? lane-swap suggests genuine PMUL0
       matches spike's ph-block1 not pl. Need empirical WORD_BLAST test; if fails, adjust
       input lane arrangement (maybe inputs are lane_swap(brev cph) = rev64 form directly,
       with htw = byteswap128 h, h_quad = h).
2. MP_TAC(SPEC [quads] GHASH_NBLOCK_KARATSUBA_EQ_PROP3); REWRITE[kara_quad_ok;project_triples;
   kara_quad_pmul; WORD_XOR_0_LEFT]; ANTS [BYTESWAP128_INVOLUTION; ASM_REWRITE karatsuba_mid;
   BYTESWAP128_SUBWORD_LO/HI; WORD_RULE]; DISCH SUBST1.
3. REWRITE[WORD_REVERSEFIELDS_REVERSEFIELDS; GHASH_POLYVAL_ACC_2]; ASM_REWRITE.

## NEXT: test the SUBGOAL equality empirically (the read Q19 = reversefields(Nblock TRIPLES)).

## UPDATE — analysis after first probe (front state lost via g(), must rebuild)
- Genuine block inputs (op1 of ph-pmuls), captured into refs in0_genuine/in1_genuine:
  in1 = word_xor(word 0)(subword(join(rf8 cph1)(rf8 cph1))(64,128))
  in0 = word_xor(subword(join(join(rf8 sub xi0)(rf8 sub xi64))(join...))(64,128))(subword(join(rf8 cph0)(rf8 cph0))(64,128))
- triples_genuine = [(in0,h2,byteswap128 hk);(in1,h,hk)] built ok (packed hk: block0 mid via subword(byteswap128 hk)0 = subword hk 64 = mid h2; block1 mid via subword hk 0 = mid h).
- unfold_tower triples_genuine: pm-block0 uses subword(byteswap128 hk)0; pm-block1 uses subword hk 0.
  REWRITE[BYTESWAP128_SUBWORD_LO/HI] + ASM(asm23/asm24) folds those to xor-of-h/h2-lanes ✓.
- CORRECT SUBGOAL shape = read Q19 s370 = word_reversefields 8 (ghash_Nblock_karatsuba triples_genuine)
  (NOT bare ghash_Nblock; the s370 register is the polyval digest = ghash_polyval_acc, and
   ghash_Nblock = reversefields(polyval_reduce_prop3 ...), so digest = reversefields(ghash_Nblock)).
- OPEN: does genuine Q19 (= word_xor(word_subword(join..)(64,128))(..)) match
  word_reversefields 8 (unfold) after WORD_REVERSEFIELDS_REVERSEFIELDS cancel? Spike's raw was
  SYNTHETIC (=unfold), so spike closed with no blast. Our genuine is a real sim register; may
  need a structural bridge. MUST TEST on real bridge goal with genuine Q19 in context.

## REBUILD PLAN (next eval, ~500s front):
  re-run set_goal + front1+front2+front3 via e(...), capturing genuine Q19 into ref `gq19`.
  THEN test close strategies on SUBGOAL_THEN (read Q19 s370 = reversefields(ghash_Nblock triples)).
  Strategy A: rewrite genuine Q19; REWRITE[tower_genuine]; WORD_REVERSEFIELDS_REVERSEFIELDS;
              midfold (BYTESWAP128_SUBWORD_LO/HI + ASM); then equality should be lane-level WORD_RULE.

## UPDATE 2 — key finding (front rebuilt to bridge, refs captured)
Captured into session refs: gq19 (genuine read Q19 s370 RHS), in0_genuine/in1_genuine,
mid0_input/mid1_input. Proved MID0_EQ, MID1_EQ (genuine mid-pmul input lane == word_xor of
in-lanes, WORD_BLAST <1s each). Built triples_genuine=[(in0,h2,byteswap128 hk);(in1,h,hk)],
tower_genuine=unfold_tower(triples_genuine), rhs_rev=reversefields(ghash_Nblock triples),
rhs_nocancel=ghash_Nblock triples.

THE PROBLEM: genuine Q19 (simulator register) has word_reversefields 8 DISTRIBUTED into the
word_join/word_xor lane structure + word_insert junk in mid inputs (e.g. word_insert k13).
The clean tower (ghash_Nblock triples) = word_reversefields 8 (word_join g f) with reduce
SYMBOLIC over (pl,ph,pm). They are EQUAL as 128-bit words but NOT syntactically:
  - first divergence at top: genuine = word_xor(...), tower(after rf-cancel) = word_join(...)
  - genuine reduce is FULLY EVALUATED by sim; tower reduce is symbolic.
WORD_BLAST can't bridge directly (embedded word_pmul atoms; full 256/128-bit blast too slow/hangs).

The spike's raw2 was SYNTHETIC (unfold_tower output) so it matched trivially. Our genuine
register is the real sim form — needs normalization first (this is what OLD MERGE/FINISH did).

## CANDIDATE NEXT STRATEGIES (untested):
A. SUBGOAL gq19 = reversefields(ghash_Nblock triples); REWRITE[MID0_EQ;MID1_EQ;tower_genuine;
   WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ABBREV_INNER_PMULS_TAC (1block helper, in scope) THEN
   CONV_TAC WORD_BLAST.  (abbreviate ALL pmul atoms incl reduce wa/wv so residual is rf/join/
   subword/insert/xor only -> blastable). MUST abbreviate innermost-first & unify both sides.
B. Investigate exact reversefields relationship: is gq19 = reversefields(word_join g f) with
   g,f the reduce lanes? Then gq19 = reversefields(ghash_Nblock... no). Determine empirically
   via small targeted WORD_BLAST after abbreviating the 6 block pmuls.
C. Fallback: keep MERGE/FINISH (the ~73s route) — already proven. EQ_PROP3 adoption deferred.

## ABBREV pitfall: naive itlist ABBREV_TAC over nested pmuls fails (outer term changes after
   inner abbreviated). Need smallest-first OR REPEAT find-smallest-abbrev. ABBREV_INNER_PMULS_TAC
   from 1block file likely handles this — CHECK ITS DEF before reinventing.

## UPDATE 3 — CRITICAL: abbreviation works, but residual needs lane-flatten (defeats purpose?)
After REWRITE[MID0_EQ;MID1_EQ;tower_genuine;WORD_REVERSEFIELDS_REVERSEFIELDS;BYTESWAP_LO/HI]
+ ASM_REWRITE + ABBREV_INNER_PMULS_TAC x3: ALL pmuls gone, goal=1329 chars, NO reversefields.
BUT residual is a 128-bit lane identity over qq0..qq14 (128-bit vars):
  LHS = word_xor(word_subword(word_join G G)(64,128))(F')   [genuine, reversefields distributed]
  RHS = word_join(...lanes...)(...lanes...)                  [tower karatsuba_reduce_shared g/f]
WORD_BLAST HANGS (15 x 128-bit vars -> SAT blowup). This is the SAME lane-flatten the OLD
FINISH_2BLK_TAC did (JOIN_EQ_SPLIT + ABBREV_ALL_SUBWORDS + WORD_BITWISE). 

=> My subgoal shape is WRONG. The genuine Q19 register has the outer reversefields of
karatsuba_reduce_shared DISTRIBUTED by the simulator into word_xor(subword(join..)..)... 
The spike's raw2 was SYNTHETIC (= the unfold) so REFL closed it. Ours is a real register.

INSIGHT: the residual lane-identity IS the reversefields(word_join g f) vs the distributed
form — i.e. exactly WORD_REVERSEFIELDS over a join. Need a CLEAN reversefields-distribution
lemma, NOT bit-blast. The two sides only differ by how word_reversefields 8 (word_join g f)
is written. 

## RECOMMENDED NEXT (pick one):
1. BEST: find/prove a lemma  word_reversefields 8 (word_join (g:64word) f) = 
   word_xor (word_subword (word_join ...)(64,128)) (...)  OR show the genuine gq19 top-level
   IS word_reversefields 8 (word_join G F) modulo a SMALL 64-bit-lane WORD_BLAST per lane.
   Then split into 2 lanes (JOIN_EQ_SPLIT) and blast each 64-bit lane (FAST, like FINISH_2BLK
   but only on the OUTPUT join, not the full Karatsuba tower) -> ~1-2s.
2. The qqN are 128-bit but only their (0,64)/(64,64) subwords appear. ABBREV those subwords
   to 64-bit vars (ABBREV_ALL_SUBWORDS_TAC from 2block file) THEN JOIN_EQ_SPLIT THEN WORD_BITWISE.
   This is the FINISH_2BLK tail — fast (<2s) because operands already abbreviated. 
   *** This still uses EQ_PROP3 for the HARD part (Karatsuba->polyval), only the cheap output
       join-reversefields needs the 64-bit flatten. Net: still way faster than old ~73s. ***

## So the winning close (TO TEST):
SUBGOAL gq19 = reversefields(ghash_Nblock triples):
  REWRITE[MID0_EQ;MID1_EQ;tower_genuine;WORD_REVERSEFIELDS_REVERSEFIELDS;BYTESWAP_LO/HI];
  ASM_REWRITE; ABBREV_INNER_PMULS x3; 
  then ABBREV_ALL_SUBWORDS_TAC (64-bit) ; REWRITE[JOIN_EQ_SPLIT? or JOINMID]; WORD_BITWISE_TAC.
Then: MP_TAC EQ_PROP3 [quads]; ANTS via kara_quad_ok (BYTESWAP_INVOLUTION+karatsuba_mid+
  BYTESWAP_SUBWORD_LO/HI+WORD_RULE); REWRITE[GHASH_POLYVAL_ACC_2] -> ghash_polyval_acc form.

## UPDATE 4 — lane-flatten close ALMOST works but WORD_BITWISE fails on final 64-bit lanes
Verified sequence on residual (gq19 = reversefields(ghash_Nblock triples) under asm23/24):
  STRIP_TAC; REWRITE[MID0_EQ;MID1_EQ;tower_genuine;WORD_REVERSEFIELDS_REVERSEFIELDS;
    BYTESWAP128_SUBWORD_LO/HI]; ASM_REWRITE;
  ABBREV_INNER_PMULS_TAC x3  -> all 15 pmuls -> qq0..qq14 (in hyps), conclusion pmul-free, 128-bit.
  GEN_REWRITE_TAC I [WORD_EQ_LANES_128]  (new lemma: a=b <=> lane0=lane0 /\ lane1=lane1, via QQ0SPLIT)
  REWRITE[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR]  -> 2 conjuncts, sz3362
  ABBREV_ALL_SUBWORDS_TAC  -> 2 subwords left, sz1453
  CONJ_TAC THEN WORD_BITWISE_TAC  -> *** FAILS *** "WORD_BITWISE_RULE ... cannot solve"  (16s)
=> Either (a) WORD_BITWISE genuinely can't (real lane mismatch => triples wrong?), or
   (b) the 2 leftover word_subword qqN atoms confuse it, or
   (c) ABBREV_ALL_SUBWORDS named-clash: 2nd call "variable already used" (zw reused) — so some
       subwords stayed un-abbreviated and WORD_BITWISE saw mixed zw/word_subword qqN forms.
MIDS CONFIRMED MATCH (block0 hk-field = byteswap128 hk: subword(bsw hk)0=subword hk 64=mid h2 ✓;
  block1 hk-field = hk: subword hk 0 = mid h ✓). So triples should be right.

## DIAGNOSIS TODO next session:
- Re-run to abbrev state; do ABBREV_ALL_SUBWORDS with UNIQUE fresh names (fix tac to use a
  global counter / variant against existing zw). Then both lanes should be flat XOR over the
  SAME atom set; WORD_BITWISE_TAC closes each in <1s. Likely the whole failure is the name clash
  leaving `word_subword qqN` un-unified between the two conjuncts/sides.
- Helper to add to file: ABBREV_ALL_SUBWORDS_TAC must `variant` names against frees in goal+asm.
- If still fails: test each lane equality in isolation with WORD_BLAST (bounded) to confirm truth.

## BUILDING BLOCKS CONFIRMED WORKING (all in session, ready to embed in file):
  BYTESWAP128_INVOLUTION, unfold_tower, JOIN_EQ_SPLIT, ABBREV_ALL_SUBWORDS_TAC (needs name fix),
  WORD_EQ_LANES_128, MID0_EQ/MID1_EQ (but these are goal-specific; generalize to a tactic that
  finds & rewrites the word_insert mid forms to word_xor-of-lanes via WORD_BLAST per atom).

## AFTER bridge eq proved: MP_TAC EQ_PROP3 on quads
  [(in0,h2,byteswap128 hk, byteswap128 h2);(in1,h,hk, byteswap128 h)]
  REWRITE[kara_quad_ok;project_triples;kara_quad_pmul;WORD_XOR_0_LEFT];
  ANTS: REWRITE[BYTESWAP128_INVOLUTION]; ASM_REWRITE[karatsuba_mid;BYTESWAP128_SUBWORD_LO/HI]; WORD_RULE
   (NOTE: kara_quad_ok needs h_tw = byteswap128 h_true AND subword hk_field 0 = karatsuba_mid h_true.
    block0: h_tw=h2, hk_field=byteswap128 hk, h_true=byteswap128 h2 => need h2 = byteswap128(bsw h2) ok
            and subword(bsw hk)0 = karatsuba_mid(bsw h2). subword(bsw hk)0=subword hk 64=xor h2 lanes;
            karatsuba_mid(bsw h2)=xor(subword(bsw h2)0)(subword(bsw h2)64)=xor(sub h2 64)(sub h2 0)=same ✓
    block1: h_tw=h, hk_field=hk, h_true=byteswap128 h => subword hk 0=xor h lanes; 
            karatsuba_mid(bsw h)=xor(sub h 64)(sub h 0)=same ✓ ). 
  THEN result = reversefields(prop3(kara_quad_pmul quads 0)). kara_quad_pmul = XOR of 
  word_pmul in_k (byteswap128 h_k^true). Need this = the GHASH_POLYVAL_ACC_2 prop3 arg.
  in0=word_xor(brev xi)(brev cph0) wait NO -- in0 here is the GENUINE rev64 form, = brev-ish.
  *** Must connect genuine in0/in1 (rev64 lane forms) to brev xi/cph via WORD_BYTEREVERSE.
  GHASH_POLYVAL_ACC_2: ghash_polyval_acc h a [b;c] = prop3(xor(pmul(xor a b)(dot h h))(pmul c h)).
  Match: a=brev xi, b=brev cph0, c=brev cph1, h=byteswap128 h. dot(bsw h)(bsw h)=byteswap128 h2 (asm25).

## UPDATE 5 — ROOT CAUSE of the lane-flatten failure (KEY INSIGHT)
After full reduction (lane-split + JOINMID + subword-push + ABBREV_ALL_SUBWORDS x2), the
residual is a PURE flat 64-bit XOR identity over ~30 zw vars (889 chars). BUT:
  - WORD_BITWISE_TAC TIMES OUT even with assumptions discarded (pure XOR, ~30 vars — should be
    instant). => WORD_BITWISE is wrong tool here; USE WORD_RULE (XOR-group algebra, no bit-blast).
  - MORE IMPORTANTLY: the two sides' VARIABLE SETS DIFFER (LHS has zw24,zw15,zw7,zw12,zw14,zw6,
    zw2,zw21,zw13...; RHS has zw9,zw4,zw30,zw31,zw22,zw19...). A pure XOR id can only hold if both
    sides share vars w/ matching parity. They DON'T => the abbreviation gave DIFFERENT zw names to
    LHS-subword(qqA) vs RHS-subword(qqB) that are SEMANTICALLY EQUAL pmuls but SYNTACTICALLY
    distinct qq atoms.

THE FUNDAMENTAL PROBLEM: genuine register pmuls (qq from LHS=gq19) and tower pmuls (qq from RHS=
unfold_tower) are SEPARATE abbreviations. They denote equal products but aren't syntactically
identical (word_insert / word_xor(word 0) / lane packaging differs PER pmul, not just the mids).
Recognizing qqA=qqB IS exactly the MERGE_2BLK work I'm trying to remove.

=> The "unfold_tower + equate to genuine register" approach does NOT avoid the merge. The spike
avoided it because raw2 WAS the synthetic unfold (identical pmuls by construction). Our genuine
register is a DIFFERENT syntactic form of the same value.

## WHAT ACTUALLY NEEDS TO HAPPEN (correct EQ_PROP3 adoption):
Option X (the RIGHT one): normalize the GENUINE register's per-block pmul INPUTS to clean
  brev forms FIRST (word_bytereverse cph_i, word_xor(brev xi)(brev cph0)) so that the genuine
  register BECOMES literally ghash_Nblock_karatsuba[(brev-form inputs, h_tw, hk_field)] — i.e.
  build triples from the NORMALIZED inputs and prove gq19 = ghash_Nblock(triples) where the
  per-pmul operands are already in canonical form on BOTH sides (so abbrev unifies them).
  Need per-pmul input rewrites:  word_subword(join(rf8 X)(rf8 X))(64,128) = word_bytereverse X
    (the lane-swap brev) and word_xor(word 0) Y = Y, and the word_insert junk-lane collapse.
  These are CHEAP WORD_BLAST lemmas PER input (cph0,cph1, and the xi+cph0 combo for block0).
  Once inputs are canonical, unfold_tower triples == gq19 by REWRITE alone (REFL), like spike.

Option Y (fast pragmatic): the final residual IS true (it's the genuine=tower lane id); the
  abbreviation just needs to unify the equal pmuls. Use WORD_RULE not WORD_BITWISE on the lanes,
  AND ensure ABBREV unifies by abbreviating pmuls to a canonical key. OR keep MERGE_2BLK for the
  pmul-pairing (cheap part) + EQ_PROP3 for the reduce. But that's the hybrid we measured as moot.

Option Z (SHIP IT): revert bridge to the PROVEN MERGE_2BLK/FINISH_2BLK route (already in file,
  ~73s but CORRECT). Keep the needs+byte_list_at corollary improvements. Defer EQ_PROP3 to a
  follow-up. The byte_list_at output (Task 3) is independent and valuable.

## DECISION POINT for next session: try Option X (canonical-input rewrites) — it's the true
   D7 recipe. If the per-input brev rewrites land, the close is REWRITE+REFL (instant) + EQ_PROP3.
   The lane-flatten detour was a wrong turn (it re-does the merge).

## UPDATE 6 — DECISIVE FINDING: unfold-tower-equate CANNOT avoid the pmul merge
Even with the CORRECT triples (htw = byteswap128 h2 / byteswap128 h — verified: layer's
karatsuba_block_pl uses subword h_tw (64,64), genuine PL-block1 op2 = subword h (0,64), and
subword(bsw h)(64,64)=subword h(0,64) ✓), after:
  REWRITE[MID0_EQ;MID1_EQ;tower_bsw;WORD_REVERSEFIELDS_REVERSEFIELDS;BYTESWAP_LO/HI];ASM_REWRITE;
  ABBREV_INNER_PMULS x3; WORD_EQ_LANES_128; JOINMID+push; ABBREV_ALL_SUBWORDS
the flat 877-char 2-lane goal has DIFFERENT variable sets on LHS vs RHS:
  conj1 LHS vars: zw0,1,2,6,10..17,21  ; RHS vars: zw8,10..13,19,22,24..27
=> WORD_RULE / WORD_BITWISE both TIME OUT (goal is FALSE as a free-var XOR id because the
   genuine-register pmuls (qq from gq19) and the tower pmuls (qq from unfold_tower) are
   SEPARATE atoms; ABBREV gives subword(qq_gen) and subword(qq_tower) distinct zw even though
   qq_gen = qq_tower semantically).

ROOT: equating a genuine sim register to a SEPARATELY-unfolded tower necessarily leaves the
per-block pmul atoms in two syntactic copies; unifying them IS the MERGE_2BLK work. The spike
sidestepped this only because raw2 WAS the unfold (one copy).

## CONCLUSION: the "unfold_tower + prove gq19 = reversefields(ghash_Nblock triples)" path is a
DEAD END for genuine registers. The real D7 recipe (per memory) must instead REWRITE gq19's
own pmul INPUTS to canonical brev forms IN PLACE, so the register becomes ghash_Nblock_karatsuba
[canonical triples] with ONE set of pmuls, then EQ_PROP3 fires. Requires input-normalization
lemmas:  subword(join(rf8 X)(rf8 X))(64,128) -> word_bytereverse X ;  word_xor(word 0) Y -> Y ;
word_insert-junk-lane collapse.  AND a GHASH_Nblock fold direction that matches (fold the
register's accumulated pl/ph/pm into ghash_Nblock form via kara_acc, not via a fresh unfold).

This is a SUBSTANTIAL redesign of the close — NOT the ~5-line drop-in the memory recipe implied
(that recipe was validated on the SYNTHETIC spike term, not a genuine register).

## SHIPPED THIS SESSION (safe, committable):
- needs "common/ghash_nblock_karatsuba.ml" added to dec 2block file (loads clean).
- This progress doc + memory update characterizing the gap.
## NOT DONE: GHASH bridge still uses MERGE_2BLK/FINISH_2BLK (PROVEN, ~73s). byte_list_at corollary
   (Task 3) not yet added — should be done independently (it's orthogonal & valuable).

## UPDATE 7 — BREAKTHROUGH: bridge eq reduces to a TINY residual (XOR-comm in Barrett reduce)
KEY FIX: triples must use htw = byteswap128 h2 / byteswap128 h (NOT h2/h). Layer's
karatsuba_block_pl uses subword h_tw (64,64); genuine PL op2 = subword h (0,64) =
subword(byteswap128 h)(64,64). So htw = byteswap128 h_real. Define:
  triples_bsw = [(in0_genuine, byteswap128 h2, byteswap128 hk); (in1_genuine, byteswap128 h, hk)]
  rhs_bsw = word_reversefields 8 (ghash_Nblock_karatsuba triples_bsw)
  tower_bsw = unfold_tower triples_bsw

WORKING bridge-eq proof prefix (gq19 = rhs_bsw under asm23/asm24), gets to a UNIFIED qq set:
  STRIP_TAC THEN REWRITE[MID0_EQ; MID1_EQ] THEN REWRITE[tower_bsw] THEN
  REWRITE[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE[BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  REWRITE[WORD_XOR_0; WORD_XOR_0_LEFT] THEN   <-- CRUCIAL: unfold_tower strips word_xor(word 0)
  ASM_REWRITE[] THEN
  ABBREV_INNER_PMULS_TAC x3   -> qq0..qq8 SHARED between genuine & tower (block pmuls qq0-5 identical!)
  GEN_REWRITE_TAC I [WORD_EQ_LANES_128] THEN
  REWRITE[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR] (x2) THEN
  ABBREV_ALL_SUBWORDS_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE[WORD_SUBWORD_SUBWORD;JOIN_SUBWORD_RULES;WORD_SUBWORD_XOR;JOINMID](x2)
=> RESIDUAL (721 chars, 2 lanes): a FLAT XOR id over zw8..zw19 (SHARED, cancel) PLUS
   c1: LHS-only {zw3,zw6} vs RHS-only {zw1,zw4} ; c2: {zw2,zw7} vs {zw0,zw5}.
   WORD_BITWISE FAILS (not equal as free vars) because zw3/zw6 (genuine) and zw1/zw4 (tower)
   are subwords of the wa/wv Barrett-reduce pmuls (qq6=pmul(subword(xor qq1 qq3)0)W etc) that
   are EQUAL-by-construction but differ by XOR-COMMUTATIVITY in the pmul arg
   (genuine: word_xor qq3 qq1 ; tower: word_xor qq1 qq3) => distinct abbreviations.

## THE LAST GAP & FIX (next session — small!):
The genuine register's Barrett reduce (polyval_reduce_prop3 evaluated by sim) and the layer's
karatsuba_reduce_shared let-form agree only up to XOR-assoc/comm inside the wa/wv pmul ARGS.
Options:
 (a) BEFORE abbreviating the reduce pmuls, normalize the qq-xor ORDER canonically so
     word_xor qqA qqB matches on both sides. A targeted GEN_REWRITE with a sorted-XOR conv, or
     rewrite the few offending word_xor qqI qqJ via WORD_RULE-proved SYM equalities, then the
     wa/wv pmuls unify -> single qq6/qq7 -> WORD_RULE closes the flat residual.
 (b) DON'T unfold karatsuba_reduce_shared at all. Instead prove
     gq19 = karatsuba_reduce_shared PL PH PM  for the genuine accumulated PL/PH/PM (= kara_acc
     triples_bsw), via the sim's own reduce structure, then fold to ghash_Nblock. The reduce
     reconciliation is then KARATSUBA_REDUCE_AS_PROP3 (layer lemma) — already proven — so no
     hand XOR-comm. THIS IS LIKELY THE CLEAN PATH: keep reduce FOLDED.
 (c) After reaching the 721-char residual, the 4 mismatched zw are 2 pairs; assert
     zw3 = zw1 /\ zw6 = zw4 (etc) — but they're not equal individually; only zw3⊕zw6 = zw1⊕zw4.
     So need the pmul-level merge: SUBGOAL qq6_gen = qq6_tower via WORD_PMUL arg-comm. ~2 merges.

RECOMMENDATION: try (a) first (cheap): after the x3 ABBREV_INNER_PMULS, the reduce pmul args
contain word_xor qq1 qq3 / qq3 qq1 etc — REWRITE with a canonical form. OR simpler: do ONE
MERGE_PMUL_ATOMS_TAC (the 1block helper, in scope) on the qq6/qq7 reduce pmuls only — it proves
them equal via PMUL_CONG_128 + WORD_BLAST(args) — then WORD_RULE the flat lanes. This is HYBRID
but the merge is now just 2 tiny reduce-pmul pairs, not the whole tower (so ~fast, not 73s).

## ALL building blocks verified in session & ready to embed:
  BYTESWAP128_INVOLUTION, unfold_tower, JOIN_EQ_SPLIT, ABBREV_ALL_SUBWORDS_TAC,
  WORD_EQ_LANES_128, MID0_EQ/MID1_EQ (goal-specific - generalize), triples_bsw construction.

## UPDATE 8 — FINAL DIAGNOSIS: genuine reduce uses a DIFFERENT pack/lane convention than layer
After abbreviating ALL pmuls (block qq0-5 SHARED + reduce wa/wv) and lane-flattening, the
residual conjuncts mismatch at the qq level:
  c1 & c2: LHS(genuine)-only = {qq6, qq8}  vs  RHS(tower)-only = {qq7, qq9}
where  qq6 = pmul(subword(word_xor qq1 qq3) 0) W   [genuine wa]
       qq7 = pmul(subword(word_xor qq2 qq0) 0) W   [tower wa]
=> genuine `a` lane (prop3 input lane 0) = xor qq1 qq3 (block-1 ph ⊕ block-0 ph?), but tower's
   = xor qq2 qq0. The Barrett-reduce lane extraction (a=subword t(0,64), b=(64,64), c=(128,64),
   d=(192,64) in polyval_reduce_prop3 / karatsuba_reduce_shared) picks DIFFERENT qq combos
   because the genuine register's accumulated (pl,ph,pm) pack the per-block products in a
   different LANE ARRANGEMENT than the layer's pack_corrected/kara_acc.

ROOT CAUSE: This is NOT mere XOR-comm. The dec assembly's GHASH accumulator packs the Karatsuba
(pl,ph,pm) into the 256-bit value with a lane layout that differs from Mila's layer convention
(pack_corrected: zx pl | shl(xor pl ph pm)64 | shl ph 128). The enc spike matched because enc
uses the same binary as Mila's source. The DEC binary's reduce differs.

## CONCLUSION FOR THE TASK:
The "unfold tower + equate genuine register" route gets 95% there (block pmuls unify perfectly
with htw=byteswap128 h_real triples + WORD_XOR_0 prepass) but the FINAL Barrett-reduce lane
reconciliation fails because the genuine dec register's pack convention != layer's. Closing it
needs EITHER:
  (i) the layer applied at the FOLDED karatsuba_reduce_shared level (so KARATSUBA_REDUCE_AS_PROP3
      handles the reduce) — requires proving gq19 = karatsuba_reduce_shared GPL GPH GPM by folding
      the sim-evaluated reduce back (hard: sim beta-reduced the lets), then GPL/GPH/GPM = kara_acc
      triples (lane-match — the real work), OR
  (ii) determining the dec-specific triple lane assignment that makes the genuine reduce's
      a/b/c/d lanes match the layer's (different from enc; needs analysis of the dec .S GHASH
      accumulate order), OR
  (iii) the MERGE_2BLK route (proven, ~73s) — i.e., DON'T adopt EQ_PROP3 for dec until (i)/(ii)
      is resolved. The block-pmul unification I achieved could feed a SHORTER merge.

## SHIPPED (committable, safe):
  - needs "common/ghash_nblock_karatsuba.ml" (loads clean).
  - This exhaustive diagnosis doc.
  - (TODO) byte_list_at corollary — INDEPENDENT of GHASH route, should still be added.
  - GHASH bridge UNCHANGED (proven MERGE_2BLK/FINISH_2BLK).

The memory recipe's "~5-line drop-in EQ_PROP3" was validated on the SYNTHETIC enc spike term;
it does NOT directly transfer to the genuine DEC register due to the pack-convention gap above.

## UPDATE 9 — SHARPER: the gap is a pl<->ph SWAP (likely a 1-line triple fix!)
Genuine wa Barrett-input a-lane = word_xor qq1 qq3 (the PH-products: qq1=pmul(.. subword h 64),
qq3=pmul(.. subword h2 64)).  Tower wa a-lane = word_xor qq2 qq0 (the PL-products).
karatsuba_reduce_shared sets a = subword pl (0,64); pl = sum of karatsuba_block_pl =
pmul(subword in 0)(subword htw 64).  So the genuine register puts the PH-products where the
layer expects PL.  => GENUINE dec reduce has pl<->ph SWAPPED vs layer convention.

LIKELY FIX (try next, cheap): in karatsuba_block_pl/ph the htw lane usage is
  pl: subword htw (64,64) ; ph: subword htw (0,64).
We chose htw = byteswap128 h_real so that subword(bsw h)(64,64)=subword h(0,64) matched genuine
PL op2=subword h(0,64).  But if genuine's pl-slot actually holds the ph-product, we instead want
htw = h_real (NOT byteswapped) for the pl/ph to land swapped, OR swap which genuine pmul is
called the block input's "pl".  Concretely: RE-TEST triples with htw = h_real (h2, h) — earlier
that gave a residual too, but the FAILURE MODE differs; with the WORD_XOR_0 prepass + correct
htw it may now unify.  Grid to try (2x2): htw in {h_real, byteswap128 h_real} x block order
{(blk0,blk1),(blk1,blk0)}.  The combo where the wa a-lane qq-set matches (both use the SAME two
qq) is correct; then WORD_RULE closes.

Diagnostic to run per combo: reach the "c1 LHSonly / RHSonly" check; the RIGHT combo gives
LHSonly = RHSonly = [] (empty) => WORD_RULE closes instantly.

## This is the single remaining unknown. Everything else (front to s370, MASK_COLLAPSE, MID0/MID1
   normalization, WORD_XOR_0 prepass, block-pmul unification, lane-flatten machinery, EQ_PROP3
   application, GHASH_POLYVAL_ACC_2 finish) is WORKED OUT. Resolve the 2x2 htw/order grid first.

## UPDATE 10 — DEFINITIVE (2x2 grid tested): reduce intermediates are lane-swapped, NOT mergeable
Grid results (c1 LHSonly/RHSonly; empty=win):
  htw=h,  order01:  {qq0,qq3,qq4,qq7,qq10,qq12} / {qq1,qq2,qq5,qq6,qq11,qq13}   (worst)
  htw=bswh,order01: {qq6,qq8} / {qq7,qq9}                                        (best, block pmuls unify)
  htw=bswh,order10: {qq7,qq8} / {qq6,qq9}
  htw=bswh,hkswap,order01: {qq4,qq7,qq8,qq10} / {qq5,qq6,qq9,qq11}
=> NO combo reaches empty. With htw=byteswap128 h_real, order01 (block0 first): block pmuls
   qq0-qq5 unify PERFECTLY; ONLY the Barrett wa/wv reduce pmuls remain split:
     genuine wa = pmul(subword(word_xor qq1 qq3) 0) W   (PH-lane sum)
     tower   wa = pmul(subword(word_xor qq2 qq0) 0) W   (PL-lane sum)
   qq1⊕qq3 != qq2⊕qq0 in general => these wa's are NOT equal; the reduce only agrees AFTER full
   Barrett mixing. The genuine dec reduce extracts prop3 lanes a,b,c,d in a DIFFERENT order than
   karatsuba_reduce_shared. CONFIRMED NOT a triple/htw/order/hk choice.

## FINAL VERDICT: EQ_PROP3 cannot close the dec bridge by "unfold tower + equate register" —
the genuine dec Barrett reduce is lane-swapped vs the layer's karatsuba_reduce_shared. The ONLY
clean adoptions are:
  (A) Keep karatsuba_reduce_shared FOLDED: prove gq19 = karatsuba_reduce_shared GPL GPH GPM
      (fold the sim-unfolded reduce back — needs GSYM of the prop3/reduce let-chain, HARD), then
      GPL/GPH/GPM = kara_acc triples_bsw (block-level lane match — DOABLE), then EQ_PROP3.
      => requires a "RE-FOLD the genuine register's Barrett reduce to karatsuba_reduce_shared"
         lemma/conversion. This is the real missing piece.
  (B) Accept the proven MERGE_2BLK/FINISH_2BLK route (it bit-blasts the WHOLE reduce, so the
      lane-swap is irrelevant). ~73s but CORRECT and SHIPPED.

I recommend (B) for now (ship) + a focused follow-up for (A): write a conversion that recognizes
the sim's evaluated `polyval_reduce_prop3`-shaped register as `word_reversefields 8
(polyval_reduce_prop3 PACKED)` then `karatsuba_reduce_shared` via KARATSUBA_REDUCE_AS_PROP3_CLEAN
backwards, with PACKED = pack_corrected GPL GPH GPM. The hard part is identifying PACKED from the
sim output (the 256-bit pre-reduce value). Possibly: the sim register at an EARLIER step (before
the rev64/reduce) holds the raw packed pmul-sum — capture THAT (like enc's s367 pre-reduce) and
bridge it, instead of the post-reduce s370. Check the dec step map for the pre-Barrett state.

>>> KEY IDEA FOR NEXT SESSION: bridge at the PRE-REDUCE step (raw 256-bit pmul accumulator),
    not s370 (post-reduce). EQ_PROP3's LHS ghash_Nblock = reduce(acc); if we match the ACC
    (pmul-sum) before reduction, the lane-swap in the reduce never surfaces. Find the dec step
    where Q17/18/19 hold the raw (pl,ph,pm) or the packed 256-bit sum, pre-Barrett.

## UPDATE 11 — FINAL ARCHITECTURAL CONCLUSION (verified from every angle)
Tested the "keep reduce FOLDED" path too: proved the goal reduces to
  gq19 = karatsuba_reduce_shared TPL TPH TPM   (TPL/TPH/TPM = kara_acc triples_bsw components)
After REWRITE[karatsuba_reduce_shared;LET;BYTESWAP_LO/HI;WORD_XOR_0] + ABBREV_INNER_PMULS x3 +
EXPAND qq6-9 + PMUL_W_64_128 + WORD_EQ_LANES_128 + lane distribute, BOTH sides become the SAME
`karatsuba_reduce_shared` formula over shared qq0-qq5, BUT the genuine register's reduce assigns
the Barrett a/b/c/d lanes differently (genuine wa input = word_xor qq1 qq3 [ph-lane], spec wa
input = word_xor qq2 qq0 [pl-lane]). Closing requires the W-reduction bit-blast over
word_subword(word_shl(word_zx ..)63/62/57)(lane) — which TIMES OUT (even one lane), exactly the
bespoke staging the dec 1-block does BY HAND in FINISH_WV_REDUCE_TAC (it inlines r1/u/r2 because
the generic tactic stack-overflows; see 1block file ~L1752 + methodology doc §5).

>>> ROOT ARCHITECTURAL FACT: the dec binary's GHASH Barrett reduction is ALREADY bridged to the
polyval form by the dec-specific GMULT_FULL_CORRECT_BA / GMULT_REDUCE_PROP3 (the OLD/current
route). Mila's EQ_PROP3 layer bridges a DIFFERENT (her) reduce shape (karatsuba_reduce_shared)
to prop3. The dec register's reduce != karatsuba_reduce_shared lane-for-lane, so EQ_PROP3 cannot
consume the dec register without RE-deriving the reduce reconciliation (= the ~73s / bespoke work
we wanted to avoid). 

CONCLUSION: EQ_PROP3 is the right tool for proof terms whose reduce IS karatsuba_reduce_shared
(Mila's own binary / the synthetic spike). For OUR dec binary it is NOT a drop-in; the reduce is
the irreducible bespoke piece and is already handled by GMULT_FULL_CORRECT_BA. The block-Karatsuba
pmul layer DOES unify cleanly (htw=byteswap128 h_real + WORD_XOR_0 prepass) — that part of D7
transfers and could shorten a future merge of the per-block products, but the Barrett reduce does
not. Recommend: KEEP MERGE_2BLK/FINISH_2BLK (proven). Revisit EQ_PROP3 only if/when the dec proof
is re-based onto Mila's exact karatsuba_reduce_shared reduce instructions (a binary/spec change),
or bridge at the raw pmul-accumulator step and reuse GMULT_FULL_CORRECT_BA for the reduce (which
is just the current route, reorganized).

## UPDATE 12 — "Can we adopt Mila's approach?" — DEFINITIVE, tested 4 more ways
Re-examined whether the lane-transpose was just my htw/triple mistake. Findings:
1. Genuine block-1 Karatsuba products (verified by extracting op1-lane/op2 of each pmul):
     pmul(G_lo)(h_LO),  pmul(G_hi)(h_HI),  pmul(G_lo⊕G_hi)(h_MID)   [STRAIGHT lanes: lo·lo, hi·hi]
   where G = genuine rev64 input = word_join(subword(rf8 cph1)0)(subword(rf8 cph1)64) = lane-swap(rf8 cph1)
   (NOT word_bytereverse/byteswap128/rf8 — it's rev64 = per-lane byte-rev WITHOUT the 64-bit lane swap).
2. Mila's karatsuba_block_pl/ph pair lanes CROSSED (in_lo·htw_hi, in_hi·htw_lo). To make her CROSSED
   layer produce the genuine STRAIGHT products needs htw = byteswap128 h (so htw_hi = h_lo). => htw=bsw h
   makes the BLOCK pmuls match (confirmed: tower_bsw block pmuls unify with genuine).
3. BUT EQ_PROP3 → clean spec needs kara_quad_pmul = xor(pmul in_k (byteswap128 h_k)) to line up with
   GHASH_POLYVAL_ACC_2 (multiplier byteswap128 h, since byteswap128 h2 = polyval_dot(bsw h)(bsw h)=asm25).
   kara_quad_ok forces h_tw = byteswap128 h_true, so h_tw=bsw h ⟹ h_true=h ⟹ kara_quad_pmul uses RAW h
   (not bsw h) ⟹ does NOT match the polyval spec. Conversely h_tw=h_real ⟹ kara_quad uses bsw h (spec OK)
   but block pmuls then CROSS and don't match genuine. ⟹ irreconcilable by triple/htw/hk/order choice.
4. DECISIVE: even with the block accumulator matching EXACTLY (bpl/bph/bpm = kara_acc triples_bsw =
   genuine pl/ph/pm), gq19 != karatsuba_reduce_shared bpl bph bpm SYNTACTICALLY (8 residual pmuls, not
   alpha-eq). So the dec assembly's Barrett reduction is a DIFFERENT let-chain than Mila's
   karatsuba_reduce_shared — equal VALUE (provable by the bespoke W-reduction blast), different SHAPE.

VERIFIED FACTS (cheap, reusable):
- GHASH_NBLOCK_KARATSUBA_EQ_PROP3 closes the LAYER side in ~0.02-0.04s for BOTH htw conventions
  (quads with h_tw=byteswap128 h_real OR h_tw=h_real); kara_quad_ok discharged by
  REWRITE[kara_quad_ok;BYTESWAP128_INVOLUTION] + ASM_REWRITE[karatsuba_mid;BYTESWAP128_SUBWORD_LO/HI]
  + WORD_RULE. So the layer ITSELF is sound and fast on our operands.
- kara_quad_pmul quads2 0 = xor(pmul(xor(rf8 xi)(rf8 cph0))(byteswap128 h2))(pmul(rf8 cph1)(byteswap128 h))
  = EXACTLY the GHASH_POLYVAL_ACC_2 prop3 argument (given asm25 + word_bytereverse=word_reversefields 8).
  So ghash_Nblock_karatsuba(project_triples quads2) = word_bytereverse(ghash_polyval_acc(bsw h)(brev xi)
  [brev cph0; brev cph1]) — the EXACT xi_p store spec — PROVED via the layer.

## ANSWER TO "can we adopt Mila's approach to the dec ghash tower?":
YES for the TOWER (block Karatsuba pmuls + the EQ_PROP3 reduce→polyval bridge): the layer applies to
our operands and lands the exact spec, fast. NO as a drop-in replacement for the dec REGISTER bridge,
because the dec binary's Barrett reduce is a different let-chain than karatsuba_reduce_shared, so
gq19 (the post-reduce register) is not syntactically ghash_Nblock_karatsuba(...). 

THE WORKABLE ADOPTION (next session): bridge at the PRE-Barrett step. The dec assembly accumulates the
raw Karatsuba (pl,ph,pm) or the packed pmul-sum in Q17/Q18/Q19 BEFORE running its Barrett reduction
(steps ~351-369, the pmull/pmull2/eor accumulate; the reduce is the later eor3/W-mult/ext sequence).
Capture the register at the step where it holds  pl=Σpmul(in_lo·htw_hi) etc OR the packed value, match
THAT to kara_acc triples_bsw / pack_corrected (block pmuls unify — PROVEN), then let
ghash_Nblock_karatsuba's OWN karatsuba_reduce_shared be the spec for the rest — i.e. assert the dec
reduce instructions compute karatsuba_reduce_shared of that accumulator. That assertion is the SAME
bespoke W-reduction GMULT_FULL_CORRECT_BA already proves for dec; reuse it. Net: layer handles the
N-block fold (the part that scales), GMULT_FULL_CORRECT_BA handles the fixed reduce. This is a genuine
simplification of MERGE_2BLK (drops the per-band lane-flatten) and the right shape for 3..8 blocks.
Requires re-mapping the dec step→PC to find the pre-reduce accumulator state (Q17/18/19 before s351-ish).
