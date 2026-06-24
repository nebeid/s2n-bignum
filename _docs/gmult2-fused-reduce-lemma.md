# GMULT2_FULL_CORRECT_BA — the scalable 2-block fused multiply+reduce (THE timing win)

## What it is (PROVEN, ~1.2s total)
The decrypt analog of the 1-block GMULT_FULL_CORRECT_BA, but for the 2-block accumulate-then-
one-reduce shape. Abstract over a0,b0,a1,b1:int128. States: the assembly's GHASH byteform that
XOR-accumulates TWO Karatsuba triples (per block: pl=pmul(a_lo,b_lo), ph=pmul(a_hi,b_hi),
pm=pmul(a_lo^a_hi, b_lo^b_hi)) into (pl,ph,cross) lanes then runs the shared W-reduction, equals
  polyval_reduce_prop3 (word_xor (word_pmul a0 b0) (word_pmul a1 b1)).

This is OUR-binary analog of Mila's GHASH_NBLOCK_KARATSUBA_EQ_PROP3 — built from OUR proven
(a) PMUL_KARATSUBA + (b) GMULT_REDUCE_PROP3, so it reuses the W-reduction lemma (proven ONCE)
instead of re-blasting it per band. Closes in ~1.2s vs MERGE_2BLK's ~73s.

## Proof recipe (the key insight — NO W-reduction blast):
  let PACK2_ID = prove(`tL = word_xor (word_pmul a0 b0) (word_pmul a1 b1)`,
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REWRITE_RULE[LET_DEF;LET_END_DEF] PMUL_KARATSUBA] THEN
     REWRITE_TAC[WORD_ZX_XOR; WORD_SHL_XOR] THEN CONV_TAC WORD_RULE);;   (* 1.14s *)
  where tL = word_xor(word_xor (word_zx plS)(word_shl(word_zx crossS)64))(word_shl(word_zx phS)128)
  and plS/phS/crossS are the XOR-sums of the two blocks' Karatsuba limbs (a-then-b pmul order).

  let gmr_tL2 = REWRITE_RULE[REWRITE_RULE[LET_DEF;LET_END_DEF] KARATSUBA_LIMBS]
                  (SPEC tL (REWRITE_RULE[LET_DEF;LET_END_DEF] GMULT_REDUCE_PROP3));;

  let GMULT2_FULL_CORRECT_BA = prove(gmult2_goal_ab,
     REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     GEN_REWRITE_TAC LAND_CONV [gmr_tL2] THEN      (* byteform -> prop3 tL *)
     AP_TERM_TAC THEN                               (* prop3 cong -> tL = pmul-sum *)
     REWRITE_TAC[PACK2_ID]);;                       (* 0.01s *)

KEY: use a-then-b pmul order in the statement (matches PMUL_KARATSUBA output) so PACK2_ID's
WORD_RULE close needs no WORD_PMUL_SYM juggling. The W-reduction NEVER gets bit-blasted — it's
encapsulated in GMULT_REDUCE_PROP3 (proven once via BITBLAST in the dec 1-block file / a checkpoint).

## Wiring into the dec 2-block bridge (in progress)
Instantiate GMULT2_FULL_CORRECT_BA at the genuine register operands:
  a0=in1_genuine (rev64 cph1 form), b0=h, a1=in0_genuine (xor(rev64 xi-lanes)(rev64 cph0)), b1=h2
  [blocks SWAPPED vs naive: the dec accumulator XORs block-1 into the layer's "block0" slot;
   kara_quad_pmul/the accumulator is XOR-commutative so RHS prop3 is unchanged.]
Then gmult2_gen : <byteform over those> = prop3(pmul in1 h ^ pmul in0 h2).
Need: read Q19 s370 (=gq19) = that byteform LHS. After REWRITE[MID0_EQ;MID1_EQ] (collapse the
genuine packed-mid `subword hk` to word_xor of input lanes), gq19 and gmult2_gen-LHS have the SAME
reduction skeleton and differ ONLY in the 6 block-pmul OPERAND encodings (genuine rev64-join form
vs the instantiated in_i form — but in_i ARE the genuine forms, so they should match; remaining
gap is the byteswap128-h lane normalization). Reconcile via per-pmul PMUL_CONG_128 + 64-bit
WORD_BLAST on operands (cheap, 6 pmuls) OR by instantiating with the EXACT genuine subterms.
Then prop3(pmul in1 h ^ pmul in0 h2) -> GHASH_POLYVAL_ACC_2 spec via the H^2 relation (asm25)
+ WORD_BYTEREVERSE_REVERSEFIELDS, giving ghash_polyval_acc (byteswap128 h)(brev xi)[brev cph0;brev cph1].

## Status: GMULT2 + PACK2_ID PROVEN in session. Final gq19=byteform reconciliation in progress.
## NEXT: promote GMULT2_FULL_CORRECT_BA + PACK2_ID to a reusable lemma (parametric, scales to
   4/8 blocks by the same recipe with N PMUL_KARATSUBA terms in tL). This is the real D7-equivalent
   for OUR binary, replacing MERGE_2BLK/FINISH_2BLK.

## UPDATE — GMULT2 + PACK2_ID PROVEN (~1.2s); register-reconciliation is standard W-staging
Confirmed in session: GMULT2_FULL_CORRECT_BA proves in ~1.2s (PACK2_ID 1.14s via
WORD_ZX_XOR/WORD_SHL_XOR+WORD_RULE; GMULT2 itself 0.01s via GMR-fold+AP_TERM+PACK2_ID). This is
the OUR-binary equivalent of Mila's flat EQ_PROP3 reduce — the W-reduction is never re-blasted.

Wiring `read Q19 s370 (gq19) = GMULT2-instantiated byteform`:
- Instantiate GMULT2 with blocks SWAPPED + genuine operands:
    SPECL [in1_genuine; `h`; in0_genuine; `h2`] GMULT2_FULL_CORRECT_BA
  (block-1=cph1 goes in slot0 because the dec accumulator XORs it first; XOR-comm => RHS prop3
   unchanged). RHS = polyval_reduce_prop3 (word_pmul in1 h ⊕ word_pmul in0 h2).
- gq19 vs that byteform LHS: after REWRITE[MID0_EQ;MID1_EQ] (collapse packed `subword hk` mid to
  word_xor of input lanes), the two are the SAME GMULT byteform up to: (i) the genuine rev64 input
  packing `word_subword(word_join(rf8 X)(rf8 X))(64,128)` vs the instantiated in_i (which ARE those,
  so they match), and (ii) the inner W-reduction lane staging. After ABBREV block pmuls (qq0-5) +
  ONCE WORD_PMUL_SYM + PMUL_W_64_128 (loop to clear all 4 W-pmuls), the goal is a PURE
  shl/zx/subword/join/xor identity over qq0-5 (no pmuls). 
- THAT residual = exactly the 1-block FINISH_WV_REDUCE_TAC shape (r1/u/r2 shift-triple staging).
  The 1-block closes it by abbreviating each `word_xor(shl 63)(shl 62)(shl 57)` triple to r1, the
  `u` mid to an abbrev, then a final flat 64-bit WORD_BLAST (~24-30s, ONE TIME). Reuse that staging
  here (the 2-block residual has the same shape, just qq0-5 instead of 1-block's qq0-2).
  ALTERNATIVELY: since gq19 IS karatsuba_reduce_shared(genuine acc) and GMULT2-byteform IS
  GMULT_REDUCE_PROP3(genuine acc), and BOTH equal prop3(same acc), prove gq19 = byteform by
  rewriting BOTH to prop3 (GMULT_REDUCE_PROP3 forward on the byteform side; and gq19 via its own
  reduce-to-prop3 which is GMULT_REDUCE_PROP3 after normalizing the rev64-join input packing to
  the plain subword form via JOINMID/SUBSUB_JOIN_DUP), then AP_TERM -> accumulators equal (WORD_RULE).

## BOTTOM LINE (answer to the user): YES — Mila's approach (fold the per-block Karatsuba products,
reduce ONCE via a pre-proven abstract reduce lemma) DOES adopt to the dec ghash tower, using OUR
GMULT_REDUCE_PROP3 as the abstract reduce (since our binary's reduce != Mila's karatsuba_reduce_shared
shape). GMULT2_FULL_CORRECT_BA captures it at ~1.2s. Scales to N blocks: tL = XOR of N Karatsuba
packs; PACK2_ID generalizes to PACKN_ID by the same WORD_ZX_XOR/WORD_SHL_XOR+WORD_RULE; GMULT_REDUCE
_PROP3 is reused unchanged. The only per-proof cost is normalizing the genuine sim register to the
byteform (the rev64 input packing + W-lane staging), which is mechanical and ~one-time per block-count.

## UPDATE 2 — register-shape gap pinned precisely
gq19 (read Q19 at s370) top structure = word_xor (word_subword(word_join G G)(64,128)) (word_xor...)
where G is the inner reduce value. This is the DEC s370 register's specific reduce arrangement and
does NOT match GMULT_REDUCE_PROP3's byteform LHS (word_xor wv (word_xor (byteswap128 v0)(join dd cc)))
directly, nor GMULT_FULL_CORRECT_BA's. The 1-block matched GMULT_FULL_CORRECT_BA at s351 (an EARLIER
step); s370 (the 2-block bridge, after the second block's accumulate + the shared reduce) has a
different surface arrangement of the SAME reduction.

So to wire GMULT2 in, the register must be bridged at the step whose form matches GMULT2's byteform
LHS (the `word_xor wv (word_xor (byteswap128 v0)(word_join dd cc))` shape) — likely a step slightly
before/after s370, OR after a GCM_SIMD_SIMPLIFY normalization pass. The 1-block found this empirically
at s351. For the 2-block, re-map the dec steps ~351-370 to find the state matching GMULT2's LHS shape
(the `word_xor wv (...)` form before the final ext/rev64), and bridge THERE via gmult2_dec.

## NET RESULT THIS SESSION (the timing answer, achieved):
GMULT2_FULL_CORRECT_BA PROVEN ~1.2s — the scalable fused 2-block multiply+reduce, our-binary analog
of Mila's flat EQ_PROP3, reusing GMULT_REDUCE_PROP3 (W-reduction proven once) instead of re-blasting
per band. This IS the mechanism that matches Mila's tower timing for the reduce. Remaining: bind it to
the exact dec register state (mechanical step-shape matching, ~the 1-block's s351 discovery repeated
for 2-block). PACK2_ID (1.14s) is the only real compute; everything else is rewriting.

## UPDATE 3 — FINAL: GMULT2 proven & useful, but the genuine-register transpose persists
Verified the two ways to instantiate GMULT2 and their irreconcilable tension (same as the
UPDATE-10 finding in dec-2block-eqprop3-progress.md, now confirmed at the GMULT2 level):
- Instantiate GMULT2 with GENUINE operands (a=rev64 input, b=h/h2): its LHS = gq19 (matches the
  register after MID rewrites + block-pmul abbrev — reduces to a pure W-lane identity), BUT its
  RHS = prop3(pmul(rev64 cph1) h ⊕ pmul(rev64...) h2), which does NOT equal the GHASH_POLYVAL_ACC_2
  spec prop3(pmul(brev cph1)(byteswap128 h) ⊕ ...) — they differ by the rev64-vs-bytereverse lane
  arrangement AND h vs byteswap128 h. (spec_chain WORD_RULE fails on exactly this.)
- Instantiate GMULT2 with SPEC operands (a=brev form, b=byteswap128 h): RHS = spec cleanly
  (proven: GHASH_POLYVAL_ACC_2 + asm25 GSYM + WORD_BYTEREVERSE_REVERSEFIELDS + AP_TERM + WORD_RULE),
  BUT its LHS uses brev/bsw operands != gq19's rev64/h operands.
=> Either instantiation leaves a rev64<->bytereverse + h<->byteswap128 lane transpose between the
   genuine register and the spec. This is the SAME transpose the whole investigation surfaced; it is
   intrinsic to the dec binary's GHASH lane convention vs the polyval spec, and GMULT2 (a reduce
   lemma) cannot absorb it — it must be discharged by the per-block-pmul operand reconciliation
   (proving pmul(rev64 X)(h) = pmul(brev X)(byteswap128 X-key) per block via WORD_BLAST on 64-bit
   lanes, i.e. MERGE_PMUL_ATOMS / FAST_OPERAND), OR by the W-lane staging on gq19=byteform.

## CONCLUSIVE ANSWER
GMULT2_FULL_CORRECT_BA (~1.2s) IS the Mila-timing reduce mechanism for our binary and is proven +
committed. But "match Mila's timing" end-to-end for DEC is blocked by the binary's GHASH lane
transpose (rev64 register input + straight-lane Karatsuba with h, vs the polyval spec's
bytereverse + byteswap128-h), which forces a per-block operand reconciliation that is the same
~per-band lane work MERGE_2BLK does. The reduce is now O(1.2s) and amortized; the residual cost is
the operand/transpose reconciliation, which is inherent to this binary (Mila's enc binary does not
have it because its register convention matches her spec). Net: the reduce is solved Mila-fast;
the dec lane-transpose is the irreducible remainder and is correctly handled by the existing
(proven) MERGE route. Shipping MERGE; GMULT2 committed for reuse + the eventual operand-bridge.

## UPDATE 4 — SPLICE EXPERIMENT RESULT (the requested run)
Ran the full splice on the live bridge goal `gq19 = ghash_polyval_acc spec`:
  STRIP; GHASH_POLYVAL_ACC_2; GSYM asm25 (fold H^2); GSYM gmult2_dec  -> RHS = GMULT spec-byteform
  REWRITE[MID0_EQ;MID1_EQ;WORD_BYTEREVERSE_REVERSEFIELDS;BYTESWAP128_SUBWORD_LO/HI]
  ABBREV_INNER_PMULS_TAC ; MERGE_2BLK_TAC
MEASURED: MERGE_2BLK closes the genuine<->spec pmul TRANSPOSE in **5.2s** (much faster than the
~28-73s folklore) and FULLY UNIFIES the two byteforms' block products — both sides end over the
SAME atom set {qq0,qq1,qq4,qq5,qq8,qq10}. So the transpose reconciliation is cheap and DONE.

REMAINING (the only blocker): the two byteforms still differ in the W-REDUCTION SURFACE
arrangement (gq19's s370 register has word_subword(word_join WV WV)(64,128) ext-form + a
byteswap128(word_xor(join)(shl(zx ..))) on the spec side). After PMUL_W_64_128 + TRIPLE_LO/HI +
JOIN/EQ_BY_SUBWORDS lane-split, the residual per lane is a NESTED word_shl/word_ushr/byteswap128
identity over ~12 zw atoms that WORD_BLAST cannot discharge in time (it diverges, same as the
1-block's known WORD_BLAST divergence). The 1-block solves the analogous single-block residual with
~50 lines of bespoke hand-staging (FINISH_WV_REDUCE_TAC: manual r1/u/r2 shift-triple abbreviations).
The 2-block residual has the SAME shape but more atoms; my generic triple/shl-arg abbreviators
partially reduce it but a byteswap128(shl(zx..)) cross-term remains un-normalized.

## CONCLUSION (timing answer, measured)
- REDUCE: solved Mila-fast via GMULT2_FULL_CORRECT_BA (~1.2s, committed).
- TRANSPOSE (genuine rev64/h <-> spec brev/bsw operands): MERGE_2BLK, **5.2s** (measured), fully unifies.
- W-REDUCTION SURFACE match (gq19 s370 form <-> GMULT byteform): the residual is the dec binary's
  bespoke W-lane identity; needs the 1-block's FINISH_WV_REDUCE-style hand staging generalized to
  2 blocks (a finite, mechanical ~50-line tactic), OR bridging at the s351-analog step whose register
  IS the GMULT byteform (avoiding the s370 ext-surface entirely).
PROJECTED total if the W-surface is staged: ~1.2s (reduce) + ~5.2s (merge) + ~25-30s (W-staging,
one-time) ~= 35s, vs the shipped ~73s. Real but bounded; not Mila's 0.08s (the dec lane convention
forbids that). The W-surface staging is the one remaining mechanical task.
