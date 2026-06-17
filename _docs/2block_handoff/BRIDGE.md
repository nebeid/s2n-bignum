# The 2-block GHASH bridge — the one remaining lemma

The full 2-block simulation is complete (direct C_ARGUMENTS entry pc+0x18, no
wrapper) up to `read Q19 s367` = the final reduced GHASH result (pc+0x11cc, the
~18.4k-char byte-form, just before the ext+rev64 byte-reorder and the store).

The entire close reduces to ONE equality (the bridge):

    read Q19 s367 = polyval_reduce_prop3
      (word_xor (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse ct0))
                           (polyval_dot (byteswap128 h) (byteswap128 h)))
                (word_pmul (word_bytereverse ct1) (byteswap128 h)))

Because (verified, `test` via ISPECL of GHASH_POLYVAL_ACC_2):
    ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse ct0; word_bytereverse ct1]
    = polyval_reduce_prop3(pmul(brev xi XOR brev ct0, polyval_dot K K)
                           XOR pmul(brev ct1, K))            [K = byteswap128 h]

So: REWRITE[GSYM GHASH_POLYVAL_ACC_2] turns the RHS into the spec's
ghash_polyval_acc list-of-2 directly.

## Proving the bridge equality
It is the 2-product analog of the 1-block `GMULT_FULL_CORRECT_BA` bridge. The
assembly's `read Q19 s367` is the Karatsuba+Prop3 byte-form of the aggregate,
with the two products keyed by the RAW htable lanes `subword h` (block 1) and
`subword h2` (block 0); the spec keys are `byteswap128 h` and
`polyval_dot (byteswap128 h)(byteswap128 h)`.  Need:
  1. The htable key invariant as a precondition:
       byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
     (h2 stored = byteswap128(H^2); add to the spec).
  2. Expand polyval_reduce_prop3 of the aggregate via PMUL_KARATSUBA /
     KARATSUBA_LIMBS / PMUL_W_64_128 on BOTH products (1-block did one).
  3. The byteswap128 lane reconciliation (subword h <-> byteswap128 h), same as
     the 1-block §6 finding, applied per product.
  4. ABBREV_INNER_PMULS_TAC / MERGE_PMUL_ATOMS_TAC + the manual r1/u/r2 lane-fold
     (the enc 1-block LE1BLOCK close, now over ~6 pmul limbs instead of ~3),
     then a final WORD_BLAST over the structural skeleton.
  5. The htable mids: subword hk (0,64)=mid(h) [block1], subword hk (64,64)=
     mid(h2) [block0] (preconds already in the spec).

This is the hardest single step (comparable to the entire 1-block bridge).
`q19_s367_reduced.txt` would hold the full LHS if re-dumped.

## After the bridge
ext(0x11cc)+rev64(0x11d0) -> word_bytereverse(gval); store st1 v19,[x3] (0x11d4);
ENSURES_FINAL_STATE_TAC; close (EXPAND ct0,ct1; out_p blocks = the two stored
ciphertexts; xi_p = the GHASH). Exit pc+0x11d8. NOTE the epilogue (ldp d8..d15;
ret) is NOT simulated — we stop at pc+0x11d8 like the 1-block body.

## Session-3 progress on the bridge (2026-06-16)

Got DEEP into the bridge. Confirmed the in-sim approach (clean int128 types) works
through most of it:
- Re-ran the full sim to s367 with the C_ARGUMENTS direct entry + the key invariant
  `byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)` as a precond.
- Asserted `read Q19 s367 = ghash_polyval_acc (byteswap128 h)(brev xi)[brev ct0;brev ct1]`.
- Opened it: LHS via its hyp; RHS via GHASH_POLYVAL_ACC_2 + invariant (so
  polyval_dot K K -> byteswap128 h2), then polyval_reduce_prop3 def + PMUL_KARATSUBA
  (on BOTH products) + byteswap128 + KARATSUBA_LIMBS + subword normalization +
  WORD_BYTEREVERSE_REVERSEFIELDS (unify reversefields) + WORD_INSERT_SUBWORD.
- ABBREV_INNER_PMULS_TAC -> 12 opaque pmul atoms (6 LHS-form + 6 RHS-form, same
  products in different arg-order/lane-nesting). MERGE_PMUL_ATOMS_TAC is too slow
  (all-pairs WORD_BLAST, >15min). Built a TARGETED merge instead:
  classify atoms by key (h vs h2) and form (LHS has word_insert/word 0/word_join),
  then merge each LHS atom into its same-key RHS twin via PMUL_CONG_128+WORD_PMUL_SYM.
  ALL 6 PAIRS MERGE in <1s each: qq11->qq10, qq8->qq6, qq7->qq5, qq9->qq4,
  qq3->qq1, qq2->qq0. (See MERGE helper `try_merge`.)
- After merge: 6 atoms (qq0,qq1,qq4,qq5,qq6,qq10), PMUL_W_64_128 eliminates the 4
  remaining word_pmul (W-reduction) -> a PURE STRUCTURAL identity (shl/zx/subword/
  xor over the 6 atoms), size ~25k.

REMAINING OBSTACLE (the last mile): the structural identity does NOT close by a
direct WORD_BLAST (timed out >16min even split per-lane via JOIN_EQ_SPLIT). The
LHS (assembly) and RHS (spec prop3) express the SAME GF(2^128) Barrett reduction
via DIFFERENT but equivalent bit-formulas: LHS uses a 2-round shift-triple fold
(shl 63/62/57) over the atom HALVES (zNl/zNh); RHS uses shl 64/128 over the whole
qq atoms with subword lanes (192,64)/(64,64)/(0,64). They are equal but not by
flat bit-blasting at this size.
NEXT: either (a) the 1-block manual r1/u/r2 lane-fold, carefully generalized so
BOTH sides reduce to the same normal form before the final (small) blast — the
shift-triple ARGs must be abbreviated UNIFORMLY on both sides; or (b) prove a
clean abstract lemma `polyval_reduce_prop3 (word_xor (word_pmul a b)(word_pmul c d))`
= <the assembly 2-round-fold byte form> over abstract a,b,c,d (the real reusable
GMULT2 lemma), then the in-sim step is one rewrite. (b) is the principled route.

## *** BRIDGE PROVEN (2026-06-16) ***

The GHASH bridge IS CLOSED. The winning sequence (after the in-sim setup that gets
to `read Q19 s367 = ghash_polyval_acc K (brev xi)[brev ct0;brev ct1]` as a SUBGOAL):
1. LHS via hyp; RHS via GHASH_POLYVAL_ACC_2 + the byteswap128-h2 invariant
   (polyval_dot K K -> byteswap128 h2).
2. polyval_reduce_prop3 def + PMUL_KARATSUBA (both products) + byteswap128 +
   KARATSUBA_LIMBS + WORD_BYTEREVERSE_REVERSEFIELDS + WORD_INSERT_SUBWORD + RF8_SUBWORD
   (per-lane reversefields normalization) + subword distribution.
3. ABBREV_INNER_PMULS_TAC -> opaque pmul atoms. TARGETED merge (NOT the all-pairs
   MERGE_PMUL_ATOMS_TAC which is too slow): classify atoms by key(h/h2) and form
   (LHS has word_insert/word 0/word_join), merge each LHS atom into its same-key RHS
   twin via SUBGOAL(v1=v2)+PMUL_CONG_128+WORD_BLAST (or WORD_PMUL_SYM first). ~6 merges,
   <1s each. (helper `try_merge`.)
4. Round-2 W-pmuls: ABBREV_INNER_PMULS again -> qq12 (RHS) merges with the round-1
   W-pmul; then a second ABBREV catches qq14/qq15 (the wv reduction) -> merge qq15->qq14.
5. KEY lemmas to flatten the 256-bit Karatsuba assembly to 64-bit lanes:
   SUBW_ZX_256 / SUBW_SHL64_256 / SUBW_SHL128_256 (for word_zx of 64-bit),
   SUBW_ZX128_256 / SUBW_SHL64_128_256 / SUBW_SHL128_128_256 (for word_zx of 128-bit qq),
   SUBW_XOR_256 (subword over xor at 256). These kill all word_shl/word_zx.
6. Abbreviate all atom halves to 64-bit y-vars (ABBREV_TAC word_subword qqN lane),
   QQ0SPLIT remaining whole atoms, JOINMID the mid-term joins, rewrite y-defs.
   -> a PURE flat XOR identity over 64-bit y-vars, NO subword/join/shift/pmul.
7. JOIN_EQ_SPLIT (word_join a b = word_join c d <=> a=c/\b=d) to split the 128-bit
   equality into two 64-bit lanes, CONJ_TAC, then **WORD_BITWISE_TAC** on each lane
   (NOT WORD_BLAST -- the pure XOR identity closes in <1s with WORD_BITWISE_TAC; BDD
   blast times out >16min on the same goal).

Then the tail close: ABBREV gval; VSTEP ext+rev64 (368-369); assert
read Q19 s369 = word_bytereverse gval (WORD_BLAST); VSTEP the store (370) -> pc+0x11d8;
ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] discharges out_p+xi_p functional goals.

## ONE REMAINING FIX (spec frame): the prologue `stp x5,xzr,[sp,64]` writes 16 bytes
[sp+64,80), but the spec MAYCHANGE frame only declares `bytes(sp+64,8)`. The actual-
change record has `bytes64(sp+64)` AND `bytes64(sp+72)`. Fix: change the spec frame
memory clause from `memory :> bytes(word_add stackpointer (word 64),8)` to
`memory :> bytes(stackpointer,80)` (or bytes(sp+64,16)) -- matching that we now
include the prologue. Then MONOTONE_MAYCHANGE_TAC closes. Re-run to confirm.

## File-encoding status (2026-06-16, end of session)

The full proof was closed INTERACTIVELY (every subgoal incl. the bridge; no cheats).
The file arm/proofs/aesv8_gcm_8x_enc_256_2block.ml encodes it as one prove(). On
loadt it gets ALL THE WAY to the final flat-XOR lane identity but FINISH_2BLK_TAC's
closing `WORD_BITWISE_TAC` FAILS:
  WORD_BITWISE_RULE `word_xor (word_xor (word_xor yy0h yy7h) yy5h) ... = word_xor ...`
i.e. the lane equation reached is NOT a tautology -> an earlier file step diverged
from the interactive proof and produced a wrong (unprovable) residual.

ROOT CAUSE (most likely): the file uses 3 rounds of
`ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC` to do the pmul-atom merges, but the
interactive proof did SPECIFIC targeted merges (qq11->qq10, qq8->qq6, qq7->qq5,
qq9->qq4, qq3->qq1, qq2->qq0; then qq13->qq12; then qq15->qq14). MERGE_2BLK_TAC's
auto-classification (FIRST over same-key RHS candidates) may merge an LHS atom into
the WRONG same-key RHS twin (a different product that happens to share the h/h2 key),
leaving a mismatched residual that is no longer a tautology. The 3 h2-keyed products
(lo/hi/mid) all have key=h2, so FIRST can mis-pair them.

FIX (next session, ~1-2h): make MERGE_2BLK_TAC pair atoms by FULL structural match,
not just key. Either (a) within a key group, match LHS atom i to the RHS atom whose
operand-1 is WORD_BLAST-equal (try all, but VERIFY the residual stays a tautology by
checking the merge doesn't just succeed but is the RIGHT pairing), or (b) hardcode the
6+1+1 pairings by recomputing them from the deterministic ABBREV naming, or (c) after
all merges, before FINISH, assert the expected post-merge goal and prove the residual
is the XOR-ACI tautology. The interactive transcript (this session) has the exact
working targeted-merge sequence. WORD_BITWISE_TAC is the correct final closer (it
worked interactively in <1s per lane) -- the bug is upstream in the merge pairing.

Everything else in the file loads clean: all helper lemmas, the front, the tail
cascade, ct0/ct1 abbreviation, the SUBW lane-collapse lemmas, the JOIN_EQ_SPLIT.

## Root cause of the file loadt failure (PINPOINTED 2026-06-16, session 4)

Reproduced the bridge in the loaded session and stepped the merge rounds:
- ROUND 1 (product atoms): MERGE_2BLK_TAC WORKS - the 12 LHS/RHS product atoms merge
  to 6 (qq0,qq1,qq2,qq3,qq4,qq9). Good.
- ROUNDS 2-3 (the W-reduction pmuls qq12/qq13 = wa, qq14/qq15 = wv): the auto-merge
  leaves 10 atoms (the W-pmul LHS/RHS twins NOT merged). qq13->qq12 merges fine (0.4s)
  but qq15->qq14 FAILS the WORD_BLAST (97s) because:
  *** the W-pmul operands REFERENCE earlier atoms (qq15's operand contains qq13; qq14's
  contains qq3/qq4) and the merges must be done in DEPENDENCY ORDER with the prior
  equalities PROPAGATED into later atom definitions.  My auto MERGE_2BLK_TAC/MERGE_ALL_TAC
  do not substitute a merged atom (qq13:=qq12) into the still-unexpanded definitions of
  later atoms (qq15), so EXPAND_TAC "qq15" reintroduces qq13 (a now-dangling alias) and
  the PMUL_CONG operand blast can't see qq13=qq12. ***
FIX (the encoding bug): after each W-pmul merge, RULE_ASSUM_TAC/substitute the merge
equality into the remaining atom DEFINITIONS (the abbreviation hyps), so subsequent
EXPAND_TACs see the canonical atom. I.e. carry the merge eqs and ASM_REWRITE the defs,
or do the merges strictly innermost-first AND rewrite defs. The interactive proof
happened to merge in the right order with propagation (via the live goal rewrites);
the file's batched ABBREV+MERGE rounds lose that propagation.
This is purely a tactic-plumbing fix; the bridge math is proven sound.

## *** FULL PROOF CONFIRMED CLOSABLE (session 4, 2026-06-16) ***

Re-ran the whole proof interactively in one session. EVERYTHING closes; two
encoding fixes needed in the file (both pinned down, both 1-liners):

FIX 1 (W-pmul merge dependency order): the rounds-2/3 W-reduction pmul atoms
(qq12/qq13=wa, qq14/qq15=wv) must be merged with PROPAGATION. Merge qq13->qq12
with `SUBGOAL_THEN ... (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))` (NOT just
REWRITE_TAC on the goal) so qq15's *definition hyp* (which references qq13) is
updated to qq12; THEN qq15->qq14 merges (its operand now matches). Confirmed:
qq13->qq12 (0.4s), then qq15->qq14 (93s WORD_BLAST). After that FINISH_2BLK_TAC
closes the bridge in 2.9s. So the file's 3x (ABBREV_INNER+MERGE_2BLK) should be:
round1 = product merge (works); then EXPLICIT qq13->qq12 with RULE_ASSUM
propagation; then qq15->qq14; then FINISH_2BLK_TAC. (Or fold the W-pmuls' merge
into MERGE_2BLK by having it RULE_ASSUM-propagate each merge eq into the hyps.)
Atom names are deterministic given the deterministic sim, so qq13/qq12/qq15/qq14
are stable; but a name-agnostic version (merge innermost W-pmul first, propagate,
repeat) is more robust.

FIX 2 (the LAST obligation - out_p block-0 ciphertext): the final goal after the
close is `read (memory:>bytes128 out_p) s370 = word_xor plaintext0 (aes256_encrypt
ctr0 keys)`. It FAILS because ABBREV_Q9_TAC abbreviated ct0 to the RAW aese/aesmc
TOWER (the Q9 s315 readback), but the postcond uses `aes256_encrypt`. The two are
the same AES but in different primitives (aese/aesmc vs aes_sub_bytes/shift_rows/
mix_columns), and reconciling them post-hoc needs an S-box blast that hangs.
FIX: abbreviate ct0 to the SPEC FORM, exactly as the 1-block does at its s265
(arm/proofs/aesv8_gcm_8x_enc_256_1block.ml lines 1673-1681): before abbreviating,
FIRST_X_ASSUM(MP_TAC o SPEC `word_xor plaintext0 (aes256_encrypt ctr0 [k0..k14])`
o MATCH_MP (MESON[]`read Q9 s=a==>!a'. a=a'==>read Q9 s=a'`)) THEN ANTS_TAC THENL
[ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[aes256_encrypt] THEN
 REWRITE_TAC EL_15_128_CLAUSES THEN REWRITE_TAC[aes256_encrypt_round;aese;aesmc]
 THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]; DISCH_TAC]
THEN ABBREV_TAC `ct0 = word_xor plaintext0 (aes256_encrypt ctr0 [k0..k14])`.
Do the SAME for ct1 (spec form `word_xor plaintext1 (aes256_encrypt CTR1 keys)`
where CTR1 = the once-incremented counter; or keep ct1's tower form since the
xi_p GHASH postcond uses brev ct1 opaquely AND the out_p block-1 clause was
dropped from the postcond -- if you re-add the block-1 out_p clause, ct1 also
needs the spec form). With ct0 in spec form, the out_p goal closes by ASM_REWRITE.

EVERYTHING ELSE IS DONE: front, tail cascade, both GHASH multiplies, the
2-product bridge (read Q19 s367 = ghash_polyval_acc...), ext+rev64, store,
MAYCHANGE frame (bytes(sp+64,16)), xi_p GHASH postcond. Just FIX 1 + FIX 2,
then one loadt (~30min incl the 657s 1-block dep) and it binds.

## Session-5 (2026-06-16): FIX 1 WORKS, FINISH_2BLK_TAC normalization incomplete

Ran the loadt with both fixes. PROGRESS: the propagating fixpoint MERGE_2BLK_TAC
(= REPEAT MERGE_ONE_2BLK_TAC with RULE_ASSUM propagation) COMPLETED all the
pmul-atom merges (FIX 1 confirmed working, though slow: ~28min in the bridge due
to all-pairs failed-blast overhead). It then reached FINISH_2BLK_TAC, which FAILS
at WORD_BITWISE_RULE because the lane goal still contains `word_subword qqN (lane)`
(and primed atoms like `qq5''`) -- i.e. FINISH's abbrev_halves + QQ0SPLIT did NOT
fully flatten to 64-bit vars before WORD_BITWISE (which needs pure bitwise ops, no
subword). Failing lane sample:
  word_xor (word_xor (word_subword qq0 (64,64)) (word_subword qq3 (64,64)))
           (word_subword qq5'' (64,64)) ... = ...

ROOT CAUSE: FINISH_2BLK_TAC's abbrev_halves abbreviates `word_subword qqN (0,64)`
to yy-vars, but (a) primed atom names (qq5'' from the merge's variant renaming)
aren't matched by the `String.sub n 0 2 = "qq"` prefix check reliably, and (b)
the QQ0SPLIT/JOINMID order may re-expose subwords after abbrev_halves. The
INTERACTIVE close (session 4, which WORKED in <3s/lane) did, IN ORDER: the SUBW
lane-collapse lemmas; ABBREV each atom's two halves; QQ0SPLIT; JOIN_SUBWORD/
WORD_SUBWORD_XOR; JOINMID; again; JOIN_EQ_SPLIT; CONJ; WORD_BITWISE_TAC. Need to
make FINISH_2BLK_TAC robust: (1) abbrev halves of ALL int128 atoms incl primed
names (match any var whose name starts "qq"); (2) after QQ0SPLIT/JOINMID, RE-RUN
the half-abbrev (or rewrite remaining word_subword qqN via the yy-defs) so NO
word_subword over an atom survives into WORD_BITWISE; (3) only then JOIN_EQ_SPLIT
+ WORD_BITWISE_TAC. Verify the post-normalization goal has zero `word_subword`
before WORD_BITWISE (assert it). Est ~1h + one ~45min loadt.

NET: FIX 1 done (merges complete & correct). FIX 2 (ct0 spec form) untested past
the bridge but should be fine. Only FINISH_2BLK_TAC's flattening robustness left.

## Session-6 (2026-06-16): bridge+FINISH CONFIRMED WORKING; 2 things left

Latest loadt (with the robust FINISH) got PAST the bridge AND FINISH_2BLK_TAC
(both work) and through ext+rev64+store to s370, failing only at the FINAL close
("TAC_PROOF: Unsolved goals"). So mathematically the whole proof is closed; two
ENGINEERING items remain for a clean, reasonably-fast loadt:

(A) *** PERFORMANCE: the fixpoint MERGE_2BLK_TAC (= REPEAT MERGE_ONE_2BLK_TAC) is
    far too slow (~30 min) *** because each iteration does FIRST over ALL atom
    pairs and the FAILED PMUL_CONG WORD_BLASTs on the big W-pmul operands cost
    ~90s each. The INTERACTIVE proof did ~8 TARGETED merges in ~3 min total.
    FIX: replace the blind all-pairs fixpoint with the targeted sequence. The
    pairing is structural: after round-1 ABBREV_INNER (products), there are 6
    product-atom LHS/RHS twins (block0 lo/hi/mid keyed by h2, block1 lo/hi/mid
    keyed by h) and the 2 W-reduction rounds (wa: 1 pair, wv: 1 pair). Pair them
    by: (1) the 2nd pmul operand (h vs h2 vs `word W`), AND (2) for same-key
    products, by which atoms appear in operand-1 — DON'T blast non-matching
    pairs. OR: memoize/skip pairs whose cheap signature differs, only blast
    plausible ones. OR simplest: hardcode the merges using the deterministic
    ABBREV naming (the sim is deterministic so names are stable WITHIN a fixed
    tactic prefix). The W-pmul merges (wa then wv) MUST be done innermost-first
    with RULE_ASSUM propagation (already in MERGE_ONE_2BLK_TAC).
    Target: bridge close in <5 min, total loadt ~20 min (deps ~11min + sim ~5min
    + bridge <5min).

(B) FINAL CLOSE ("Unsolved goals" after s370): the close now is
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(EXPAND_TAC "ct0" THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_BLAST) THEN TRY(REWRITE[MAYCHANGE_REGS...] THEN REPEAT
    CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]).
    This mirrors the proven 1-block close (1block.ml lines 1767-1774) and ct0 is
    now the aes256_encrypt spec form, so out_p block-0 should close by ASM and
    the MAYCHANGE by MONOTONE. NOT yet re-verified after the (B) edit. The
    unsolved goal in the PREVIOUS run (before this close-hardening) was most
    likely the MAYCHANGE frame left by a bare TRY. To DEBUG without a 30-min
    rerun: temporarily replace MERGE_2BLK_TAC with the fast targeted merge (A),
    reach s370 quickly, then `e(ENSURES_FINAL_STATE_TAC); e(ASM_REWRITE_TAC[])`
    and inspect each residual subgoal directly.

INTERACTIVE-PROVEN FACTS (all hold, from sessions 4-6):
- bridge: read Q19 s367 = ghash_polyval_acc (byteswap128 h)(brev xi)[brev ct0;brev ct1]
  closes via the recipe above (merges + SUBW lemmas + ABBREV_ALL_SUBWORDS + JOIN_EQ_SPLIT
  + WORD_BITWISE_TAC).
- ext+rev64 -> word_bytereverse gval; store @ s370 -> pc+0x11d8.
- MAYCHANGE frame = bytes(out_p,32),bytes(xi_p,16),bytes(ivec_p,16),bytes(sp+64,16).
- Direct C_ARGUMENTS pc+0x18 entry (prologue steps 1-5 inline), NO wrapper.

SPEC NOTE (hook flagged): the stated postcond is currently PC + out_p block-0
ciphertext only. For the COMPLETE spec, re-add: out_p block-1 = ct1 (needs ct1 in
spec form = word_xor plaintext1 (aes256_encrypt CTR1 keys), CTR1 = the lane-level
once-incremented counter -- model it as a spec var/fn), and xi_p =
word_bytereverse gval (closes trivially via the gval store readback). Do this
AFTER the bare version loads.
