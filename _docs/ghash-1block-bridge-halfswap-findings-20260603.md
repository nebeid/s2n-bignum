# 1-block GHASH bridge — SOLVED the s348 bridge (2026-06-03 late)

## ★ BREAKTHROUGH (supersedes the "lane-swap" analysis below, which was based on a
## MIS-EXTRACTED operand — that block_a was NOT the real GHASH operand).

VERIFIED by numeric eval AND proved as an isolated lemma (no cheat, ~100s WORD_BLAST):
```
read Q19 s348  =  polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse ct))
                              (byteswap128 h)
```
i.e. the block is the PLAIN spec block `blk_plain = word_xor (brev xi)(brev ct)` (NOT
lane-swapped), and the GHASH key is **`byteswap128 h`** (the htable h, byteswapped — exactly
the standalone gcm_gmult_v8 convention which used `b := byteswap128 h`).

### The isolated bridge proof that WORKS (reproduce in ~2 min once at s348):
Goal: `abs_lhs = polyval_dot blk_plain (byteswap128 h)` (abs_lhs = read Q19 s348, ct->cc).
1. `GEN_REWRITE_TAC RAND_CONV [GSYM (REWRITE_RULE[LET_DEF;LET_END_DEF]
      (ISPECL [blk_plain; \`byteswap128 h\`] GMULT_FULL_CORRECT_BA))]`
2. `REWRITE_TAC[byteswap128]` then `REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD]`
   + inline subword-over-xor/join distribution lemma (BITBLAST) + `WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES`.
3. Abbreviate the 3 innermost pmuls r0,r1,r2 (ABBREV_TAC on programmatically-EXTRACTED terms —
   hand-written operands fail on word_join width typing).  Now BOTH sides are in r0,r1,r2.
4. Prove r0=P0, r1=P1, r2=P2 (P_i = the RHS GMULT pmuls) via a typed `pmul_cong`
   (`a=c/\b=d ==> word_pmul a b:int128 = word_pmul c d`):
   `EXPAND_TAC "r_i" THEN GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN MATCH_MP_TAC pmul_cong
    THEN CONJ_TAC THEN CONV_TAC WORD_BLAST`.  Then `REWRITE_TAC[GSYM these]`.
5. Clean `word 0` noise (WORD_XOR_0 + subword-of-0 BITBLAST lemmas).
6. Abbreviate the inner W-reduction pmul `wa = pmul (subword r1 (0,64)) W`.  Prove the two
   outer wv pmuls equal via pmul_cong+WORD_BLAST, ASM_REWRITE.  Abbreviate the wv pmul.
7. `CONV_TAC WORD_BLAST` — closes (~100s).  NO subgoals.

### CONFIRMED WORKING CLOSE (No subgoals, reproduced 3×)
The bridge `read Q19 s348 = polyval_dot (word_xor (brev xi)(brev ct)) (byteswap128 h)` closes
with this sequence. CRITICAL: apply the GSYM GMULT rewrite as its OWN tactic step first
(in a single mega-THEN chain it intermittently no-ops — apply separately or it's the head of
the chain that must land). Helper tactics/lemmas needed in preamble:
- `PMUL_CONG_128 = prove(\`!a b c d:64 word. a=c/\b=d ==> (word_pmul a b:int128)=word_pmul c d\`, ...)`
- `SUBWORD_XOR_JOIN_DIST` (the 4-way subword-over-xor/join distribution, BITBLAST)
- `SUBWORD0_LEMMAS` (word_subword (word 0) (k,64) = word 0, BITBLAST)
- `ABBREV_INNER_PMULS_TAC` (abbrev all currently-innermost 2-arg word_pmuls to fresh qqN;
  scan ALL hyp+goal frees for used names)
- `MERGE_PMUL_ATOMS_TAC` (for each pair of pmul-atom defs, try prove v1=v2 via EXPAND+
  PMUL_SYM(LAND)+MATCH_MP PMUL_CONG_128+WORD_BLAST, as in-context SUBGOAL_THEN, rewrite)
- `ABBREV_WA_TAC` (abbrev the innermost `pmul (subword _ (0,64)) (word 0xC2..)` to wa_atom)
- `FINISH_WV_TAC` (if exactly 2 pmuls remain, prove equal via PMUL_CONG_128+WORD_BLAST then
  CONV_TAC WORD_BLAST; else just WORD_BLAST)

Sequence (~135s, dominated by 2 WORD_BLASTs):
```
GEN_REWRITE_TAC RAND_CONV [GSYM(REWRITE_RULE[LET_DEF;LET_END_DEF]
  (ISPECL [<blk_plain>; \`byteswap128 h\`] GMULT_FULL_CORRECT_BA))] THEN  (* SEPARATE step *)
REWRITE_TAC[byteswap128] THEN
REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
ABBREV_INNER_PMULS_TAC THEN MERGE_PMUL_ATOMS_TAC THEN
REWRITE_TAC[WORD_XOR_0; SUBWORD0_LEMMAS] THEN REWRITE_TAC[WORD_XOR_0] THEN
ABBREV_WA_TAC THEN FINISH_WV_TAC
```

### REMAINING to finish the whole theorem
The s348 value is `polyval_dot blk_plain (byteswap128 h)`.  Spec stores
`word_bytereverse(ghash_polyval_acc h (brev xi)[brev ct]) = word_bytereverse(polyval_dot blk_plain h)`.
So we still must reconcile `byteswap128 h` (assembly key) vs `h` (spec key), through the
tail EXT(349)+REV64(350).  Earlier numeric tests of the OLD (wrong) capture don't apply.
NEXT: with the CORRECT s348 value, recompute the tail map and check
`<tail>(polyval_dot blk_plain (byteswap128 h)) =? word_bytereverse(polyval_dot blk_plain h)`.
This is a GHASH bit-reflection identity (byteswap of key ↔ byteswap of result); likely
provable from a `polyval_dot (byteswap128 h)` ↔ `byteswap/reverse (polyval_dot ... h)` lemma,
OR the htable h IS already the twisted key and the spec's h should be byteswap128 h.

---

# (OBSOLETE) earlier half-swap analysis — operand was mis-extracted, IGNORE below
# 1-block GHASH bridge — half-swap root cause PINNED DOWN (2026-06-03)

## Context
Goal: capture the Prop3 stack constant (DONE — it's a precondition, survives to s348 as
`read (memory :> bytes64 (word_add stackpointer (word 64))) s348 = word 13979173243358019584`)
and close the s348 GHASH bridge end-to-end.

## What is verified working (this session)
- Preamble loads (EXEC + all bridge lemmas), 41s. ELF needs ABSOLUTE path (HOL cwd =
  hol-light dir). Preamble split into `_tmp/ghash_preamble_abs.ml`.
- Full simulation runs to **s348** with all clean values:
  - `read Q19 s348` = the assembly Karatsuba+Prop3 GHASH result (20267-char term, NO
    old-state refs — self-contained in xi, ct, h).
  - Prop3 constant present at s348 ✓.  out_p ciphertext asserted at s332 ✓.
- After s348, `DISCARD_OLDSTATE_TAC "s348"` prunes 1357→77 hyps safely (Q19 RHS has no
  old-state refs).  This is REQUIRED before the bridge or ASM_REWRITE over 1357 hyps + a
  big goal makes the close crawl (timed out at 400s/500s twice).

## THE ROOT CAUSE (numerically PINNED, not speculation)
The assembly's GHASH operand at the multiply is the **lane-swap** of the spec block.

Let `blk_plain = word_xor (word_bytereverse xi) (word_bytereverse ct)` (the spec's block,
ct = word_xor plaintext (aes256_encrypt ctr0 [k0..k14])).
Let `block_a` = the operand actually fed to the assembly's pmuls at s348 (extracted
verbatim from `read Q19 s348`):
```
word_xor (word_subword (word_join (word_join (rev8(sub xi 0,64))(rev8(sub xi 64,64)))
                                  (word_join (rev8(sub xi 0,64))(rev8(sub xi 64,64)))) (64,128))
         (word_subword (word_join (rev8 ct)(rev8 ct)) (64,128))
```
PROVEN by WORD_BLAST (both directions, ~1.2s):
- `word_subword block_a (0,64)  = word_subword blk_plain (64,64)`
- `word_subword block_a (64,64) = word_subword blk_plain (0,64)`
i.e. **block_a = lane_swap(blk_plain)** (the two 64-bit halves are swapped).
Also PROVEN FALSE: `block_a = blk_plain` (WORD_BLAST refutes).

### Consequence for the bridge
- Instantiating GMULT_FULL_CORRECT_BA with `a := block_a` makes the LHS pmul operands match
  exactly (good), BUT the Prop3 reduction limb then uses `subword r1 (0,64)` on the
  assembly side vs `subword r0 (0,64)` on the GMULT side (r0 = p_lo, r1 = p_hi).  So the
  reduced results differ — the equation `read Q19 s348 = polyval_dot block_a h` does NOT
  close, because GMULT's reduction reduces the LOW limb (aa = subword p_lo (0,64)) while
  the assembly reduced the limb built from p_hi.  i.e. the assembly's reduction is on the
  lane-swapped limb layout.
- Instantiating with `a := blk_plain` (the file's current target) is the mirror image:
  same r0/r1 mismatch in the opposite direction.

So **neither `polyval_dot block_a h` nor `polyval_dot blk_plain h` matches `read Q19 s348`
by GMULT_FULL_CORRECT_BA directly** — the lemma's lane convention is off by the lane-swap.

## Reduction so far (isolated, fast — reproduce in seconds)
Captured `abs_lhs` = `read Q19 s348` with ct abstracted to fresh `cc:int128`
(frees xi,cc,h).  Then on goal `abs_lhs = polyval_dot block_a h`:
1. `GEN_REWRITE_TAC RAND_CONV [GSYM (ISPECL [block_a; h] GMULT_FULL_CORRECT_BA (LET-reduced))]`
2. `REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD]` + subword-over-xor/join distribution
   lemma (proved inline by BITBLAST) + `WORD_SUBWORD_SUBWORD`.
3. Abbreviate the 6 innermost pmuls (r0..r5) by EXACT extracted terms (ABBREV_TAC on
   programmatically-found subterms — hand-written ABBREV operands FAIL to match due to
   word_join width typing 128 vs 256!).  Goal drops 30k→2.1k chars, 10→4 pmuls.
4. Prove r3=r0, r4=r1, r5=r2 via EXPAND_TAC + `GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM]`
   + REFL (r5=r2 needs an AP_TERM/WORD_BLAST fallback).  ASM_REWRITE eliminates r3,r4,r5.
5. `REWRITE_TAC[byteswap128]`, clean `word 0` noise (WORD_XOR_0 + subword-of-0 lemmas).
6. Abbreviate the 2 inner W-reduction pmuls (s0,s1).  Goal = 1476 chars in r0,r1,r2,s0,s1.

RESULT: LHS uses `s1 = pmul (subword r1 (0,64)) W`; RHS uses `s0 = pmul (subword r0 (0,64)) W`.
Since r0≠r1, the goal is NOT closable — confirming the lane-swap obstruction above.

## NUMERIC GROUND TRUTH (concrete eval via GMULT byte-form + WORD_RED, 2026-06-03)
Used eval_dot(a,h) = reduce(SYM(ISPECL[a;h]GMULT_FULL_CORRECT_BA) with byteswap128 expanded).
lane_swap(x) = `word_subword (word_join x x :(256)word) (64,128)` (CORRECT halfswap — note the
256-bit join; the int128 join truncates and is NOT a swap, a recurring trap).
Concrete: xi=123456789012345, cc=987654321098765, h=5555555555555555.

Ruled out (all FALSE):
- `polyval_dot (lane_swap a) h = polyval_dot a h`
- `polyval_dot (lane_swap a) h = lane_swap (polyval_dot a h)`
- `lane_swap(polyval_dot (lane_swap b) h) = polyval_dot b h`

**Assembly stored value vs spec — THE THEOREM AS WRITTEN DOES NOT HOLD NUMERICALLY:**
Let absv = Q19@s348 = (assembly reduced GHASH) at the concrete inputs.
- `word_bytereverse(absv)` = 195350293995108280929525540631873280  ≠ spec
- spec = `word_bytereverse(polyval_dot (word_xor (brev xi)(brev cc)) h)`
       = 161264276855004937280913922090848317916
- `word_bytereverse(lane_swap absv)` = 161264276855004937**270962356067454503335**
  — TOP bits match spec (161264276855004937...) but LOW ~64 bits differ.  SO CLOSE.
- Tried spec with h replaced by {h, byteswap128 h, brev h, lane_swap h}, with/without outer
  brev — NONE match `word_bytereverse(lane_swap absv)`.

INTERPRETATION: the file currently captures the store as `word_bytereverse(Q19@s348)` via
REV64_LANES_EQ, but the real tail is EXT(349)+REV64(350); the EXT is a lane-swap so the true
store is `word_bytereverse(lane_swap(Q19@s348))` — which matches the spec in the HIGH 64 bits
but not the low.  The residual low-64 discrepancy means there is a FURTHER byte/lane convention
mismatch (likely in how the two GHASH operand lanes (lo vs hi limb) map through the Prop3
reduction's asymmetric treatment, or an off-by-one in which half REV64 hits).  This is a real
spec/lemma-convention bug, NOT a tactic problem.

### CONCRETE NEXT STEP (do this first next session)
Do NOT fold steps 349/350.  Step them with plain ARM_VSTEPS_TAC and READ OFF the exact
symbolic `read Q19 s350` (the true pre-store value).  Compare it structurally to
`word_bytereverse(lane_swap(Q19@s348))` and to the spec RHS.  That pins whether the tail is
byterev∘laneswap or something else, and exactly which lemma (REV64_LANES_EQ vs a new
REV64_EXT8 lemma) the store needs.  THEN re-derive the s348 bridge target to be the value
that, after the TRUE tail map, equals the spec — and prove that bridge with a lane-swap-aware
GMULT instantiation (option A).  The numeric near-match (high 64 bits already correct) says
the fix is small and local once the tail map is read off exactly.

## What this means / next options (pick one)
The half-swap is REAL and at the Karatsuba-limb level, not just byte order.  Options:

(A) **Re-derive GMULT_FULL_CORRECT_BA with a lane-swapped convention** matching the full
    function's INS/EXT lane layout (the 8x function differs from the standalone gcm_gmult_v8
    whose EXT placement gave non-swapped lanes — that's why bck0020 closed with a:=brev xi).
    i.e. prove `GMULT_FULL_CORRECT_BA_SWAPPED: <assembly byte form> = polyval_dot a b` where
    a's lanes are read in the swapped order.  Then instantiate with a:=blk_plain.

(B) **Check steps 349-350 (EXT then REV64) actually do a lane-swap+byterev**, not just
    byterev (REV64_LANES_EQ).  If EXT(349)=halfswap is NOT cancelled, the stored value is
    `word_bytereverse(lane_swap(Q19@s348))` and lane_swap(polyval_dot block_a h) may equal
    polyval_dot blk_plain h.  TEST: don't fold 349/350; track the EXT explicitly.  THIS IS
    THE MOST LIKELY RESOLUTION — the operand lane-swap at the multiply is probably undone by
    the EXT in the tail, so target the bridge at the POST-EXT state (s350) not s348, OR
    target s348 = polyval_dot block_a h (provable once lemma lanes fixed) and let EXT+REV64
    map it to the spec.

(C) Prove `polyval_dot (lane_swap a) h = lane_swap (polyval_dot a h)` (a GHASH lane-swap
    commutation lemma) if true — then reconcile via the tail EXT.  NEEDS CHECKING if true.

## Reproduce
- Preamble: `loadt "_tmp/ghash_preamble_abs.ml"` (abs ELF path).
- Drive main theorem with `g`/`e` from `_tmp/ghash_setgoal.ml` (comment stripped, lines
  315-389 of the .ml as the goal).
- Sim to s348: the file's tactic lines 390-466 verbatim (the ARM_VSTEPS_FOLD 333-348 takes ~96s).
- Then `DISCARD_OLDSTATE_TAC "s348"` before any bridge attempt.

No CHEAT_TAC introduced anywhere.  File unchanged except this is all interactive.
