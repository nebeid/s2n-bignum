# HOL Light Proof Tips for s2n-bignum

Tips combined by kiro-cli (Claude Opus 4.6) in the same session after the proof of ciphertext-stealing safety in encrypt (producing it and correcting it together) from [Appendix B. HOL Light Tips: Verifying AES-XTS encrypt and decrypt with HOL Light](https://quip-amazon.com/ec1HA42xAjWe#temp:C:cUT48ecd0975be6480295c895f63) and [My HOL Light questions](https://quip-amazon.com/RlC4AMTMDMZx). Tips from June’s materials docs (md files) that are in https://github.com/aqjune/hol-light-materials are appended.

## Assumptions and Automatic Tactics

1. `ARITH_TAC` looks at the goal only, so bring assumptions as antecedents using `UNDISCH_TAC` (or `SUBGOAL_THEN <...> MP_TAC` to prove something first)
2. `ASM_ARITH_TAC` uses assumptions but sometimes gets lost/hangs (especially with many `val(...)` terms). Try manually bringing specific assumptions into the goal with `UNDISCH_TAC` + `ARITH_TAC`
3. `BITBLAST_TAC` always looks at assumptions, so to focus it, use a lemma to prove what you want it to focus on
4. Eagerly abbreviate `val` of words with `ABBREV_TAC `my_xx = val xx`` before main s2n-bignum tactics. `SIMPLE_ARITH_TAC` (used internally) filters out `val ...` assumptions, so abbreviations help it run smoothly

## `SUBGOAL_THEN` Variants

* `SUBGOAL_THEN term ASSUME_TAC`: prove and add as assumption
* `SUBGOAL_THEN term MP_TAC`: prove and add as antecedent of goal
* `SUBGOAL_THEN term SUBST1_TAC`: prove and substitute once in goal
* `SUBGOAL_THEN term SUBST_ALL_TAC`: prove and substitute in both assumptions and goal
* `SUBGOAL_THEN term STRIP_ASSUME_TAC`: prove and split conjunctions into separate assumptions

## Case Splits

* `ASM_CASES_TAC term`: two cases based on `term` and `~term`
* `COND_CASES_TAC`: two cases based on the first `if` condition in the goal
* `EQ_TAC`: breaks apart `<=>` into two subgoals

## Induction

* `LIST_INDUCT_TAC`: first universally quantified variable must be a list
* `INDUCT_TAC`: first universally quantified variable must be a `num`
* `WF_INDUCT_TAC term`: doesn't require quantification

## Quantifiers

* `GEN_TAC`: removes universal quantifier
* `SPEC_TAC`: adds universal quantifier
* `LEFT_IMP_FORALL_THM`: converts between `(forall x. P x) ==> Q` and `(exists x. P x) ==> Q` — useful when `IMP_REWRITE_TAC` generates unwanted universal quantifiers

## Rewrites

* `REWRITE_TAC`: for unconditional equalities `A = B`
* `ASM_SIMP_TAC`: for conditional rewrites `P ==> A = B` where `P` can be auto-discharged from assumptions
* `IMP_REWRITE_TAC`: for conditional rewrites where you want to see/prove the side conditions explicitly
* `GEN_REWRITE_TAC` with conversionals for controlled rewriting of subterms, e.g. `GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_XOR_SYM]`
* `GSYM` with assumptions: `REWRITE_TAC[GSYM (ASSUME `A = B`)]` rewrites `B` to `A`
* Expand `let`: `REWRITE_TAC[LET_DEF; LET_END_DEF]`
* Reduce to numbers: `CONV_TAC NUM_REDUCE_CONV`

## Word Arithmetic and Cutoff Subtraction

* `word_sub` / natural number subtraction mixing is a common pain point. `curr_len - 0x10` can truncate to `0` if `curr_len < 16`
* Canonicalize `word_sub` expressions early:

```
  SUBGOAL_THEN
    `word_sub (word_add ctxt_p (word curr_len)) (word 0x10):int64 =
     word_add ctxt_p (word(curr_len - 0x10))`
    SUBST_ALL_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[GE]) THEN
     ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE;
     RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))]
```

* Simplify `curr_len - 0x10 + 0x10 = curr_len` using `UNDISCH_TAC `0x10 <= curr_len` THEN ARITH_TAC` (not `ASM_ARITH_TAC` which may hang)
* For conditional arithmetic: `ASM_SIMP_TAC[ADD_ASSOC; ARITH_RULE `~(val x < 0x10) ==> val x - 0x10 + 0x10 = val x`]`
* `WORD_RULE` cannot handle natural number subtraction inside `word(... - ...)` — need precondition + `WORD_SUB` first

## Converting Between Word and `val` Forms

* Pattern: `ONCE_REWRITE_TAC[GSYM VAL_EQ]` → `REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64]` → `IMP_REWRITE_TAC[MOD_LT]`
* Key theorems: `VAL_EQ`, `VAL_WORD_ADD`, `DIMINDEX_64`, `MOD_LT`, `VAL_WORD_SUB_CASES`
* `BITBLAST_RULE` for word operations / bit-level reasoning when `ARITH_RULE` fails. Use `BITBLAST_RULE` when the goal involves `ival`, `word_sub`, or signed word comparisons; use `ARITH_RULE` for pure `num`/`int` arithmetic without word types
* `EQ_IMP_RULE`: create two rules from an `iff` rule

## Signed/Unsigned (`ival`/`val`) Reasoning

* `ival` is signed interpretation, `val` is unsigned
* For small values (< `2^63`), `ival (word n) = &n` — prove via `REWRITE_TAC[ival]` then show value is below threshold
* Branch condition proofs mixing `ival` and `val` are nasty — for small ranges (< `16`), John suggests explicit enumeration with `EXPAND_CASES_CONV`

## Applying Lemmas

* For lemmas that can't be applied with `MATCH_MP_TAC`: use `MP_TAC` + `SPEC`/`SPECL` to attach to goal antecedent, then `ASM_SIMP_TAC[]` or `ANTS_TAC` to discharge preconditions, then `DISCH_TAC` to push result into assumptions
* `DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS)` — elegant way to rewrite all assumptions with a discharged theorem (John Harrison)

## Keeping Assumptions After Using Them

```
UNDISCH_THEN `assumption`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]
    THEN ASSUME_TAC th)
```



## `ENSURES` Tactics

* `ENSURES_SEQUENCE_TAC`: always put all useful assumptions into the term — they may get discarded later
* `ENSURES_FRAME_SUBSUMED`: use when `MAYCHANGE` clauses fail because memory length is parameterized and only partially written. Introduces manual proof that partial write subsumes whole region
* `ARM_ADD_RETURN_STACK_TAC`: helps automatically add back preserved registers saved in stack. `~pre_post_nsteps:(n, n)` for manual step counts

## `nonoverlapping`

* Prefer `nonoverlapping` (word-based) over `nonoverlapping_modulo` (numeric) form
* Avoid `NONOVERLAPPING_CLAUSES` rewrite early — it creates `2 EXP 64` redexes that confuse automation
* To convert back: `RULE_ASSUM_TAC(REWRITE_RULE[GSYM DIMINDEX_64; NONOVERLAPPING_MODULO]) THEN RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_64; WORD_VAL])`

## Debugging

* `components_print_log := true;;` — logs `nonoverlapping` predicates during ARM simulation
* `arm_print_log := true;;` — logs ARM stepping details
* `safety_print_log := true;;` — logs safety property discharge details
* Hex output:

```
let pp_print_num_hex fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n) in
install_user_printer("pp_print_num", pp_print_num_hex);;
```

or simply (because the first 3 lines are in `arm/proofs/utils.ml`:

```
needs "arm/proofs/utils.ml";;
install_user_printer("pp_print_num", pp_print_num_hex);;
```

* Back to decimal: `delete_user_printer "pp_print_num";;`

## Safety Proof Specific

* `DISCHARGE_SAFETY_PROPERTY_TAC` needs clean variable names — local abbreviations like `l1_curr_len` must be expanded back before calling
* Use `~abbrevs_unfold_before_f_events_tac:[...]` parameter to expand abbreviations before event unification
* Flatten nested `word_add` before discharging: `REWRITE_TAC[WORD_RULE `!a b c. word_add (word_add (a:int64) (word b)) (word c) = word_add a (word (b + c))`]`
* `ENSURES_EVENTS_WHILE_UP2_TAC` backedge PC should be the instruction *after* the branch (fall-through address), not the branch instruction itself

* * *
Adding June’s materials docs (md files) that are in https://github.com/aqjune/hol-light-materials


## Searching for Theorems

* `search [`pattern1`; `pattern2`]` — find theorems containing all given subterms
* `search [name "ASSOC"]` — find theorems with "ASSOC" in their name
* `search [`pattern`; name "MOD"]` — combine pattern and name filters
* Also grep `Library/words.ml` for word-related definitions and lemmas

## Named vs Unnamed Assumptions

* `NAME_ASSUMS_TAC` — label all assumptions as `H0`, `H1`, ...
* `INTRO_TAC "Hname"` — name an assumption while introducing it (like Coq's `intro`)
* `USE_THEN "H" MP_TAC` — pick named assumption and add as antecedent
* `REMOVE_THEN "H" ttac` — pick, use, and remove named assumption
* `UNDISCH_THEN` — pick unnamed assumption by its term and use it
* For unnamed style, `ASM_REWRITE_TAC[]` uses all assumptions; `FIRST_X_ASSUM` picks the first matching one

## Custom Utility Tactics

* Rewrite assumptions using one assumption:

```
  let REWRITE_ASSUMES_TAC (t:term) =
      UNDISCH_THEN t (fun thm → RULE_ASSUM_TAC (REWRITE_RULE [thm]) 
      THEN ASSUME_TAC thm);;
```

* `note` tactic for adding derived facts:

```
  let note t why = SUBGOAL_THEN t MP_TAC THENL
    [ASM_MESON_TAC why; DISCH_THEN(fun th → ASSUME_TAC th)];;
  (* usage: note 1 + 2 = 2 + 1 [ADD_SYM] THEN ... *)
```



## Controlled Rewriting with `GEN_REWRITE_TAC`

* `LAND_CONV` — rewrite left argument of binary operator
* `RAND_CONV` — rewrite right argument (or operand of any application)
* `RATOR_CONV` — rewrite the operator `f` in `f x`
* `PAT_CONV `\x. x + a = b`` — rewrite at positions matching a pattern
* `PATH_CONV "lrl"` — navigate to subexpression via `l`(operator)/`r`(operand)/`b`(body)
* Compose with `o`: `LAND_CONV o RAND_CONV` for nested positions
* Add recursive traversal: `DEPTH_CONV o (PAT_CONV ...)` for bottom-up, `ONCE_DEPTH_CONV` for single pass
* `DEPTH_BINOP_CONV `(/\)`` — traverse only through a specific binary operator

## Deriving Rewrite Rules On-the-fly

* `GSYM thm` — reverse an equality `A = B` to `B = A`
* `TRANS thm1 thm2` — chain `A = B` and `B = C` into `A = C`
* `MATCH_MP thm1 thm2` — modus ponens: from `P ==> Q` and `P`, get `Q`
* `SPEC `term` thm` / `SPECL [`t1`; `t2`] thm` — specialize universally quantified variables
* `REWRITE_RULE[rules] thm` — rewrite within a theorem
* `NUM_REDUCE_CONV `1 + 2`` — evaluate to `|- 1 + 2 = 3`
* `REWRITE_CONV[rules] `term`` — create rewrite rule from other rules

## Conditional Rewrite Strategies

* `IMP_REWRITE_TAC[rule]` — rewrite and leave preconditions as conjuncts to prove later. Good when multiple matches need different specialized preconditions
* `SEQ_IMP_REWRITE_TAC[rules]` — like `IMP_REWRITE_TAC` but order-sensitive
* `CASE_REWRITE_TAC[rule]` — case-splits on precondition: generates `(P ==> Q') /\ (~P ==> Q)`
* `ASM_SIMP_TAC[rules]` — proves preconditions from assumptions first, then rewrites. Use when assumptions already contain what's needed

## Conversions as Rewrite Rules

* `CONV_TAC (LAND_CONV NUM_REDUCE_CONV)` — evaluate LHS of equality
* `CONV_TAC NUM_REDUCE_CONV` — evaluate numerical expressions everywhere
* `CONV_TAC MOD_DOWN_CONV` — push `MOD` inward
* `WORD_REDUCE_CONV` — evaluate word expressions

## Destructuring and Pattern Matching

* `DISJ_CASES_TAC(SPEC `x` num_CASES)` — destruct `num` as `0` or `SUC n`
* `CONJUNCTS thm` — split conjunction into list of theorems
* `CONJUNCT1 thm` / `CONJUNCT2 thm` — extract first/rest of conjunction
* `SPEC`/`SPECL` + `CONJUNCT1`/`CONJUNCT2` — extract and specialize parts of compound theorems


## ARM_VSTEPS_TAC: Simplifying at Intermediate Points

When ARM simulation produces expressions that grow too large for WORD_BLAST (e.g., memory stores followed by many steps), use `ARM_VSTEPS_TAC` for a small window around the critical point to keep intermediate register hypotheses alive.

**The problem**: `ARM_STEPS_RESOLVE_TAC` runs CLARIFY_TAC after each step, which substitutes register values into the goal and discards them. After 20+ steps, memory read-back expressions become tens of thousands of characters — too large for WORD_BLAST.

**The solution**: Use VSTEPS for a small window (2–8 steps) around the store instruction, then assert the memory value equals the spec using `SUBGOAL_THEN ... ASSUME_TAC` + `ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST`. The clean hypothesis then propagates through subsequent `ARM_STEPS_RESOLVE_TAC` calls.

**Pattern**:
```ocaml
(* Steps before the critical window *)
ARM_STEPS_RESOLVE_TAC EXEC (266--324) THEN DISCARD_COUNTER_REGS_TAC THEN
(* VSTEPS for the store window — keeps register hypotheses alive *)
ARM_VSTEPS_TAC EXEC (325--332) THEN
(* Assert the memory value while expressions are still small *)
SUBGOAL_THEN `read (memory :> bytes128 out_p) (s332:armstate) = spec`
  ASSUME_TAC THENL
[ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
(* Continue with ARM_STEPS_RESOLVE — the clean hypothesis propagates *)
ARM_STEPS_RESOLVE_TAC EXEC (333--352) THEN ...
```

**Key points**:
- VSTEPS is slow with many hypotheses. Discard unneeded registers before VSTEPS, or keep the window small (≤8 steps).
- VSTEPS doesn't handle D-register instructions (INS/MOV element). Use ARM_STEPS_RESOLVE for those, then switch to VSTEPS after.
- The technique is used in `bignum_montmul.ml`, `bignum_modinv.ml`, and the AES-GCM proof.
- Only ~8 proofs in s2n-bignum use VSTEPS — it's a specialized technique for when expressions blow up.
- The number of VSTEPS could be smaller (even 2–4 steps) — you only need the window from just before the store through the store itself. 8 steps was used because it's fast (<1s) and gives margin.

## GHASH/Polynomial Multiplication Closure Pattern

For proofs involving GHASH (carry-less multiplication + polynomial reduction), the closure tactic after ARM simulation is:

```ocaml
(* Expand the spec to match assembly structure *)
REWRITE_TAC[ghash_polyval_acc; polyval_dot; polyval_reduce_prop3; PMUL_KARATSUBA] THEN
CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
(* Abbreviate word_pmul terms (WORD_BLAST can't handle them) *)
ABBREV_ALL_PMUL_TAC THEN
(* WORD_BLAST handles the remaining XOR/join/subword structure *)
CONV_TAC WORD_BLAST
```

Where `ABBREV_ALL_PMUL_TAC` abbreviates all `word_pmul` subterms of type `:128 word`:
```ocaml
let ABBREV_ALL_PMUL_TAC =
  let pmul_tm = `word_pmul` in
  fun (asl,w) ->
    let pmuls = find_terms (fun t ->
      try fst(strip_comb t) = pmul_tm && type_of t = `:128 word`
      with _ -> false) w in
    let unique_pmuls = setify pmuls in
    let n = ref 0 in
    let tacs = List.map (fun t ->
      incr n;
      ABBREV_TAC (mk_eq(mk_var("pmul_"^string_of_int !n, type_of t), t))
    ) unique_pmuls in
    (EVERY tacs) (asl,w);;
```

**Key insight**: The assembly uses Karatsuba multiplication (3 half-size pmulls) while the spec uses a single full `word_pmul`. Rewriting with `PMUL_KARATSUBA` (from `common/karatsuba_pmul.ml`) bridges this gap. After abbreviating all `word_pmul` terms, both sides have the same structure and WORD_BLAST resolves the equality.

**Precondition**: The htable's Karatsuba middle key must be constrained:
```
word_subword hk (0,64) :64 word = word_xor (word_subword h (0,64)) (word_subword h (64,64))
```
