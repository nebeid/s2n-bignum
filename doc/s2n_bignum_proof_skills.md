# s2n-bignum Proof Skills — Crypto Verification

Project-specific proof techniques for s2n-bignum cryptographic proofs.
Supplements the HOL Light MCP SKILL.md.

---

## Generic techniques (applicable to ARM and x86)

### Precondition must match calling convention exactly
Getting register values wrong (e.g., X1=128 bits vs 16 bytes, counter in register vs memory) wastes hours on wrong execution paths. Always verify the precondition against the assembly's actual entry state by checking the first few instructions' operands.

### Simplify early, not late
Assert intermediate results (via `SUBGOAL_THEN ... ASSUME_TAC` + `ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST`) at the point where expressions are still small. The clean hypothesis propagates through subsequent simulation steps. Trying to prove a 100K+ char expression at the end is impractical.

### WORD_BLAST proves mask identities
`ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST` handles all-ones mask simplification (word_and/word_or/word_insert with 0xFFFFFFFFFFFFFFFF). No need for manual mask lemmas.

### WORD_BLAST can't handle word_pmul
Polynomial multiplication (`word_pmul`) is not a standard bitwise operation. Abbreviate all `word_pmul` subterms before calling WORD_BLAST:
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
After abbreviation, both sides have the same opaque pmul variables and WORD_BLAST resolves the structural XOR/join/subword equality.

### PMUL_KARATSUBA bridges assembly and spec
The assembly uses 3 half-size pmulls (Karatsuba), while the spec uses one full `word_pmul`. Rewriting with `PMUL_KARATSUBA` (from `common/karatsuba_pmul.ml`) decomposes the spec's pmul into the same 3-pmull structure the assembly computes.

### Preconditions on precomputed tables
If the assembly uses precomputed values from a table (like the Karatsuba middle key `hk`), the proof needs a precondition constraining those values. Without it, the proof obligation is unprovable. Example:
```
word_subword hk (0,64) :64 word =
  word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
```

### GHASH closure pattern (1-block)
After ARM/x86 simulation completes, close the GHASH postcondition:
```ocaml
REWRITE_TAC[ghash_polyval_acc; polyval_dot; polyval_reduce_prop3; PMUL_KARATSUBA] THEN
CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
ABBREV_ALL_PMUL_TAC THEN
CONV_TAC WORD_BLAST
```
Key theorems (from `common/karatsuba_pmul.ml` and `common/polyval_ghash.ml`):
- `PMUL_KARATSUBA`: `word_pmul a b` = 3 half-size pmulls
- `polyval_dot`: `polyval_dot a b = polyval_reduce_prop3 (word_pmul a b)`
- `polyval_reduce_prop3`: Prop3 reduction with W = 0xC200000000000000
- `ghash_polyval_acc`: Horner iteration for GHASH accumulation

### Multi-block GHASH (2+ blocks)
The assembly batches GHASH across N blocks: computes N Karatsuba triples (using h, h², ..., h^N from htable), XORs all 256-bit products, then does ONE Prop3 reduction. This means:
- Per-block assertion won't work (no per-block GHASH boundaries in the assembly)
- Need `GHASH_POLYVAL_ACC_N` (N-block Horner unrolling lemma)
- Need a bridge lemma connecting the batched assembly shape to the mathematical spec
- The 4-line WORD_BLAST closure works for 1 block but doesn't scale (exponential in expression depth)
- For N blocks: per-step simplification + bridge lemma + `ABBREV_ALL_PMUL_TAC` + WORD_BLAST (or manual reduction rounds)

### AES encryption assertion pattern
After AES rounds complete, assert the ciphertext:
```ocaml
FIRST_X_ASSUM(MP_TAC o SPEC `(word_xor plaintext (aes256_encrypt ctr0 keys)):int128`
  o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
ANTS_TAC THENL
[ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
 REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
 REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
 CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC];
 DISCH_TAC]
```

### Understand the control flow before proving
Trace the execution path through the assembly before writing the proof. For the 8x function: the B.GT cascade is linear (6 comparisons against thresholds), not a loop. For 1 full block with X5=0, all branches are NOT taken. Getting this wrong means simulating the wrong path entirely.

### Frame condition closure
After `ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]`:
```ocaml
REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]
```

---

## ARM-specific techniques

### DISCARD_COUNTER_REGS_TAC prevents term explosion
Counter-increment registers (REV32+ADD patterns for AES-GCM counter mode) produce 4.7MB terms. Discard after each pair of steps:
```ocaml
let DISCARD_COUNTER_REGS_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let s = string_of_term(concl th) in
    try String.sub s 0 7 = "read PC" || String.sub s 0 7 = "read NF" ||
        String.sub s 0 7 = "read ZF" || String.sub s 0 7 = "read CF" ||
        String.sub s 0 7 = "read VF"
    with _ -> false)));;
```
Usage: `ARM_STEPS_TAC EXEC (12--13) THEN DISCARD_COUNTER_REGS_TAC`

### ARM_VSTEPS_TAC for intermediate assertions
Use VSTEPS for a small window (2–8 steps) around a store instruction to keep register hypotheses alive:
```ocaml
ARM_VSTEPS_TAC EXEC (325--332) THEN
SUBGOAL_THEN `read (memory :> bytes128 out_p) (s332:armstate) = spec`
  ASSUME_TAC THENL
[ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
(* Clean hypothesis propagates through subsequent ARM_STEPS_TAC *)
```
- VSTEPS is slow with many hypotheses — discard unneeded ones first, keep window ≤8 steps
- VSTEPS is O(n²) in hypothesis count; the ciphertext VSTEPS (8 steps) took <1s with ~80 hypotheses but would timeout with 200+

### VSTEPS can't handle D-register instructions
`mov v16.d[0], v8.d[1]` (INS element) causes `mk_comb: types do not agree` in VSTEPS. Use ARM_STEPS_TAC for those steps, then switch to VSTEPS after.

### ARM_STEPS_TAC consumes register hypotheses
CLARIFY_TAC (run after each step) substitutes register values into the goal and discards them. You cannot use FIRST_X_ASSUM to find a register hypothesis after ARM_STEPS_TAC — it's gone. Use VSTEPS if you need to keep it, or assert the value via SUBGOAL_THEN before it's consumed.

### ARM_STEPS_RESOLVE_TAC for branch cascades
Handles conditional branches automatically without needing to know their positions. Use for sections with B.GT/B.LT cascades.

### D-register instructions and type-specialized clauses
`arm_MOVI` and `arm_LDR` are polymorphic in register width N. `GEN_REWRITE_CONV` can't type-instantiate, so 64-bit specializations must be added explicitly to `ARM_OPERATION_CLAUSES` and `ARM_LOAD_STORE_CLAUSES` if the standard arm.ml doesn't handle them.

### REV64 on large expressions explodes
When a register holds a large symbolic expression and REV64 expands it into 16 byte-level subwords, the term can take minutes to process. Abbreviate the register value before the REV64 step to avoid this (~3.5 min → ~3s).

---

## x86-specific techniques

*(To be added when x86 AES-GCM proofs are attempted.)*
