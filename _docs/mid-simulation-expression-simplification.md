# Mid-Simulation Expression Simplification

How to collapse bloated symbolic expressions during ARM simulation proofs.

## The Problem

After `ARM_STEPS_TAC` (or `ARM_ACCSTEPS_TAC`) steps through SIMD/crypto
instructions, register assumptions become deeply nested `word_join` /
`word_subword` trees — thousands of lines for a single 128-bit register.
These are correct but unusable: subsequent steps compound the bloat, and
`ENSURES_FINAL_STATE_TAC` can't match them against the postcondition.

Example after `rev64` + `ext #8` on a 128-bit load:

```
read Q3 s7 = word_subword (word_join (word_join (word_join (...) (...)) ...) ...) (64,128)
```

This equals `word_bytereverse xi` but HOL Light doesn't know that yet.

## The Solution (from `aes_xts_encrypt.ml`)

Replace the bloated assumption with a clean one by asserting equality
and proving it with `BITBLAST_TAC`:

```ocaml
FIRST_X_ASSUM(MP_TAC o SPEC `desired_clean_value` o MATCH_MP (MESON[]
  `read (REG:(armstate,T)component) s = a
   ==> !a'. a = a' ==> read REG s = a'`)) THEN
ANTS_TAC THENL [BITBLAST_TAC; DISCH_TAC]
```

After this:
- The old assumption `read REG s = <bloated>` is consumed
- A new assumption `read REG s = desired_clean_value` is added
- Subsequent `ARM_STEPS_TAC` calls operate on the clean form

## Step by Step

### 1. Run ARM_STEPS_TAC for a group of instructions

```ocaml
ARM_STEPS_TAC EXEC (1--7) THEN   (* e.g., ld1 + movi + ldp + ext + shl + rev64 + ext *)
```

### 2. Identify which register has the bloated expression

Look at the goal state. You'll see assumptions like:
```
read Q3 s7 = word_join (word_join ...) ...
```

### 3. Determine what the expression should simplify to

From the assembly semantics, you know what the register should contain.
For `rev64` + `ext #8` on data loaded from memory: `word_bytereverse xi`.

### 4. Apply the simplification pattern

```ocaml
FIRST_X_ASSUM(MP_TAC o SPEC `word_bytereverse (xi:int128)` o MATCH_MP (MESON[]
  `read (Q3:(armstate,int128)component) s = a
   ==> !a'. a = a' ==> read Q3 s = a'`)) THEN
ANTS_TAC THENL [BITBLAST_TAC; DISCH_TAC] THEN
```

`BITBLAST_TAC` closes the equality `<bloated> = word_bytereverse xi`
via BDD-based bit-level reasoning (~7s for 128-bit expressions with
one free variable).

### 5. Continue stepping with clean state

```ocaml
ARM_STEPS_TAC EXEC (8--11) THEN   (* next group of instructions *)
```

Now the simulator sees `read Q3 s7 = word_bytereverse xi` instead of
the bloated tree, so subsequent expressions stay manageable.

## When to Simplify

Apply after each logical group of SIMD instructions:

| After instructions | Simplify to |
|---|---|
| `rev64` + `ext #8` (data prep) | `word_bytereverse x` |
| `ext #8` (H from Htable) | `byteswap128(byteswap128 h) = h` |
| 3 × `pmull` + `eor` (Karatsuba) | `word_pmul a b` (via `PMUL_KARATSUBA`) |
| `pmull` + `ins` + `eor` (reduction phase 1) | intermediate reduction term |
| `pmull` + `ext` + `eor` (reduction phase 2) | `polyval_reduce_prop3 t` |
| `rev64` + `ext #8` (output) | `word_bytereverse result` |

## Variations

### Multiple registers at once

Apply the pattern to each register separately:

```ocaml
FIRST_X_ASSUM(MP_TAC o SPEC `val1` o MATCH_MP (MESON[]
  `read (Q3:(armstate,int128)component) s = a ==> !a'. a = a' ==> read Q3 s = a'`)) THEN
ANTS_TAC THENL [BITBLAST_TAC; DISCH_TAC] THEN
FIRST_X_ASSUM(MP_TAC o SPEC `val2` o MATCH_MP (MESON[]
  `read (Q17:(armstate,int128)component) s = a ==> !a'. a = a' ==> read Q17 s = a'`)) THEN
ANTS_TAC THENL [BITBLAST_TAC; DISCH_TAC] THEN
```

### When BITBLAST_TAC is too slow

If the expression has multiple free 128-bit variables (e.g., after XOR
of two symbolic values), `BITBLAST_TAC` may time out. Alternatives:

1. **CONV_TAC with domain-specific rewrites** — unfold definitions and
   use `REWRITE_CONV` + `let_CONV` (as XTS does for AES rounds)
2. **WORD_RULE** — for pure word-algebra equalities (XOR commutativity, etc.)
3. **Split into 64-bit halves** — prove `word_subword result (0,64) = lo`
   and `word_subword result (64,64) = hi` separately, then combine

### Using REWRITE_CONV instead of BITBLAST_TAC (XTS AES pattern)

For AES round simplification, XTS uses algebraic unfolding:

```ocaml
ANTS_TAC THENL
[ EXPAND_TAC "key_lst" THEN
  CONV_TAC (RAND_CONV (
    REWRITE_CONV [aes256_encrypt_round; aese; aesmc] THENC
    DEPTH_CONV let_CONV)) THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
  REFL_TAC;
  DISCH_TAC] THEN
```

For GHASH, the analogous approach would unfold `polyval_reduce_prop3`
and the Karatsuba definitions, then use word-level rewrites.

### Wrapping as a reusable tactic

```ocaml
let SIMD_SIMPLIFY_TAC reg desired_val =
  FIRST_X_ASSUM(MP_TAC o SPEC desired_val o MATCH_MP (MESON[]
    (mk_comb(mk_comb(`(==>)`,
      mk_comb(mk_comb(`(=):int128->int128->bool`,
        mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`, reg),`s:armstate`)),
        `a:int128`)),
      `!a'. a = a' ==> read ... s = a'`)))) THEN
  ANTS_TAC THENL [BITBLAST_TAC; DISCH_TAC];;
```

In practice, just inline the pattern — it's short enough.

## Performance

| Expression complexity | BITBLAST_TAC time |
|---|---|
| 128-bit, 1 free variable (rev64+ext) | ~7s |
| 128-bit, 1 free variable (ext only) | ~0.2s |
| 256-bit, 2 free variables (pmull) | may timeout — use algebraic approach |

## Key Insight

The simulator is correct but dumb — it faithfully tracks every bit
manipulation without simplifying. The proof engineer must periodically
"checkpoint" the symbolic state by asserting what each register equals
in terms of the spec-level operations. This is analogous to loop
invariants: you state what the registers mean at key points, prove it
matches the simulation output, and continue from the clean state.
