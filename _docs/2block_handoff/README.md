# enc 2-block proof handoff

The full 2-block (bit_len=256) simulation of aesv8_gcm_8x_enc_256 is COMPLETE
through to pc+0x11d0 (one step before the xi_p store). See
`arm/proofs/aesv8_gcm_8x_enc_256_2block.ml` PROGRESS block for the full recipe.

## The remaining piece: the GHASH bridge

`q19_s361_reduced.txt` is the reduced GHASH result in Q19 at state s361 (the
bridge LHS), just before the ext(0x11c8)+rev64(0x11d0) byte-reorder. It is only
~691 chars because the two carryless products stay as opaque `word_pmul`:

- block-1 term: `word_pmul (subword (brev ct1) _) (subword h _)`     [vs H = byteswap128 h key]
- block-0 term: `word_pmul (subword (brev xi XOR brev ct0) _) (subword h2 _)` [vs H^2]

This is exactly the shape of GHASH_POLYVAL_ACC_2's RHS:
  ghash_polyval_acc K a [b;c]
    = polyval_reduce_prop3(pmul(a XOR b, polyval_dot K K) XOR pmul(c, K))
with K = byteswap128 h, a = brev xi, b = brev ct0, c = brev ct1, and
polyval_dot K K = byteswap128 h2 (machine-checked: byteswap128(h_power H 1) form).

### Bridge plan
1. Assert `read Q19 s361 = <GHASH_POLYVAL_ACC_2 RHS over K,a,b,c>` by the 1-block
   bridge machinery (GMULT-style: PMUL_KARATSUBA / KARATSUBA_LIMBS / PMUL_W_64_128
   / ABBREV_INNER_PMULS_TAC / MERGE_PMUL_ATOMS_TAC / the manual lane-fold), now
   over TWO products instead of one.
2. GSYM GHASH_POLYVAL_ACC_2 to get ghash_polyval_acc K (brev xi) [brev ct0; brev ct1].
3. ext+rev64 -> word_bytereverse(gval); store to xi_p; ENSURES_FINAL_STATE; close
   (EXPAND ct0, ct1; the spec GHASHes [brev ct0; brev ct1]).

### Spec finalization
Expose ctr1 as a spec variable (block-1's AES-input counter = lane-level
rev32(rev32(ctr0)+1)); add a precond pinning Q1's keystream, OR carry ct1 inline.

### Front recipe (validated, ~31s to the tail; deterministic)
In the work-file PROGRESS block. Key: 1-at-a-time fold through the CTR setup
(steps 1-25) keeping Q0,Q1,Q30; DK1 for AES bulk; X5=word 32 rewrite resolves
the tail cascade; DK1c (keep Q7) through the cascade; ABBREV ct0,ct1 before the
GHASH pmull; ARM_VSTEPS_FOLD + DISCARD_OLDSTATE through the two multiplies + the
single reduction.
