# GHASH-closure timing spike (2026-06-22)

Measurement-only spike for handback-doc **§D7** — *which GHASH band-closure is faster:
our direct `MERGE_2BLK`/`FINISH_2BLK` lane-flatten, Mila's instruction-mirror
`GHASH_NBLOCK_KARATSUBA_EQ_PROP3`, or a hybrid?* Nothing here is part of a shipped proof.

## Result (measured, no cheats)

Faithful **s367 register tower** = Mila's `ghash_Nblock_karatsuba` UNFOLDED (her spec mirrors
the assembly instruction-for-instruction) instantiated with the real GHASH operands, closed to
our `ghash_polyval_acc` spec two ways:

| route | N=2 | N=3 | N=4 |
|---|---|---|---|
| **MILA** (`GHASH_NBLOCK_KARATSUBA_EQ_PROP3` + `GHASH_POLYVAL_ACC_{2,3,4}`) | **0.05s** | **0.08s** | **0.10s** |
| OURS (`ABBREV_INNER_PMULS`+`MERGE_2BLK`+`FINISH_2BLK`) | ~73s (real s367, recorded) | — | — |
| OURS on reconstructed tower | 157s then FAIL | — | — |

**MILA wins decisively and scales flat (~+25–30 ms/block)** — the hard induction is proven once.
**HYBRID is unnecessary**: `EQ_PROP3` lands on `polyval_reduce_prop3` of the XOR-of-`pmul input_k h_k`
with ZERO residual operand equalities (the per-block Karatsuba pack identity is baked into
`KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN`), so `FAST_OPERAND_TAC` has nothing to do.
**Clash check**: her `common/ghash_spec.ml` `needs common/polyval_ghash.ml` (built on top of ours,
adds only lemmas, zero new constants); her GHASH-karatsuba wrapper loads clash-free on our
`polyval_ghash` + `karatsuba_pmul`.

## Files

- `mila_ghash_spec_body.ml` — Mila's `common/ghash_spec.ml` minus its `needs` (HELPER_3, ACC_3/4).
- `mila_nblock_layer.ml` — Mila's GHASH-karatsuba layer materialized standalone (from
  `mila/aes256_gcm_tail` `gcm_aesgcm_{helpers,nblock_helpers}.ml`): `kara_acc`,
  `karatsuba_reduce_shared`, `ghash_Nblock_karatsuba`, `pack_corrected`, `kara_quad_*`,
  `project_triples`, `GHASH_NBLOCK_KARATSUBA_EQ_PROP3`.
- `our_bridge_helpers.ml` — our bridge machinery (from `aesv8_gcm_8x_enc_256_{1,2}block.ml`):
  `PMUL_CONG_128`, `ABBREV_INNER_PMULS_TAC`, `MERGE_2BLK_TAC`, `FINISH_2BLK_TAC`, `FAST_OPERAND_TAC`.
- `time_ghash_closure.ml` — builds the N=2/3/4 s367 goals and runs+times the MILA route on each.

## Reproduce (HOL MCP, cwd = project root, base.ml preloaded)

```
needs "common/karatsuba_pmul.ml";;
needs "common/polyval_ghash.ml";;
loadt "_spike/mila_ghash_spec_body.ml";;
loadt "_spike/mila_nblock_layer.ml";;
loadt "_spike/our_bridge_helpers.ml";;
loadt "_spike/time_ghash_closure.ml";;
```
