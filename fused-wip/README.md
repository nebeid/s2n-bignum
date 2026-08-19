# AES-256-GCM decrypt — d5 fused small-path proof arc (WIP)

**Branch:** `aes-gcm-fused-wip` only. **Do NOT merge to `aes-gcm-wb-mainloop`**
until the whole arc is CHEAT-free (axioms=3, hyps=0) *and* gated by the cold
load test. These are archival proof scaffolds captured from the prover session
logs so the arc no longer exists only as loose `/tmp` and log files.

## What this is

The d5 fused small path is a runtime optimisation queued on top of the already
complete AES-256-GCM whole-blocks DECRYPT proof
(`arm/proofs/aesv8_gcm_8x_dec_256_wb.ml`). It adds one fused code region with
entry labels for `nblk = 4/3/2/1`, each section finishing one block through all
14 AES rounds with GHASH folds interleaved, sharing a tail. The proof shape is
**one code region, one simulation, instantiated four times** for `nblk = 1..4`
— structurally like the existing `<= 8` bands that share a front lemma. NOT four
independent proofs.

All four fused blocks are **PROVEN, CHEAT-free** (`hyps=0`, no `new_axiom` /
`mk_thm` / `CHEAT_TAC` in the canonical proof of each). See "Canonical proofs"
below.

## IMPORTANT: these scaffolds are NOT source-loadable standalone

Each canonical `*_PROVEN.ml` / `wb_v42.ml` / `wb2_v3_qq8fold.ml` was developed
and validated by loading it **on top of the fused DMTCP checkpoint**
`hol-wb-dec-fused.ckpt` via `/tmp/s108work/restore_fused.sh <check.ml> <TAG>`
(`RESTORE_EXIT=0`). They depend on infrastructure baked into that checkpoint and
NOT present in a from-source base:

- `build_GMULTn_fast k` (defined in `arm/proofs/aesv8_gcm_8x_dec_256_le*block.ml`)
- `GHASH_POLYVAL_ACC_2 / _3 / _4` (GHASH 8-block extension algebra)
- the whole `aesv8_gcm_8x_dec_256_lemmas.ml` bridge + store helper stack
  (`~117s` to `needs`)
- `POLYVAL_DOT_SYM` (`wb.ml:1650`) and `spec_to_byteform_wbK`, which the
  scaffolds redefine in-file.

So `needs`-ing these files from a clean tree will fail on unbound values. That
is expected for WIP. The proofs are real; only the load harness (the fused
checkpoint) is not in-tree yet. The eventual in-tree home is the atomic
`.S + machine-code literal + DISPATCH splice` into
`arm/proofs/aesv8_gcm_8x_dec_256_wb.ml` (see the s108/s109 integration plan),
which is deliberately deferred until AFTER the mainloop cold-load rebase.

## Canonical proofs (do not re-prove)

| k | fused block         | canonical file                               | status                                  |
|---|---------------------|----------------------------------------------|-----------------------------------------|
| 1 | `WB_FUSED_1BLOCK`   | `session-122-work/wb_v42.ml`                 | PROVEN hyps=0, no CHEAT, `RESTORE_EXIT=0` |
| 2 | `WB_FUSED_2BLOCK`   | `session-126-work/wb2_v3_qq8fold.ml`         | PROVEN hyps=0, no CHEAT, `RESTORE_EXIT=0` |
| 3 | `WB_FUSED_3BLOCK`   | `session-132-work/WB_FUSED_3BLOCK_PROVEN.ml` | PROVEN hyps=0, no CHEAT, `RESTORE_EXIT=0` |
| 4 | `WB_FUSED_4BLOCK`   | `session-133-work/WB_FUSED_4BLOCK_PROVEN.ml` | PROVEN hyps=0, no CHEAT, `RESTORE_EXIT=0` |

Each fused block's `prove(...)` pays a ~13-min justification-replay (finite, NOT
a hang — measured in session 132: `cpu_elapsed=777.4s`, `major_colls_delta=8`).
Budget any cold gate that loads them accordingly.

### SIM step-maps (from the canonical file headers)

- **k=1**: bridge = s121 `BRIDGE_CLOSE_FULL_TAC`; store tail splits bytes128
  readbacks to bytes64 halves before `ENSURES_FINAL`.
- **k=2**: windows `(1--30)`; blk0×H² KEEPGHALL, pt0; blk1×H reduce; bridge; tail
  xi/ivec(`GCM_CTR_INC2_LANES`)/pt1. Bridge = 3 block-0 mid distributions folded
  via `WORD_PMUL_XOR` before `WA_UNIFY`.
- **k=3**: `plain(1--30)`; g3/blk0 KEEPGHALL `(31--80)` pt0@s80; g2/blk1
  `(81--123)` pt1@s123; g1/blk2+reduce `(124--170)` bridge@s170; tail s170→s183:
  xi@s177, ivec@s180, pt2@s182. See `session-132-work/K4_DISASM_FACTS.md`.
- **k=4**: `plain(1--30)`; w0 blk0×H⁴ KEEPGHALL `(31--81)` pt0@s81; w1 blk1×H³
  `(82--124)` pt1@s124; w2 blk2×H² `(125--167)` pt2@s167; w3 blk3×H+reduce
  `(168--214)` bridge@s214; brev@s218; tail VSTEPS `(215--227)`: xi@s221,
  ivec@s224, blk3 store@s226, b@s227. Bridge: qq14=qq9⊕qq1 (hi), qq13=qq8⊕qq0
  (lo), qq20=qq15⊕qq16 (mid). See `session-133-work/K4_STEP_MAP.md`.

The MAYCHANGE frame for k=3/k=4 is discharged via a `WB{3,4}_FRAME_SUBSUMED` /
`WB{3,4}_FRAME_IMP` lemma proved at file top in a clean environment (frame
algebra, no fused deps), then transported by `MATCH_MP` + `ACCEPT` at the
MAYCHANGE goal — this side-steps the post-SIM environmental spin of
`SUBSUMED_MAYCHANGE_TAC` over the ~1300-assumption accumulated frame.

## Other files per session-work dir

`wb_v33..v41.ml`, `wb2_diag_*.ml`, `wb3_v11_TERMINATES.ml`, `wb4_diag.ml`,
`wb4_close.ml`, `*.out`, `SESSION-*-SUMMARY.md` are the diagnostic /
stepping-stone / stage-tracer files that led to each canonical proof. **Several
of the diagnostic files DO contain `CHEAT_TAC`** (they stub the bridge or the
store tail to isolate one stage): `wb_v33_diag.ml`, `wb_v37.ml`, `wb_v39.ml`,
`wb_v40.ml`, `wb_v41.ml`, `wb2_diag_bridge.ml`, `wb2_diag_stores.ml`,
`wb4_diag.ml`, `wb4_close.ml`. They are kept for provenance and to speed up the
eventual splice; they are NOT part of the CHEAT-free result. The canonical
`*_PROVEN.ml` / `wb_v42.ml` / `wb2_v3_qq8fold.ml` files are the CHEAT-free
artifacts.

## Next step (deferred, not in this WIP)

Per HUMAN DIRECTION 2026-08-19: do the `.S + literal + DISPATCH` splice into
`aesv8_gcm_8x_dec_256_wb.ml` only AFTER the `aes-gcm-wb-mainloop` cold-load
rebase (the `arm_REV32_VEC` shape-mismatch fix), or the fused bodies will need
re-adapting.
