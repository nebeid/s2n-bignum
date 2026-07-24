(* ============================================================================
   WORK FILE — empty slate (2026-07-24).

   Previous contents (NIST convergence layer: KARATSUBA_MID_BYTESWAP,
   H_POWER_UNFOLD_7, HTABLE_MEM_DEC_H_POWER, htable_mem_8,
   HTABLE_MEM_DEC_IS_HTABLE_MEM_8, GCM_DEC_FINAL_XI_NIST, BREV_RF8_128,
   AESV8_GCM_8X_DEC_256_WB_DISPATCH_NIST_TAG) were PROMOTED into
   arm/proofs/aesv8_gcm_8x_dec_256_wb_nist.ml.
   Also hoisted aes13 + AES256_XOR_ENCRYPT_RECONSTRUCT from wb.ml into
   arm/proofs/utils/aes_gcm_reconstruct.ml (shared with the future
   main-loop proof); wb.ml now needs that file.
   Snapshot of the pre-promotion work.ml: _backups/work.nist_convergence.bck0001.ml.

   Next workstream: the whole-blocks main-loop (ENSURES_WHILE) proof for
   symbolic nblk > 8 — see _docs/wb-main-loop-plan.md.
   ============================================================================ *)
