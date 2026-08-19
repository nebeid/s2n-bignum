(* SESSION 122: the 3 store-tail closers for the d5 fused WB_FUSED_1BLOCK, each validated hyps=0
   on the fast MCP against the REAL machine store readback forms (dumped via the STORE97 diagnostic
   at s97 — see store97-diag.out). These transform the bytes128 store readbacks to SPEC form BEFORE
   ENSURES_FINAL_STATE_TAC (while `gval` is still a live ABBREV). ENSURES_FINAL then splits into
   bytes64 halves that close by REFL against the now-SPEC-valued readbacks.

   KEY FINDINGS:
   * The machine OUT AES input word_join(word_subword ctr0 (8k,8)...) reconstructs ctr0 EXACTLY
     (identity, NOT a byte-reversal as s121 supposed). JOIN_IS_CTR0 collapses it — but WORD_BLAST
     needs EXPLICIT intermediate word types (:16/:32/:64). A find_term'd/reparsed join has schematic
     type vars so WORD_BLAST FAILS; in-sim the types are concrete so the standalone lemma fires.
   * OUT machine outer form is word_xor (word_xor cph TOWER) k14 (AddRoundKey folded at the END),
     so NO leading AP_TERM_TAC — expand aes256_encrypt and let WORD_RULE reassociate the final XOR.
   * The machine IVEC store form == gcm_ctr_inc_iter 1 ctr0 unfolded via GCM_CTR_INC_LANES EXACTLY.
   * XI readback = word_bytereverse gval where gval = polyval_dot(word_xor(brev xi)(brev cph))(bswap h);
     EXPAND gval + AP_TERM_TAC + GHASH_1BLOCK_CORRECT bridges to word_bytereverse(ghash_polyval_acc...).

   Load prereq: needs "arm/proofs/aesv8_gcm_8x_dec_256_lemmas.ml" (fast base MCP). *)

let JOIN_IS_CTR0 = prove(
 `word_join
    (word_join
     (word_join
      (word_join (word_subword (ctr0:int128) (120,8):8 word) (word_subword ctr0 (112,8):8 word):16 word)
      (word_join (word_subword ctr0 (104,8):8 word) (word_subword ctr0 (96,8):8 word):16 word):32 word)
     (word_join
      (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
      (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word):32 word):64 word)
    (word_join
     (word_join
      (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
      (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word):32 word)
     (word_join
      (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
      (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word):32 word):64 word):int128
  = ctr0`,
  CONV_TAC WORD_BLAST);;

(* OUT closer (validated hyps=0 on a typed representative of the machine out tower): *)
(*   REWRITE_TAC[JOIN_IS_CTR0] THEN REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
     REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE  *)

(* XI closer (validated hyps=0): *)
let XI_BYTES128 = prove(
  `word_bytereverse (polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph)) (byteswap128 h))
   = word_bytereverse
       (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) [word_bytereverse cph])`,
  AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT]);;
(*   in-sim: EXPAND_TAC "gval" THEN AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT]  *)

(* IVEC closer (validated: gcm_ctr_inc_iter 1 ctr0 unfolds to the machine lane-shuffle exactly): *)
(*   REWRITE_TAC[num_CONV `1`; gcm_ctr_inc_iter; GCM_CTR_INC_LANES]  *)
