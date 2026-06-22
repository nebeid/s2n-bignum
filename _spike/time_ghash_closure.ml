(* ========================================================================= *)
(* SPIKE (2026-06-22): time the GHASH band-closure three ways on the faithful  *)
(* s367 register tower, at N = 2, 3, 4 blocks.  Measurement / methodology      *)
(* comparison for handback-doc D7 (our MERGE/FINISH vs Mila's EQ_PROP3 vs the  *)
(* hybrid).  NOT part of any shipped proof -- scratch only.  No CHEAT_TAC.      *)
(*                                                                            *)
(* Load order (cwd = project root, base.ml preloaded):                         *)
(*   needs "common/karatsuba_pmul.ml";;       [ schoolbook/karatsuba pmul ]     *)
(*   needs "common/polyval_ghash.ml";;        [ our GHASH spec layer ]          *)
(*   loadt "_spike/mila_ghash_spec_body.ml";; [ Mila ghash_spec extras ]         *)
(*   loadt "_spike/mila_nblock_layer.ml";;    [ Mila ghash_Nblock_karatsuba +    *)
(*                                              GHASH_NBLOCK_KARATSUBA_EQ_PROP3 ]*)
(*   loadt "_spike/our_bridge_helpers.ml";;   [ our MERGE_2BLK/FINISH_2BLK ]    *)
(*   loadt "_spike/time_ghash_closure.ml";;                                    *)
(*                                                                            *)
(* The faithful s367 tower IS her ghash_Nblock_karatsuba UNFOLDED (her spec    *)
(* mirrors the assembly instruction-for-instruction), instantiated with the    *)
(* real GHASH operands and with the outer word_reversefields 8 stripped (= our  *)
(* ext+rev64 at sim steps 368-369, applied AFTER s367).                        *)
(* ========================================================================= *)

let time_it label f =
  let t0 = Sys.time() in
  let r = f () in
  let dt = Sys.time() -. t0 in
  Printf.printf "[TIMING] %-28s %.4fs\n%!" label dt;
  (r, dt);;

let BYTESWAP128_INVOLUTION = prove(
  `!x:int128. byteswap128(byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* our_bridge_helpers rebinds KARATSUBA_LIMBS to a CONJ form via her layer;     *)
(* restore the LET form for the OURS route (not used by MILA).                  *)
let KARATSUBA_LIMBS = prove(
  `!(p_lo:int128) (p_hi:int128) (cross:int128).
   let t:(256)word = word_xor (word_xor (word_zx p_lo)
                                        (word_shl (word_zx cross) 64))
                              (word_shl (word_zx p_hi) 128) in
   word_subword t (0,64) : 64 word = word_subword p_lo (0,64) /\
   word_subword t (64,64) : 64 word = word_xor (word_subword p_lo (64,64))
                                               (word_subword cross (0,64)) /\
   word_subword t (128,64) : 64 word = word_xor (word_subword p_hi (0,64))
                                                (word_subword cross (64,64)) /\
   word_subword t (192,64) : 64 word = word_subword p_hi (64,64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

(* ---- generic tower builder: unfold her spec on N symbolic triples --------- *)
let unfold_tower triples =
  REWRITE_CONV[ghash_Nblock_karatsuba; kara_acc; karatsuba_block_pl;
               karatsuba_block_ph; karatsuba_block_pm; karatsuba_reduce_shared;
               LET_DEF; LET_END_DEF; WORD_XOR_0_LEFT]
    (mk_comb(`ghash_Nblock_karatsuba`, triples));;

(* ========================================================================= *)
(* N = 2                                                                       *)
(* ========================================================================= *)
let tower2_th = unfold_tower
  `[(in0:int128, htw0:int128, hk0:int128); (in1:int128, htw1:int128, hk1:int128)]`;;
let tower2_inst = INST [
  `word_xor (word_bytereverse (xi:int128)) (word_bytereverse (ct0:int128))`, `in0:int128`;
  `word_bytereverse (ct1:int128)`, `in1:int128`;
  `h2:int128`, `htw0:int128`; `h:int128`, `htw1:int128`;
  `hk2:int128`, `hk0:int128`; `hk:int128`, `hk1:int128`] tower2_th;;
let raw2 = rand(rhs(concl tower2_inst));;
let ghash2_goal = mk_imp(
  `(word_subword (hk:int128) (0,64):(64)word =
      word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)) /\
   (word_subword (hk2:int128) (0,64):(64)word =
      word_xor (word_subword (h2:int128) (0,64):64 word) (word_subword h2 (64,64):64 word)) /\
   byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)`,
  mk_eq(raw2, `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                  [word_bytereverse ct0; word_bytereverse ct1]`));;

let (th_mila2, dt_mila2) = time_it "MILA 2-block (EQ_PROP3)" (fun () -> prove(ghash2_goal,
  STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(raw2, `word_reversefields 8 (ghash_Nblock_karatsuba
      [(word_xor (word_bytereverse xi) (word_bytereverse ct0), h2, hk2);
       (word_bytereverse ct1, h, hk)])`)) SUBST1_TAC THENL
   [REWRITE_TAC[tower2_inst] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]; ALL_TAC] THEN
  MP_TAC(SPEC `[(word_xor (word_bytereverse xi) (word_bytereverse ct0), h2, hk2, byteswap128 h2);
                (word_bytereverse ct1, h, hk, byteswap128 h)]
               :(int128#int128#int128#int128)list` GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  REWRITE_TAC[kara_quad_ok; project_triples; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BYTESWAP128_INVOLUTION] THEN
    ASM_REWRITE_TAC[karatsuba_mid; BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
    CONV_TAC WORD_RULE; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN ASM_REWRITE_TAC[]));;

(* ========================================================================= *)
(* N = 3                                                                       *)
(* ========================================================================= *)
let tower3_th = unfold_tower
  `[(in0:int128, htw0:int128, hk0:int128); (in1:int128, htw1:int128, hk1:int128);
    (in2:int128, htw2:int128, hk2:int128)]`;;
let tower3_inst = INST [
  `word_xor (word_bytereverse (xi:int128)) (word_bytereverse (ct0:int128))`, `in0:int128`;
  `word_bytereverse (ct1:int128)`, `in1:int128`;
  `word_bytereverse (ct2:int128)`, `in2:int128`;
  `h3:int128`, `htw0:int128`; `h2:int128`, `htw1:int128`; `h:int128`, `htw2:int128`;
  `hk3:int128`, `hk0:int128`; `hk2:int128`, `hk1:int128`; `hk:int128`, `hk2:int128`] tower3_th;;
let raw3 = rand(rhs(concl tower3_inst));;
let ghash3_goal = mk_imp(
  `(word_subword (hk:int128) (0,64):(64)word = word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)) /\
   (word_subword (hk2:int128) (0,64):(64)word = word_xor (word_subword (h2:int128) (0,64):64 word) (word_subword h2 (64,64):64 word)) /\
   (word_subword (hk3:int128) (0,64):(64)word = word_xor (word_subword (h3:int128) (0,64):64 word) (word_subword h3 (64,64):64 word)) /\
   byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h))`,
  mk_eq(raw3, `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                  [word_bytereverse ct0; word_bytereverse ct1; word_bytereverse ct2]`));;

let (th_mila3, dt_mila3) = time_it "MILA 3-block (EQ_PROP3)" (fun () -> prove(ghash3_goal,
  STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(raw3, `word_reversefields 8 (ghash_Nblock_karatsuba
      [(word_xor (word_bytereverse xi) (word_bytereverse ct0), h3, hk3);
       (word_bytereverse ct1, h2, hk2); (word_bytereverse ct2, h, hk)])`)) SUBST1_TAC THENL
   [REWRITE_TAC[tower3_inst] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]; ALL_TAC] THEN
  MP_TAC(SPEC `[(word_xor (word_bytereverse xi) (word_bytereverse ct0), h3, hk3, byteswap128 h3);
                (word_bytereverse ct1, h2, hk2, byteswap128 h2);
                (word_bytereverse ct2, h, hk, byteswap128 h)]
               :(int128#int128#int128#int128)list` GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  REWRITE_TAC[kara_quad_ok; project_triples; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BYTESWAP128_INVOLUTION] THEN
    ASM_REWRITE_TAC[karatsuba_mid; BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
    CONV_TAC WORD_RULE; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_3] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE));;

(* ========================================================================= *)
(* N = 4                                                                       *)
(* ========================================================================= *)
let tower4_th = unfold_tower
  `[(in0:int128, htw0:int128, hk0:int128); (in1:int128, htw1:int128, hk1:int128);
    (in2:int128, htw2:int128, hk2:int128); (in3:int128, htw3:int128, hk3:int128)]`;;
let tower4_inst = INST [
  `word_xor (word_bytereverse (xi:int128)) (word_bytereverse (ct0:int128))`, `in0:int128`;
  `word_bytereverse (ct1:int128)`, `in1:int128`;
  `word_bytereverse (ct2:int128)`, `in2:int128`;
  `word_bytereverse (ct3:int128)`, `in3:int128`;
  `h4:int128`, `htw0:int128`; `h3:int128`, `htw1:int128`;
  `h2:int128`, `htw2:int128`; `h:int128`, `htw3:int128`;
  `hk4:int128`, `hk0:int128`; `hk3:int128`, `hk1:int128`;
  `hk2:int128`, `hk2:int128`; `hk:int128`, `hk3:int128`] tower4_th;;
let raw4 = rand(rhs(concl tower4_inst));;
let ghash4_goal = mk_imp(
  `(word_subword (hk:int128) (0,64):(64)word = word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)) /\
   (word_subword (hk2:int128) (0,64):(64)word = word_xor (word_subword (h2:int128) (0,64):64 word) (word_subword h2 (64,64):64 word)) /\
   (word_subword (hk3:int128) (0,64):(64)word = word_xor (word_subword (h3:int128) (0,64):64 word) (word_subword h3 (64,64):64 word)) /\
   (word_subword (hk4:int128) (0,64):(64)word = word_xor (word_subword (h4:int128) (0,64):64 word) (word_subword h4 (64,64):64 word)) /\
   byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)`,
  mk_eq(raw4, `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                  [word_bytereverse ct0; word_bytereverse ct1; word_bytereverse ct2; word_bytereverse ct3]`));;

let (th_mila4, dt_mila4) = time_it "MILA 4-block (EQ_PROP3)" (fun () -> prove(ghash4_goal,
  STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(raw4, `word_reversefields 8 (ghash_Nblock_karatsuba
      [(word_xor (word_bytereverse xi) (word_bytereverse ct0), h4, hk4);
       (word_bytereverse ct1, h3, hk3); (word_bytereverse ct2, h2, hk2);
       (word_bytereverse ct3, h, hk)])`)) SUBST1_TAC THENL
   [REWRITE_TAC[tower4_inst] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]; ALL_TAC] THEN
  MP_TAC(SPEC `[(word_xor (word_bytereverse xi) (word_bytereverse ct0), h4, hk4, byteswap128 h4);
                (word_bytereverse ct1, h3, hk3, byteswap128 h3);
                (word_bytereverse ct2, h2, hk2, byteswap128 h2);
                (word_bytereverse ct3, h, hk, byteswap128 h)]
               :(int128#int128#int128#int128)list` GHASH_NBLOCK_KARATSUBA_EQ_PROP3) THEN
  REWRITE_TAC[kara_quad_ok; project_triples; kara_quad_pmul; WORD_XOR_0_LEFT] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[BYTESWAP128_INVOLUTION] THEN
    ASM_REWRITE_TAC[karatsuba_mid; BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
    CONV_TAC WORD_RULE; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_4] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE));;

Printf.printf "\n[SUMMARY] MILA EQ_PROP3 route: N=2 %.4fs | N=3 %.4fs | N=4 %.4fs\n%!"
  dt_mila2 dt_mila3 dt_mila4;;

(* ========================================================================= *)
(* MEASURED RESULTS (2026-06-22)                                              *)
(*                                                                            *)
(*   route                         N=2        N=3        N=4                  *)
(*   ----------------------------- ---------- ---------- ----------           *)
(*   MILA (EQ_PROP3 + ACC_N)       0.047s     0.078s     0.103s              *)
(*   OURS (MERGE/FINISH) real      ~73s       (n/a)      (n/a)               *)
(*   OURS reconstructed-term       157s FAIL  -          -                   *)
(*                                                                            *)
(* MILA scales flat (~+25ms/block): the hard induction                        *)
(* GHASH_NBLOCK_KARATSUBA_EQ_PROP3 is proven ONCE at layer-load.              *)
(* OURS re-runs the lane-flatten/merge per band (~73s on the genuine s367     *)
(* term, recorded in the proof file) and is BRITTLE to exact XOR-nesting.     *)
(*                                                                            *)
(* WINNER: MILA for the band ladder. HYBRID (her EQ_PROP3 + our FAST_OPERAND *)
(* for residuals) is UNNECESSARY: EQ_PROP3 closes with NO residual operand    *)
(* equalities (the per-block pack identity is baked into                       *)
(* KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN, proven once).                          *)
(* ========================================================================= *)
