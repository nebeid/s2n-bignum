(* ===== her GHASH-karatsuba layer, materialized standalone for the spike ===== *)
let WORD_XOR_0_LEFT = WORD_BITWISE_RULE `word_xor (word 0) x = (x:(N)word)`;;

let KARATSUBA_LIMB_0_63 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (0,64) : 64 word =
    word_subword xl (0,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_64_127 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (64,64) : 64 word =
    word_xor (word_subword xl (64,64)) (word_subword mid (0,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_128_191 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (128,64) : 64 word =
    word_xor (word_subword xh (0,64)) (word_subword mid (64,64))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMB_192_255 = prove(
  `!(xl:128 word) (xh:128 word) (mid:128 word).
    word_subword (word_xor (word_xor (word_zx xl : 256 word)
                 (word_shl (word_zx mid : 256 word) 64))
                 (word_shl (word_zx xh : 256 word) 128)) (192,64) : 64 word =
    word_subword xh (64,64)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let KARATSUBA_LIMBS = CONJ (CONJ KARATSUBA_LIMB_0_63 KARATSUBA_LIMB_64_127)
                           (CONJ KARATSUBA_LIMB_128_191 KARATSUBA_LIMB_192_255);;

let BYTESWAP128_SUBWORD_LO = prove(
  `!(h:int128). word_subword (byteswap128 h) (0,64):(64)word = word_subword h (64,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_SUBWORD_HI = prove(
  `!(h:int128). word_subword (byteswap128 h) (64,64):(64)word = word_subword h (0,64)`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* Karatsuba (pl_k, ph_k, pm_k) for a single block. *)
let karatsuba_block_pl = new_definition
 `karatsuba_block_pl (input:int128) (h_tw:int128) : int128 =
  word_pmul (word_subword input (0,64) :64 word)
            (word_subword h_tw (64,64) :64 word)`;;

let karatsuba_block_ph = new_definition
 `karatsuba_block_ph (input:int128) (h_tw:int128) : int128 =
  word_pmul (word_subword input (64,64) :64 word)
            (word_subword h_tw (0,64) :64 word)`;;

let karatsuba_block_pm = new_definition
 `karatsuba_block_pm (input:int128) (hk:int128) : int128 =
  word_pmul
    (word_xor (word_subword input (0,64) :64 word)
              (word_subword input (64,64) :64 word))
    (word_subword hk (0,64) :64 word)`;;

(* The recursive XOR-sum of (pl, ph, pm) across all blocks. *)
let kara_acc = define
 `(kara_acc ([]:(int128#int128#int128)list) (pl_acc:int128) (ph_acc:int128)
            (pm_acc:int128) = (pl_acc, ph_acc, pm_acc)) /\
  (kara_acc (CONS (input,h_tw,hk) rest) pl_acc ph_acc pm_acc =
    kara_acc rest
      (word_xor pl_acc (karatsuba_block_pl input h_tw))
      (word_xor ph_acc (karatsuba_block_ph input h_tw))
      (word_xor pm_acc (karatsuba_block_pm input hk)))`;;

(* The shared Barrett reduction taking the accumulated (pl, ph, pm) triple
   and producing the final 128-bit GHASH digest. This mirrors the let-chain
   in ghash_1block_karatsuba (lines 96-112 of gcm_aesgcm_helpers.ml) and the
   matching let-chain in ghash_2block_karatsuba. *)
let karatsuba_reduce_shared = new_definition
 `karatsuba_reduce_shared (pl:int128) (ph:int128) (pm:int128) : int128 =
  let mid:int128 = word_xor (word_xor pm ph) pl in
  let a:64 word = word_subword pl (0,64) in
  let b:64 word = word_xor (word_subword pl (64,64)) (word_subword mid (0,64)) in
  let c:64 word = word_xor (word_subword ph (0,64)) (word_subword mid (64,64)) in
  let d:64 word = word_subword ph (64,64) in
  let w:64 word = word 13979173243358019584 in
  let wa:128 word = word_pmul a w in
  let wa_lo:64 word = word_subword wa (0,64) in
  let wa_hi:64 word = word_subword wa (64,64) in
  let v:64 word = word_xor b wa_lo in
  let u:64 word = word_xor (word_xor c a) wa_hi in
  let wv:128 word = word_pmul v w in
  let wv_lo:64 word = word_subword wv (0,64) in
  let wv_hi:64 word = word_subword wv (64,64) in
  let f:64 word = word_xor u wv_lo in
  let g:64 word = word_xor (word_xor d v) wv_hi in
  word_reversefields 8 (word_join g f : 128 word)`;;

(* The full N-block assembly-shape spec: accumulate Karatsuba triples,
   then apply the shared Barrett reduction. *)
let ghash_Nblock_karatsuba = new_definition
 `ghash_Nblock_karatsuba (triples:(int128#int128#int128)list) : int128 =
  let pl,ph,pm = kara_acc triples (word 0) (word 0) (word 0) in
  karatsuba_reduce_shared pl ph pm`;;


(* ========================================================================= *)
(* INDUCTIVE BRIDGE                                                           *)
(*                                                                           *)
(* GHASH_NBLOCK_KARATSUBA_EQ_PROP3 is proved BY INDUCTION on the block list  *)
(* via three structural lemmas:                                               *)
(*                                                                           *)
(*   1. KARATSUBA_REDUCE_AS_PROP3_CLEAN:                                     *)
(*      karatsuba_reduce_shared pl ph pm =                                    *)
(*        word_reversefields 8 (polyval_reduce_prop3 (pack_corrected pl ph pm)) *)
(*      (i.e., the assembly-shape Barrett reduction equals prop3 on the      *)
(*       Karatsuba-corrected packed value, modulo a final byte-reversal.)    *)
(*                                                                           *)
(*   2. KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN:                                 *)
(*      pack_corrected (pl_k, ph_k, pm_k) = pmul input_k h_k (256-bit)        *)
(*      under the precondition that hk's low half = karatsuba_mid h_k.        *)
(*                                                                           *)
(*   3. PACK_CORRECTED_XOR (additivity / linearity):                          *)
(*      pack_corrected commutes with XOR in all three arguments.              *)
(*                                                                           *)
(* From these three the inductive bridge follows: kara_acc XOR-folds         *)
(* per-block (pl, ph, pm); pack distributes over XOR; each block contributes *)
(* pmul input_k h_k; the total equals XOR of pmul input_k h_k; then          *)
(* karatsuba_reduce_shared = prop3 on this total.                             *)
(*                                                                           *)
(* The N=1, 2, 3, ..., 8 bridges are derived from this inductive bridge      *)
(* + GHASH_POLYVAL_ACC_<N> (from ghash_spec.ml).                              *)
(* ========================================================================= *)

(* Pack-corrected: combines (pl, ph, pm) into the 256-bit Karatsuba layout
   (with mid corrected by ⊕ pl ⊕ ph). *)
let pack_corrected = new_definition
 `pack_corrected (pl:int128) (ph:int128) (pm:int128) :256 word =
   word_xor (word_xor
     (word_zx pl :256 word)
     (word_shl (word_zx (word_xor (word_xor pl ph) pm) :256 word) 64))
    (word_shl (word_zx ph :256 word) 128)`;;

(* Lemma 1: structural identity karatsuba_reduce_shared = prop3 ∘ pack_corrected *)
let KARATSUBA_REDUCE_AS_PROP3 = prove
 (`!pl ph pm:int128.
    karatsuba_reduce_shared pl ph pm =
    word_reversefields 8 (polyval_reduce_prop3
      (word_xor (word_xor
        (word_zx pl :256 word)
        (word_shl (word_zx (word_xor (word_xor pl ph) pm) :256 word) 64))
       (word_shl (word_zx ph :256 word) 128)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[karatsuba_reduce_shared; polyval_reduce_prop3;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[KARATSUBA_LIMBS] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  ABBREV_TAC `(plL:(64)word) = word_subword (pl:(128)word) (0,64)` THEN
  ABBREV_TAC `(plH:(64)word) = word_subword (pl:(128)word) (64,64)` THEN
  ABBREV_TAC `(phL:(64)word) = word_subword (ph:(128)word) (0,64)` THEN
  ABBREV_TAC `(phH:(64)word) = word_subword (ph:(128)word) (64,64)` THEN
  ABBREV_TAC `(pmL:(64)word) = word_subword (pm:(128)word) (0,64)` THEN
  ABBREV_TAC `(pmH:(64)word) = word_subword (pm:(128)word) (64,64)` THEN
  SUBGOAL_THEN
    `word_xor (word_xor (plH:(64)word)
                (word_xor (word_xor pmL phL) plL))
              (word_subword (word_pmul plL
                              (word 13979173243358019584:(64)word):(128)word)
                            (0,64):(64)word) =
     word_xor (word_xor plH
                (word_xor (word_xor plL phL) pmL))
              (word_subword (word_pmul plL
                              (word 13979173243358019584:(64)word):(128)word)
                            (0,64):(64)word):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC
    `qBig = word_pmul (word_xor (plH:(64)word)
                         (word_xor (word_xor plL phL) pmL))
                      (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC
    `qSmall = word_pmul (plL:(64)word)
                        (word 13979173243358019584:(64)word):(128)word` THEN
  ABBREV_TAC `qBigL = word_subword (qBig:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qBigH = word_subword (qBig:(128)word) (64,64):(64)word` THEN
  ABBREV_TAC `qSmallL = word_subword (qSmall:(128)word) (0,64):(64)word` THEN
  ABBREV_TAC `qSmallH = word_subword (qSmall:(128)word) (64,64):(64)word` THEN
  BINOP_TAC THENL [CONV_TAC WORD_RULE; CONV_TAC WORD_RULE]);;

let KARATSUBA_REDUCE_AS_PROP3_CLEAN = prove
 (`!pl ph pm:int128.
    karatsuba_reduce_shared pl ph pm =
    word_reversefields 8 (polyval_reduce_prop3 (pack_corrected pl ph pm))`,
  REWRITE_TAC[pack_corrected; KARATSUBA_REDUCE_AS_PROP3]);;

(* Lemma 2: per-block pack identity *)
let KARATSUBA_BLOCK_PACKS_TO_PMUL = prove
 (`!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==>
    (word_xor (word_xor
        (word_zx (karatsuba_block_pl input (byteswap128 h)) :256 word)
        (word_shl (word_zx (word_xor (word_xor
            (karatsuba_block_pl input (byteswap128 h))
            (karatsuba_block_ph input (byteswap128 h)))
          (karatsuba_block_pm input hk)) :256 word) 64))
       (word_shl (word_zx (karatsuba_block_ph input (byteswap128 h)) :256 word) 128)) =
    word_pmul input h : 256 word`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[karatsuba_block_pl; karatsuba_block_ph; karatsuba_block_pm;
              BYTESWAP128_SUBWORD_LO; BYTESWAP128_SUBWORD_HI] THEN
  ASM_REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `(p1:(128)word) = word_pmul (word_subword (input:(128)word) (0,64):(64)word)
                                          (word_subword (h:(128)word) (0,64):(64)word)` THEN
  ABBREV_TAC `(p2:(128)word) = word_pmul (word_subword (input:(128)word) (64,64):(64)word)
                                          (word_subword (h:(128)word) (64,64):(64)word)` THEN
  ABBREV_TAC `(p3:(128)word) = word_pmul
                                  (word_xor (word_subword (input:(128)word) (0,64):(64)word)
                                            (word_subword (input:(128)word) (64,64):(64)word))
                                  (word_xor (word_subword (h:(128)word) (0,64):(64)word)
                                            (word_subword (h:(128)word) (64,64):(64)word))` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC WORD_RULE);;

let KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN = prove
 (`!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==>
    pack_corrected
      (karatsuba_block_pl input (byteswap128 h))
      (karatsuba_block_ph input (byteswap128 h))
      (karatsuba_block_pm input hk) =
    word_pmul input h : 256 word`,
  REWRITE_TAC[pack_corrected; KARATSUBA_BLOCK_PACKS_TO_PMUL]);;

(* Lemma 3: pack_corrected is XOR-additive in each argument *)
let PACK_CORRECTED_XOR = prove
 (`!pl1 ph1 pm1 pl2 ph2 pm2:int128.
   pack_corrected (word_xor pl1 pl2) (word_xor ph1 ph2) (word_xor pm1 pm2) =
   word_xor (pack_corrected pl1 ph1 pm1) (pack_corrected pl2 ph2 pm2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pack_corrected; WORD_ZX_XOR; WORD_SHL_XOR] THEN
  CONV_TAC WORD_RULE);;

(* Linearity of kara_acc: starting at non-zero (pl0, ph0, pm0) is the same as
   starting at (0,0,0) and XOR-ing the result with the start. *)
let KARA_ACC_CONS_DESTR = prove
 (`!input h_tw hk rest pl0 ph0 pm0.
    kara_acc (CONS (input,h_tw,hk) rest) pl0 ph0 pm0 =
    kara_acc rest
      (word_xor pl0 (karatsuba_block_pl input h_tw))
      (word_xor ph0 (karatsuba_block_ph input h_tw))
      (word_xor pm0 (karatsuba_block_pm input hk))`,
  REWRITE_TAC[kara_acc]);;

let KARA_ACC_FIRST = prove
 (`!triples (pl0:int128) (ph0:int128) (pm0:int128).
    kara_acc triples pl0 ph0 pm0 =
    (let (pl', ph', pm') = kara_acc triples (word 0) (word 0) (word 0) in
     (word_xor pl0 pl', word_xor ph0 ph', word_xor pm0 pm'))`,
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL
   [REWRITE_TAC[kara_acc; LET_DEF; LET_END_DEF; WORD_XOR_0];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`input:int128`; `h_tw:int128`; `hk:int128`;
                        `rest:(int128#int128#int128)list`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[KARA_ACC_CONS_DESTR] THEN
    FIRST_X_ASSUM(fun ih ->
      ONCE_REWRITE_TAC[ih] THEN
      MP_TAC(SPECL [`word_xor (word 0:int128)
                              (karatsuba_block_pl input h_tw)`;
                    `word_xor (word 0:int128)
                              (karatsuba_block_ph input h_tw)`;
                    `word_xor (word 0:int128)
                              (karatsuba_block_pm input hk)`] ih)) THEN
    REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(fun th ->
      ABBREV_TAC `acc_zero = kara_acc rest (word 0:int128) (word 0:int128) (word 0:int128)` THEN
      MP_TAC th) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    SPEC_TAC(`acc_zero:int128#int128#int128`,`q:int128#int128#int128`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE]);;

(* Quad-list = (input, h_tw, hk, h_true) per block. Used to express the bridge
   precondition (every triple must come from a real `h` with byteswap128 + mid). *)
let kara_quad_pmul = define
  `(kara_quad_pmul ([]:(int128#int128#int128#int128)list) (acc:256 word) = acc) /\
   (kara_quad_pmul (CONS (input,h_tw,hk,h) qrest) acc =
     kara_quad_pmul qrest (word_xor acc (word_pmul input h:256 word)))`;;

let kara_quad_ok = define
  `(kara_quad_ok ([]:(int128#int128#int128#int128)list) <=> T) /\
   (kara_quad_ok (CONS (input,h_tw,hk,h) qrest) <=>
     h_tw = byteswap128 h /\
     word_subword hk (0,64):(64)word = karatsuba_mid h /\
     kara_quad_ok qrest)`;;

let project_triples = define
  `(project_triples ([]:(int128#int128#int128#int128)list) = []:(int128#int128#int128)list) /\
   (project_triples (CONS (input,h_tw,hk,h) qrest) =
     CONS (input,h_tw,hk) (project_triples qrest))`;;

(* The key inductive helper: kara_acc on the projected triples, packed,
   equals kara_quad_pmul (XOR of pmul input_k h_k). *)
let KARA_ACC_PACK_HELPER = prove
 (`!quads (acc:256 word).
    kara_quad_ok quads
    ==>
    (let pl,ph,pm = kara_acc (project_triples quads)
                              (word 0:int128) (word 0:int128) (word 0:int128) in
     kara_quad_pmul quads acc = word_xor acc (pack_corrected pl ph pm))`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[kara_quad_ok; project_triples; kara_quad_pmul; kara_acc;
                LET_DEF; LET_END_DEF; pack_corrected;
                WORD_ZX_0; WORD_SHL_ZERO; WORD_XOR_0] THEN
    GEN_TAC THEN CONV_TAC WORD_BLAST;
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`input:int128`; `h_tw:int128`; `hk:int128`;
                        `h:int128`; `qrest:(int128#int128#int128#int128)list`] THEN
    DISCH_TAC THEN GEN_TAC THEN
    REWRITE_TAC[kara_quad_ok; kara_quad_pmul; project_triples;
                KARA_ACC_CONS_DESTR; WORD_XOR_0_LEFT; WORD_XOR_0] THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[KARA_ACC_FIRST] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `word_xor (acc:256 word)
                                          (word_pmul (input:int128) (h:int128):256 word)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    SPEC_TAC(`kara_acc (project_triples (qrest:(int128#int128#int128#int128)list))
                       (word 0:int128) (word 0:int128) (word 0:int128)`,
             `q:int128#int128#int128`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`pl':int128`; `ph':int128`; `pm':int128`] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`input:int128`; `h:int128`; `hk:int128`]
                 KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM PACK_CORRECTED_XOR] THEN
    REWRITE_TAC[PACK_CORRECTED_XOR] THEN
    CONV_TAC WORD_RULE]);;

(* THE INDUCTIVE BRIDGE *)
let GHASH_NBLOCK_KARATSUBA_EQ_PROP3 = prove
 (`!quads.
    kara_quad_ok quads
    ==>
    ghash_Nblock_karatsuba (project_triples quads) =
    word_reversefields 8
      (polyval_reduce_prop3 (kara_quad_pmul quads (word 0:256 word)))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ghash_Nblock_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[KARATSUBA_REDUCE_AS_PROP3_CLEAN] THEN
  MP_TAC(SPECL [`quads:(int128#int128#int128#int128)list`; `word 0:256 word`]
               KARA_ACC_PACK_HELPER) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  SPEC_TAC(`kara_acc (project_triples (quads:(int128#int128#int128#int128)list))
                     (word 0:int128) (word 0:int128) (word 0:int128)`,
           `q:int128#int128#int128`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`pl:int128`; `ph:int128`; `pm:int128`] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_XOR_0_LEFT]);;
