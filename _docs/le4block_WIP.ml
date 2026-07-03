(* ============================================================================
   LE4BLOCK (AES-GCM-256 decrypt, 49-63 byte band, nfull=3) — WORK IN PROGRESS.

   bit_len = 384 + 8*bl1, 1<=bl1<=16: THREE full ciphertext blocks 0,1,2 + one
   MASKED partial tail block 3.  Mirrors le3block (nfull=2) with one extra full
   GHASH round (more_than_3 at 0x1074); whole-4-block case = bl1=16 endpoint.

   needs the le3block band file (brings EXEC, GMULT machinery, bubble_fix,
   BYTE_LIST_AT_NBLOCK_CTR, INPUT bridges, the front/store/tail tactic templates).

   PROGRESS (2026-06-29):
   - DONE (all instant/cheap, proven in this file): the FAST GMULTn builder
     (PACK_N in ~0.3s, NOT the old ~373s WORD_RULE), GMULT4_FULL_CORRECT_BA,
     spec_to_byteform_4, and the cascade helpers (USHR_384, X5_ZERO_LEMMA4,
     IVAL_*_LE64, X1_MOD128_BRIDGE4, GCM_CTR_INC3_LANES, AES_CTR_4_EL).
   - TODO: the ARM simulation BODY (front 1..~? to more_than_3, 3 full stores +
     masked tail store, bridge at s(381+round_len) after the shared eor v19,v19,v18),
     then the readable two-layer wrapper (INPUT_BYTES_FULL N=4 + BYTE_LIST_AT_NBLOCK_CTR
     nfull=3 + AES_CTR_4_EL).

   KEY DESIGN ANSWER (from objdump, b.gt strict cascade): LE-N band (nfull) covers
   bytes [16*nfull+1, 16*(nfull+1)] INCLUSIVE; bl1=16 endpoint = whole-(N+1)-block
   (all-ones mask = full block).  So LE4BLOCK INCLUDES the whole-4-block (64 byte)
   case; whole-3-block (48 byte) is already inside LE3BLOCK.  No separate whole-block
   theorems needed.
   ============================================================================ *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_le3block.ml";;

(* ===========================================================================
   PART 0 — the FAST, REUSABLE GMULTn builder (back-portable optimization).
   Replaces the hand-written dec3_tL + ~373s monolithic WORD_RULE PACK3_ID.
   PACK_N is proved compositionally: decN_tL = XOR_k dec1[k]  (structural XOR-AC
   via WORD_XOR_ACI, opaque pmul atoms, NO bit-blast) then per-block PACK1.
   =========================================================================== *)

let mk_sub v lo = mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, v), mk_pair(mk_small_numeral lo,`64`));;
let blk_lo k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, mk_sub a 0), mk_sub b 0);;
let blk_hi k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, mk_sub a 64), mk_sub b 64);;
let blk_mid k =
  let a = mk_var(Printf.sprintf "a%d" k,`:int128`) and b = mk_var(Printf.sprintf "b%d" k,`:int128`) in
  let xa = mk_comb(mk_comb(`word_xor:64 word->64 word->64 word`, mk_sub a 0), mk_sub a 64) in
  let xb = mk_comb(mk_comb(`word_xor:64 word->64 word->64 word`, mk_sub b 0), mk_sub b 64) in
  let pmid = mk_comb(mk_comb(`word_pmul:64 word->64 word->128 word`, xa), xb) in
  let xor128 x y = mk_comb(mk_comb(`word_xor:128 word->128 word->128 word`,x),y) in
  xor128 (xor128 pmid (blk_lo k)) (blk_hi k);;
let xor_fold128 f n =
  let xs = map f (0--(n-1)) in
  let rec go = function [x] -> x | x::xs -> mk_comb(mk_comb(`word_xor:128 word->128 word->128 word`,x), go xs) | [] -> failwith "empty" in
  go xs;;
let mk_decN_tL n =
  let zx t = mk_comb(`word_zx:128 word->256 word`, t) in
  let shl t k = mk_comb(mk_comb(`word_shl:256 word->num->256 word`, t), mk_small_numeral k) in
  let xor256 x y = mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`,x),y) in
  xor256 (xor256 (zx (xor_fold128 blk_lo n)) (shl (zx (xor_fold128 blk_mid n)) 64))
         (shl (zx (xor_fold128 blk_hi n)) 128);;
let mk_packed_L n =
  let term k = let a=mk_var(Printf.sprintf "a%d" k,`:int128`) and b=mk_var(Printf.sprintf "b%d" k,`:int128`) in
               mk_comb(mk_comb(`word_pmul:int128->int128->256 word`,a),b) in
  match map term (0--(n-1)) with
  | x::rest -> List.fold_left (fun acc y -> mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`,acc),y)) x rest
  | [] -> failwith "";;
let blkvars n = List.concat (map (fun k -> [mk_var(Printf.sprintf "a%d" k,`:int128`); mk_var(Printf.sprintf "b%d" k,`:int128`)]) (0--(n-1)));;
let dec1_at k =
  subst [mk_var(Printf.sprintf "a%d" k,`:int128`),`a0:int128`;
         mk_var(Printf.sprintf "b%d" k,`:int128`),`b0:int128`] (mk_decN_tL 1);;
let xor256_fold ts = match ts with
  | x::r -> List.fold_left (fun a y->mk_comb(mk_comb(`word_xor:256 word->256 word->256 word`,a),y)) x r
  | []->failwith"";;
(* decN_tL = XOR_k dec1[k], structural XOR-AC (no bit-blast) *)
let build_SPLIT n =
  let lf = REWRITE_CONV[WORD_ZX_XOR; WORD_SHL_XOR] (mk_decN_tL n)
  and rf = REWRITE_CONV[WORD_ZX_XOR; WORD_SHL_XOR] (xor256_fold (map dec1_at (0--(n-1)))) in
  TRANS lf (TRANS (AC WORD_XOR_ACI (mk_eq(rhs(concl lf), rhs(concl rf)))) (SYM rf));;
let pack1_at k =
  let ak=mk_var(Printf.sprintf "a%d" k,`:int128`) and bk=mk_var(Printf.sprintf "b%d" k,`:int128`) in
  prove(mk_eq(dec1_at k, mk_comb(mk_comb(`word_pmul:int128->int128->256 word`,ak),bk)),
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REWRITE_RULE[LET_DEF;LET_END_DEF] PMUL_KARATSUBA] THEN
    REWRITE_TAC[WORD_ZX_XOR; WORD_SHL_XOR] THEN CONV_TAC WORD_RULE);;
let build_PACKn n =
  let split = build_SPLIT n in
  TRANS split (GEN_REWRITE_CONV ONCE_DEPTH_CONV (map pack1_at (0--(n-1))) (rhs(concl split)));;
let build_GMULTn_fast n =
  let pack_id = build_PACKn n in
  let tL = lhs(concl pack_id) in
  let gmr = REWRITE_RULE[REWRITE_RULE[LET_DEF;LET_END_DEF] KARATSUBA_LIMBS]
              (SPEC tL (REWRITE_RULE[LET_DEF;LET_END_DEF] GMULT_REDUCE_PROP3)) in
  (pack_id, GENL (blkvars n) (TRANS gmr (AP_TERM `polyval_reduce_prop3` pack_id)));;

(* GMULT4 (the le4block bridge lemma) — instant via the fast builder. *)
let PACK4_ID, GMULT4_FULL_CORRECT_BA = build_GMULTn_fast 4;;

(* ===========================================================================
   PART 1 — LE4BLOCK cascade/counter helper lemmas (bound 48+bl1<=64, x5=word(48+bl1)).
   =========================================================================== *)

let USHR_384_8BL_LEMMA = prove
 (`!bl1. bl1 <= 16 ==> word_ushr (word (384 + 8 * bl1):int64) 3 = word (48 + bl1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val (word (384 + 8 * bl1):int64) = 384 + 8 * bl1`
   (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let X5_ZERO_LEMMA4 = prove
 (`!bl1. 1 <= bl1 /\ bl1 <= 16
        ==> word_and (word_sub (word (48 + bl1)) (word 1):int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [WORD_RULE `word_sub (word (48 + bl1):int64) (word 1) = word (47 + bl1)`] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `j < 7` THENL
   [REPEAT DISJ2_TAC THEN
    SUBGOAL_THEN `~bit j (word 18446744073709551488:int64)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `j < 7` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[BIT_WORD] THEN
    SUBGOAL_THEN `47 + bl1 < 2 EXP j` (fun th -> SIMP_TAC[th; DIV_LT; ODD; DE_MORGAN_THM]) THEN
    TRANS_TAC LTE_TRANS `2 EXP 7` THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]]);;

let IVAL_WORD_LE64 = prove
 (`!b. b <= 64 ==> ival (word b:int64) = &b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival] THEN
  SUBGOAL_THEN `val (word b:int64) = b` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_SIMP_TAC[ARITH_RULE `b <= 64 ==> b < 2 EXP (64 - 1)`]);;

let IVAL_WSUB_LE64 = prove
 (`!b k. b <= 64 /\ k <= 112
          ==> ival (word_sub (word b) (word k):int64) = &b - &k`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let X1_MOD128_BRIDGE4 = prove
 (`!bl1. bl1 <= 16
    ==> word_and (word (384 + 8 * bl1):int64) (word 127) =
        word_and (word (8 * bl1):int64) (word 127)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val (word (384 + 8 * bl1):int64) = 384 + 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (8 * bl1):int64) = 8 * bl1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `384 + 8 * bl1 = 8 * bl1 + 3 * 128`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let GCM_CTR_INC3_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`,
        subst [`word 3:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

let AES_CTR_4_EL = prove
 (`EL 0 (aes_ctr ctr0 [pt0;pt1;pt2;pt3] keys) = word_xor pt0 (aes256_encrypt ctr0 keys) /\
   EL 1 (aes_ctr ctr0 [pt0;pt1;pt2;pt3] keys) =
     word_xor pt1 (aes256_encrypt (gcm_ctr_inc ctr0) keys) /\
   EL 2 (aes_ctr ctr0 [pt0;pt1;pt2;pt3] keys) =
     word_xor pt2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)) keys) /\
   EL 3 (aes_ctr ctr0 [pt0;pt1;pt2;pt3] keys) =
     word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))) keys)`,
  REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_block; gcm_ctr_inc_iter] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_1; gcm_ctr_inc_iter] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; ARITH_RULE `2 = SUC(SUC 0)`; ARITH_RULE `3 = SUC(SUC(SUC 0))`; EL; HD; TL] THEN
  REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_INC_ITER_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[gcm_ctr_inc_iter]);;

(* spec-side fold for 4 blocks: ghash_polyval_acc 4-block = prop3 of the H-power
   pmul-sum, under the LEFT-NESTED h2/h3/h4 byteswap relations (matching the
   htable's actual H-power layout that GHASH_POLYVAL_ACC_4 produces). *)
let spec_to_byteform_4 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cphm] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h4))
           (word_pmul (word_bytereverse cph1) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h2)))
         (word_pmul (word_bytereverse cphm) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cphm:int128`] GHASH_POLYVAL_ACC_4)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ===========================================================================
   TODO PART 2 — the ARM simulation BODY + readable two-layer wrapper.
   The front/store/tail templates from le3block (the full_le3_tac front/stores/tail)
   generalize with: one extra full-block GHASH round (more_than_3 at 0x1074), 3 full
   stores + masked tail, bridge after the SHARED eor v19,v19,v18.

   PC MAP (objdump): cascade #112/96/80/64 fall through (resolvers IDENTICAL to
   le3block's dec_bl3_resolve at 270/282/290/297), then #48 is TAKEN ->
   more_than_3 = pc+4212 (0x1074).  more_than_3 (0x1074..0x10b4) = one full H^4
   GHASH round, then falls into more_than_2 (0x10b8, H^3), more_than_1 (0x10f4, H^2),
   less_than_1 (0x1138, masked tail vs H), shared reduction (eor v19,v19,v18 at
   0x11d4, rev64 0x11dc, st1 xi 0x11e0).  Exit pc+4576 (0x11e0) region.

   *** HTABLE PACKING (critical, discovered from objdump) ***
   The register at [x6,#64] (le3block named it h3k) is PACKED:
     - LOW  64 bits = h3's Karatsuba mid (h3k), used by the H^3 round via `pmull` (.1d);
       le3block already constrains this: word_subword h3k (0,64) = h3 lo ^ h3 hi.
     - HIGH 64 bits = h4's Karatsuba mid (h4k), used by the H^4 round via
       `pmull2 v27,v27.2d,v24.2d` (.2d = high half).  NEW for le4block:
         word_subword h3k (64,64) = word_xor (word_subword h4 (0,64)) (word_subword h4 (64,64)).
   And [x6,#80] = h4 (H^4), a NEW read.  So le4block PRECOND = le3block precond
   + read h4 at htbl_p+80 + the h3k-high-half constraint + (for the bridge)
   byteswap128 h4 = polyval_dot(polyval_dot(polyval_dot(bsw h)(bsw h))(bsw h))(bsw h)
   (LEFT-nested, per spec_to_byteform_4 above — NOTE le3block's h3 precond is
   RIGHT-nested `polyval_dot (bsw h)(polyval_dot (bsw h)(bsw h))`; for le4 the h3
   precond must ALSO be re-stated left-nested `polyval_dot(polyval_dot(bsw h)(bsw h))(bsw h)`
   to match GHASH_POLYVAL_ACC_4 — or bridged. RECONCILE during the close.)

   STORES: 3 full plaintext stores pt0/pt1/pt2 (st1 at 0x108c, 0x10d0, 0x110c) +
   masked tail pt3 (GCM_CTR_INC3_LANES for the +3 counter), masked store at out_p+48.

   BRIDGE: at s(381 + round_len) after the H^4 round's extra steps; read Q19 =
   ghash_polyval_acc (bsw h)(brev xi)[brev cph0;brev cph1;brev cph2;brev cphm];
   close via spec_to_byteform_4 + GSYM GMULT4_FULL_CORRECT_BA + the SAME
   MERGE/qq-fold/wa-wv-unify/opaque/QQ0SPLIT/bubble_fix pipeline (more qq atoms,
   bubble_fix flat).  The BRIDGE_CLOSE_TAC from le3block generalizes in shape.

   READABLE WRAPPER (sim-free, after BODY): INPUT_BYTES_FULL at N=4 (4 lane reads) +
   BYTE_LIST_AT_NBLOCK_CTR at nfull=3 + AES_CTR_4_EL, via ENSURES_PRE/POSTCONDITION_THM
   (witness: BODY pre for PRE, BODY post for POST — apply PRE then POST).
   =========================================================================== *)

(* ---- LE4BLOCK_BODY goal builder (term surgery on the le3block BODY concl).
   VERIFIED: type-checks (37 vars), and the adapted front tactic runs the prologue
   (steps 1-5 + USHR_384 fold to word(48+bl1)) cleanly.  This is the resumable goal
   for the ARM-sim BODY proof.  When the BODY is proved, the FINAL band file writes
   this goal out EXPLICITLY (no surgery), per the readable-spec convention. ---- *)
let keys15 = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;
let build_le4_body_goal () =
  let vs3, bod3 = strip_forall (concl AESV8_GCM_8X_DEC_256_LE3BLOCK_BODY) in
  let hyp3, ens3 = dest_imp bod3 in
  let pre3 = rand(rator(rator ens3)) and post3 = rand(rator ens3) and frame3 = rand ens3 in
  let (sv,preb) = dest_abs pre3 and (_,postb) = dest_abs post3 in
  (* HYP: bump nonoverlapping out_p/in_p 48->64; restate h3 left-nested; add h4 + h3k-hi *)
  let isNonov c = try fst(dest_const(rator(rator c)))="nonoverlapping" with _->false in
  let bump c = subst [`(out_p:int64,64)`,`(out_p:int64,48)`; `(in_p:int64,64)`,`(in_p:int64,48)`] c in
  let hypL = map (fun c -> if isNonov c then bump c else c) (conjuncts hyp3) in
  let h3_old = `byteswap128 (h3:int128) = polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h))` in
  let h3_new = `byteswap128 (h3:int128) = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)` in
  let h4_new = `byteswap128 (h4:int128) = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)` in
  let h3k_hi = `word_subword (h3k:int128) (64,64) :64 word = word_xor (word_subword (h4:int128) (0,64):64 word) (word_subword h4 (64,64))` in
  let hypL = List.concat_map (fun c -> if c = h3_old then [h3_new; h4_new; h3k_hi] else [c]) hypL in
  let hyp4 = list_mk_conj hypL in
  (* PRE: byte_len 384; add cph3 read in_p+48; add h4 read htbl_p+80; outprev moves to out_p+48 *)
  let preL = map (fun c -> subst [`word (384 + 8 * bl1):int64`,`word (256 + 8 * bl1):int64`] c) (conjuncts preb) in
  let preL = List.concat_map (fun c -> if c = `read (memory :> bytes128 (word_add in_p (word 32))) s = cph2`
                then [c; `read (memory :> bytes128 (word_add in_p (word 48))) s = cph3`] else [c]) preL in
  let preL = List.concat_map (fun c -> if c = `read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k`
                then [c; `read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4`] else [c]) preL in
  let preL = map (subst [`word_add out_p (word 48):int64`,`word_add out_p (word 32):int64`]) preL in
  let pre4 = mk_abs(sv, list_mk_conj preL) in
  (* POST: 4 stores + 4-block GHASH list *)
  let enc k blk = mk_comb(mk_comb(`word_xor:int128->int128->int128`, blk),
                          mk_comb(mk_comb(`aes256_encrypt`, k), keys15)) in
  let ctr1 = `gcm_ctr_inc ctr0` and ctr2 = `gcm_ctr_inc (gcm_ctr_inc ctr0)`
  and ctr3 = `gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))` in
  let mk = `word (2 EXP (8 * bl1) - 1):int128` and notmk = `word_not (word (2 EXP (8 * bl1) - 1)):int128` in
  let blend body = mk_comb(mk_comb(`word_xor:int128->int128->int128`,
     mk_comb(mk_comb(`word_and:int128->int128->int128`, body), mk)),
     mk_comb(mk_comb(`word_and:int128->int128->int128`, `outprev:int128`), notmk)) in
  let post4L = [
    `read PC s = word (pc + 4576)`;
    mk_eq(`read (memory :> bytes128 out_p) s`, enc `ctr0:int128` `cph0:int128`);
    mk_eq(`read (memory :> bytes128 (word_add out_p (word 16))) s`, enc ctr1 `cph1:int128`);
    mk_eq(`read (memory :> bytes128 (word_add out_p (word 32))) s`, enc ctr2 `cph2:int128`);
    mk_eq(`read (memory :> bytes128 (word_add out_p (word 48))) s`, blend (enc ctr3 `cph3:int128`));
    mk_eq(`read (memory :> bytes128 xi_p) s`,
          `word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
               word_bytereverse (word_and cph3 (word (2 EXP (8 * bl1) - 1)))])`)] in
  let post4 = mk_abs(sv, list_mk_conj post4L) in
  let frame4 = subst [`(out_p:int64,64)`,`(out_p:int64,48)`] frame3 in
  list_mk_forall(vs3 @ [`cph3:int128`; `h4:int128`],
                 mk_imp(hyp4, list_mk_comb(`ensures arm`,[pre4;post4;frame4])));;

(* The front tactic (adapted from le3block full_le3_tac_front): prologue + CTR/AES bulk +
   cascade #112/96/80/64 fall-through (dec_bl3_resolve IDENTICAL) then #48 TAKEN.

   FRONT-SIM VALIDATED LIVE (2026-06-29) through the cascade:
   - prologue 1-5 + USHR_384 fold -> X9=word(48+bl1): OK
   - CTR/AES bulk 6-254: OK, s254 = pc+1040 (identical to le3block)
   - X5_ZERO_LEMMA4 collapse + tail-entry 255-265: OK, s265 = pc+3788
   - 266-269 + pt0 abbrev: OK, s269 = pc+3804
   - cascade #112 (dec_bl4_resolve 270 112 3808), #96 (282 96 3856), #80 (290 80 3888): OK
   - #64 IS A BOUNDARY (48+bl1 can = 64 at bl1=16; b.gt strict => still falls through).
     Use bl4_resolve_pc_bdy 297 64 3916 (the =64 case + <64 case both make b.gt false).
     *** OPEN ISSUE: bl4_resolve_pc_bdy + dec_bl4_resolve_stale at #64 leaves NO clean
     `read PC s297` assumption (the stale-scrubber's >1-word-term test eats the fresh
     resolved PC, OR the ASM_CASES merge doesn't re-assert it), so the next ARM_STEPS
     (s298) fails "mk_comb: types do not agree".  FIX NEEDED: a #64 boundary resolver
     that resolves PC to pc+3916 (fall-through) and KEEPS that as a clean assumption
     WITHOUT the stale-scrub discarding it (or scrub only the OLD multi-word PC, keep new).
     Likely: drop dec_bl4_resolve_stale after the #64 bdy, or make _bdy end by
     re-ASSUME-ing `read PC s297 = word(pc+3916)`.
   - #64 stale-scrub IS correct (keeps clean PC, drops the conditional one); my first
     s298 failure was a transient state-numbering issue, not the scrub.
   - then #48 TAKEN: bl4_resolve_pc48_taken 303 4212 -> more_than_3 (pc+4212). VALIDATED. *)

(* ---- LE4 cascade resolvers (bound 48+bl1<=64, x5=word(48+bl1)) ---- *)
let bl4_resolve_pc sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `48 + bl1 <= 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`48 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE64) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE64] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN (parse_term (Printf.sprintf "&(48 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
     [MP_TAC(ASSUME `bl1 <= 16`) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]; ALL_TAC]);;
let bl4_resolve_pc_bdy sN k fall =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s fall)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `48 + bl1 <= 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`48 + bl1:num`; mk_small_numeral k] IVAL_WSUB_LE64) THEN
    ASM_SIMP_TAC[IVAL_WORD_LE64] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC (parse_term (Printf.sprintf "48 + bl1 = %d" k)) THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      SUBGOAL_THEN (parse_term (Printf.sprintf "&(48 + bl1) - &%d:int < &0" k)) ASSUME_TAC THENL
       [MP_TAC(ASSUME `bl1 <= 16`) THEN MP_TAC(ASSUME (parse_term (Printf.sprintf "~(48 + bl1 = %d)" k))) THEN
        REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[TAUT `(a /\ F) = F`; COND_CLAUSES]]; ALL_TAC]);;
let bl4_resolve_pc48_taken sN target =
  let s = Printf.sprintf "s%d" sN in
  (SUBGOAL_THEN (parse_term (Printf.sprintf "read PC %s = word (pc + %d)" s target)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_eq(concl th)) = parse_term(Printf.sprintf "read PC %s" s) with _ -> false) then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `word_sub (word (48+bl1):int64) (word 48) = word bl1` (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    SUBGOAL_THEN `val (word bl1:int64) = bl1` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[IVAL_WORD_LE64; ARITH_RULE `bl1 <= 16 ==> bl1 <= 64`; ARITH_RULE `bl1 <= 16 ==> 48 + bl1 <= 64`] THEN
    SUBGOAL_THEN `~(bl1 = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(48+bl1) - &48:int = &bl1` (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `~(&bl1:int < &0)`];
    ALL_TAC]);;
let dec_bl4_resolve_stale = dec_bl3_resolve_stale;;
let dec_bl4_resolve sN k fall = bl4_resolve_pc sN k fall THEN dec_bl4_resolve_stale;;

(* FRONT TACTIC — VALIDATED LIVE end-to-end to s303=more_than_3 (pc+4212), ~120s. *)
let full_le4_tac_front =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C_ARGUMENTS;SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (1--5) THEN
  MP_TAC(SPEC `bl1:num` USHR_384_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [3;4;5;6;7]) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (31--84) THEN mk_discard2 [3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (85--173) THEN mk_discard2 [3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (174--177) THEN GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (178--184) THEN mk_discard2 [3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (185--254) THEN mk_discard2 [3;4;5;6;7;30] THEN GCM_SIMD_SIMPLIFY_TAC THEN
  MP_TAC(SPEC `bl1:num` X5_ZERO_LEMMA4) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [255] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (256--265) THEN mk_discard2 [3;4;5;6;30] THEN
  MP_TAC(SPEC `bl1:num` USHR_384_8BL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub (word_add in_p (word (48 + bl1):int64)) in_p = word (48 + bl1)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (266--269) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt0:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph0:int128`),mk_comb(mk_comb(`aes256_encrypt`,`ctr0:int128`),keys15)))) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (270--270) THEN dec_bl4_resolve 270 112 3808 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (271--282) THEN dec_bl4_resolve 282 96 3856 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (283--290) THEN dec_bl4_resolve 290 80 3888 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (291--297) THEN bl4_resolve_pc_bdy 297 64 3916 THEN dec_bl4_resolve_stale THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (298--303) THEN bl4_resolve_pc48_taken 303 4212 THEN dec_bl4_resolve_stale;;

(* STORES TACTIC — VALIDATED LIVE end-to-end (2026-06-30): captures pt0/pt1/pt2 (3 full
   plaintext stores) cleanly.  pt0 store auto-folds at s312; pt1 eor3 lands at s313 (needs
   WORD_XOR_ASSOC around the aes256_encrypt expand); pt2 at s328+ (GCM_CTR_INC2_LANES).
   Each full store readback auto-folds once its pt_k abbrev exists. *)
let full_le4_tac_stores =
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (304--312) THEN
  SUBGOAL_THEN `read (memory :> bytes128 out_p) (s312:armstate) = pt0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pt0" THEN REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s312" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC [313] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph1:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc ctr0:int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt1:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph1:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc ctr0:int128`),keys15)))) THEN
  DISCARD_OLDSTATE_TAC "s313" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (314--327) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 16))) (s327:armstate) = pt1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s327" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (328--334) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph2:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc ctr0):int128`),keys15)))
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC (mk_eq(`pt2:int128`, mk_comb(mk_comb(`word_xor:int128->int128->int128`,`cph2:int128`),mk_comb(mk_comb(`aes256_encrypt`,`gcm_ctr_inc (gcm_ctr_inc ctr0):int128`),keys15)))) THEN
  DISCARD_OLDSTATE_TAC "s334" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (335--350) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add out_p (word 32))) (s350:armstate) = pt2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s350";;
(* NOTE: the masked block's UNMASKED plaintext lives in Q12 from the eor3 at pc+4384 and is
   read by the bif at s370 (pc+4476).  DISCARD_OLDSTATE "s350" above keeps `read Q12 s350`
   (the current state), which IS the carried pt3-form — but its STATE LABEL must be matched
   exactly when capturing pt3 for the masked store (the bif reads `read Q12 s369` after the
   intervening masked-GHASH steps carry Q12 forward unchanged). The masked-store capture
   (full_le4_tac_tail, TODO) must: at s369 (just before the bif), SPEC `read Q12 s369` =
   word_xor cph3 (aes256_encrypt (gcm_ctr_inc^3 ctr0) keys) [GCM_CTR_INC3_LANES + WORD_XOR_ASSOC
   + aes-expand + WORD_BLAST], ABBREV pt3; THEN step the bif (s370) so the masked-blend
   word_or(word_and (read Q12 s369) MK)(word_and outprev ~MK) folds via MASK_LEMMA/BLEND_OR_XOR.
   The earlier failures came from capturing at the wrong state label / after the bif consumed Q12. *)

(* ===========================================================================
   STORES + TAIL — VALIDATED LIVE step map (2026-06-30), bridge close still TODO.
   From s303 (more_than_3, pc+4212), stepping ARM_STEPS/VSTEPS one-at-a-time:
     - H^4 round 304..319; **pt0 store auto-folds clean at s312**:
         read (memory :> bytes128 out_p) s312 = pt0   (no manual assert needed;
         just SUBGOAL_THEN ...=pt0 ASSUME + DISCARD_OLDSTATE_TAC "s312").
     - s320 = pc+4280 = 0x10b8 = more_than_2 entry. FROM HERE the structure matches
       le3block's more_than_2 onward, shifted by the H^4 round.
     - pt1 CAPTURE GOTCHA (validated s313): the eor3 makes Q12 = word_xor (word_xor cph1
       <aese-form>) k14 (a 3-way XOR; the aes256_encrypt last-round eor k14 is the OUTER
       operand). To abbrev pt1 = word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0) keys),
       the ANTS needs ONCE_REWRITE_TAC[WORD_XOR_ASSOC] BEFORE expanding aes256_encrypt,
       then REWRITE_TAC[WORD_XOR_ASSOC] after (mirrors enc le2block's ct capture). The
       le3 dec stores did NOT need this because its pt0/pt1 captures were at clean states;
       le4's more_than_3 H^4 round changes the eor3 timing. STILL DEBUGGING this exact form.
       FURTHER FINDING: the pt1 eor3 (Q12 = word_xor(word_xor cph1 KS)k14) already executed
       by s312 (more_than_3 round, 0x1090); the readback is `read Q12 s312 = ...`, so the
       capture MESON-trick must target s312 (NOT s313 — step 313 doesn't touch Q12). General
       rule: capture each pt_k at the state where its eor3 lands, which for le4 is shifted
       into the more_than_3 round for pt1. Step-then-find-Q12-state, don't assume le3's numbers.
     - pt1 store (more_than_2, out_p+16) ~s327-331; pt2 store (more_than_1, out_p+32)
       ~s340-345.  (each more_than_K: rev64 v8; eor mask; pmull/pmull2 vs H^(K+1) +
       its mid; eor into Q17/18/19; st1 prior pt; eor3 next pt.)
     - X1_MOD128_BRIDGE4 fold before less_than_1 (~s351, pc+4404=0x1134).
     - masked tail: at s368 the `and v9,v9,v0` executes -> Q9 = word_and <cph3 form> MASK
       (cph3 present in the arg). Collapse to word_and cph3 MK via MASK_LEMMA (le3 pattern,
       cph3 not cph2). Then masked-blend store out_p+48 = word_xor(word_and pt3 MK)(word_and outprev ~MK).
     - BRIDGE: read Q19 = ghash_polyval_acc (bsw h)(brev xi)[brev cph0;brev cph1;brev cph2;brev cphm]
       at the post-`eor v19,v19,v18` state (0x11d4, after the H^4-shifted offset). Close via
       spec_to_byteform_4 + GSYM GMULT4_FULL_CORRECT_BA + le3 BRIDGE_CLOSE_TAC pipeline
       (MERGE/qq-fold/wa-wv-unify/opaque/QQ0SPLIT/bubble_fix; more qq atoms, bubble_fix flat).
       *** This 4-term bridge is the genuine remaining risk (le3's 3-term took ~8 attempts). ***
     - then rev64 + st1 xi_p (0x11e0), ENSURES_FINAL_STATE, MONOTONE_MAYCHANGE.
   RESUME: set_goal(build_le4_body_goal()); e(full_le4_tac_front);  [at s303]
     then continue the stores+tail per the map above; assemble full_le4_tac_stores/_tail;
     then AESV8_GCM_8X_DEC_256_LE4BLOCK_BODY = prove(build_le4_body_goal(), front THEN stores THEN tail).
   =========================================================================== *)
(* TODO: full_le4_tac_front / _stores / _tail, then:
   let AESV8_GCM_8X_DEC_256_LE4BLOCK_BODY = prove(build_le4_body_goal(),
     full_le4_tac_front THEN full_le4_tac_stores THEN full_le4_tac_tail);;
   then the readable wrapper AESV8_GCM_8X_DEC_256_LE4BLOCK. *)
