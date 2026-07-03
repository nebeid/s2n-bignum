(* ========================================================================= *)
(* AES-256-GCM decrypt, the genuine 2-block path of aesv8_gcm_8x_dec_256.      *)
(*                                                                            *)
(* Decrypt analog of AESV8_GCM_8X_ENC_256_2BLOCK (arm/proofs/aesv8_gcm_8x_enc_ *)
(* 256_2block.ml).  Mirror principle (see _docs/decrypt-nblock-plan.md):       *)
(*   - pt -> cph throughout the spec/abbreviations;                            *)
(*   - out_p block i = EL i (aes_ctr ctr0 [cph0;cph1] keys) (the plaintext     *)
(*     word_xor cph keystream), stored to out_p;                              *)
(*   - tag over MAP word_bytereverse (aes_ctr ...) of the CIPHERTEXT blocks    *)
(*     (dec GHASHes the loaded input ciphertext, not a computed output);       *)
(*   - block-1 counter = gcm_ctr_inc ctr0;                                     *)
(*   - GHASH 2-block fold via GHASH_POLYVAL_ACC_2, data blocks brev cph0/cph1; *)
(*   - the dec routine is 4612 bytes: nonoverlapping (word pc, 4612);          *)
(*   - the dec bridge is at the s351-analog (dec splits enc's final eor3 into   *)
(*     two eors), NOT s350.                                                    *)
(*                                                                            *)
(* No CHEAT_TAC, no new axioms.                                               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
needs "common/karatsuba_pmul.ml";;
needs "common/polyval_ghash.ml";;
(* Mila's N-block GHASH Karatsuba layer (D7 adoption): GHASH_NBLOCK_KARATSUBA_   *)
(* EQ_PROP3 closes the band GHASH conjunct in ~0.08s (vs ~73s MERGE/FINISH).     *)
needs "common/ghash_nblock_karatsuba.ml";;
(* Shared fast GMULTn bridge-lemma builder (build_GMULTn_fast n): GMULT2 built  *)
(* in ~0.1s vs the old ~1.1s hand-written dec2_tL + WORD_RULE PACK2_ID, and the *)
(* same builder serves le3/le4 (and le5..le8).                                  *)
needs "common/gmult_nblock_lemmas.ml";;
(* Counter-mode spec layer: gcm_ctr_inc + GCM_CTR_INC_LANES + gcm_ctr_inc_iter. *)
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;
(* Recursive list-based CTR ciphertext spec (aes_ctr) + 2-block reductions.     *)
needs "arm/proofs/utils/aes_ctr_spec.ml";;

(* The machine code + EXEC rule + all GHASH/Karatsuba bridge helper lemmas and  *)
(* tactics are shared with the dec 1-block proof; load that file so             *)
(* aesv8_gcm_8x_dec_256_mc / _EXEC and the helpers (GMULT_FULL_CORRECT_BA,       *)
(* ABBREV_INNER_PMULS_TAC, MERGE_PMUL_ATOMS_TAC, QQ0SPLIT, JOINMID,             *)
(* ARM_VSTEPS_FOLD_TAC, GCM_SIMD_SIMPLIFY_TAC, RESOLVE_BRANCH_TAC, ...) are in   *)
(* scope.  We only ADD the 2-block theorem; we never edit the 1-block file.     *)
needs "arm/proofs/aesv8_gcm_8x_dec_256_1block.ml";;

(* ========================================================================= *)
(* Helper lemmas for the 2-product GHASH bridge (copied verbatim from the      *)
(* encrypt 2-block proof; they are byte-form-agnostic so transfer unchanged).  *)
(* ========================================================================= *)

(* word_join lane split: reduces a 128-bit word_join equality to two 64-bit   *)
(* lane equalities (so the final close is two small flat XOR identities).      *)
let JOIN_EQ_SPLIT = prove(
  `!(a:(64)word) (b:(64)word) (c:(64)word) (d:(64)word).
     ((word_join a b:(128)word) = word_join c d) <=> (a = c /\ b = d)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th ->
      MP_TAC(REWRITE_RULE[JOIN_SUBWORD_RULES]
        (BETA_RULE(AP_TERM `\x:(128)word. word_subword x (64,64):(64)word` th))) THEN
      MP_TAC(REWRITE_RULE[JOIN_SUBWORD_RULES]
        (BETA_RULE(AP_TERM `\x:(128)word. word_subword x (0,64):(64)word` th))) THEN
      MESON_TAC[]);
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* per-lane reversefields: word_reversefields 8 on a full int128 commutes with *)
(* the 64-bit lane projection (with a lane swap).                              *)
let RF8_SUBWORD = prove(
  `(!x:int128. word_subword (word_reversefields 8 x) (0,64):64 word =
               word_reversefields 8 (word_subword x (64,64):64 word)) /\
   (!x:int128. word_subword (word_reversefields 8 x) (64,64):64 word =
               word_reversefields 8 (word_subword x (0,64):64 word))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* subword lane extraction through word_zx / word_shl of the 256-bit Karatsuba *)
(* assembly (for a 64-bit source).                                             *)
let SUBW_ZX_256 = prove(
  `(!x:64 word. word_subword (word_zx x:256 word) (0,64):64 word = x) /\
   (!x:64 word. word_subword (word_zx x:256 word) (64,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_zx x:256 word) (128,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_zx x:256 word) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL64_256 = prove(
  `(!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (0,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (64,64):64 word = x) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (128,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 64) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL128_256 = prove(
  `(!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (0,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (64,64):64 word = word 0) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (128,64):64 word = x) /\
   (!x:64 word. word_subword (word_shl (word_zx x:256 word) 128) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
(* and for a 128-bit source (the qq atoms). *)
let SUBW_ZX128_256 = prove(
  `(!x:128 word. word_subword (word_zx x:256 word) (0,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_zx x:256 word) (64,64):64 word = word_subword x (64,64)) /\
   (!x:128 word. word_subword (word_zx x:256 word) (128,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_zx x:256 word) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL64_128_256 = prove(
  `(!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (0,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (64,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (128,64):64 word = word_subword x (64,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 64) (192,64):64 word = word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_SHL128_128_256 = prove(
  `(!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (0,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (64,64):64 word = word 0) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (128,64):64 word = word_subword x (0,64)) /\
   (!x:128 word. word_subword (word_shl (word_zx x:256 word) 128) (192,64):64 word = word_subword x (64,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_XOR_256 = prove(
  `!x y:256 word. !lo. word_subword (word_xor x y) (lo,64):64 word =
     word_xor (word_subword x (lo,64)) (word_subword y (lo,64))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR]);;

(* Collapse a 64-bit lane of subword(subword(join a a)(64,128)) to a plain lane *)
(* of a (the duplicated mid-half the wv W-reduction operand produces).          *)
let SUBSUB_JOIN_DUP = prove(
  `(!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (0,64) :64 word
                 = word_subword a (64,64)) /\
   (!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (64,64) :64 word
                 = word_subword a (0,64))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Abbreviate EVERY `word_subword (a:int128) (lo,64)` subterm in the goal to a   *)
(* fresh 64-bit var, so the residual is a flat word_xor identity over 64-bit     *)
(* vars that WORD_BITWISE_TAC closes.                                            *)
let ABBREV_ALL_SUBWORDS_TAC : tactic = fun (asl,w) ->
  let is_sw64 t = try fst(dest_const(rator(rator t)))="word_subword" &&
                      type_of t = `:(64)word` &&
                      type_of (rand(rator t)) = `:int128` with _->false in
  let sws = setify(find_terms is_sw64 w) in
  let used = ref 0 in
  let tac = itlist (fun t acc ->
      let n = !used in used := n+1;
      ABBREV_TAC (mk_eq(mk_var("zw"^string_of_int n,`:64 word`), t)) THEN acc)
    sws ALL_TAC in
  tac (asl,w);;

(* Fast closer for a merge's operand-equality subgoal (flatten 256-bit Karatsuba *)
(* lanes to 64-bit, abbreviate, WORD_BITWISE — <1s vs ~90s WORD_BLAST).           *)
let FAST_OPERAND_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; SUBSUB_JOIN_DUP; WORD_SUBWORD_SUBWORD;
              JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  WORD_BITWISE_TAC;;

(* Targeted pmul-atom merge for the 2-block bridge (one structurally-determined  *)
(* pair per call; FAST_OPERAND_TAC closes the operand equalities).               *)
let MERGE_ONE_2BLK_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  let goalvars = setify(map (fun t->fst(dest_var t))
    (find_terms (fun t->is_var t && type_of t=`:int128` &&
      (let n=fst(dest_var t) in String.length n>=2 && String.sub n 0 2="qq")) w)) in
  let defs = filter (fun (_,th)->let c=concl th in is_eq c && is_var(rhs c) &&
    is_pmul(lhs c) && mem (fst(dest_var(rhs c))) goalvars) asl in
  let fvnames t = sort (<) (filter (fun n -> not(is_keyvar n))
                              (map (fun v->fst(dest_var v)) (frees t))) in
  let lane_tag op2 =
    if is_comb op2 && is_comb(rator op2) &&
       (try fst(dest_const(rator(rator op2)))="word_subword" with _->false)
    then string_of_term(rand op2) else "X" in
  let info th =
    let p = lhs(concl th) in
    let (_,args) = strip_comb p in
    let op1 = el 0 args and op2 = el 1 args in
    (rhs(concl th), op2, (fvnames op1, fvnames op2, lane_tag op2)) in
  let items = map (fun (_,th)-> info th) defs in
  let rec find_pair = function
    | [] -> None
    | (v,op2,sg)::rest ->
        let cand =
          if is_wordconst op2
          then filter (fun (v2,op2b,_)-> v2<>v && is_wordconst op2b && op2b=op2) rest
          else filter (fun (v2,op2b,sg2)-> v2<>v && not(is_wordconst op2b) && sg2=sg) rest in
        (match cand with (v2,_,_)::_ -> Some(v,v2) | [] -> find_pair rest) in
  (match find_pair items with
  | None -> (fun _ -> failwith "MERGE_ONE_2BLK_TAC: nothing to merge")
  | Some(v1,v2) ->
      let close_op = FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST in
      SUBGOAL_THEN (mk_eq(v1,v2))
        (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
       THENL [EXPAND_TAC(fst(dest_var v1)) THEN EXPAND_TAC(fst(dest_var v2)) THEN
              ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op)
               ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op));
              ALL_TAC]) (asl,w);;

(* Repeat the single-merge to a fixpoint. *)
let MERGE_2BLK_TAC : tactic = REPEAT MERGE_ONE_2BLK_TAC;;

(* Discard helpers for the front (keep block-0/1 keystreams + GHASH tag). *)
let mk_discard2 keepset =
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let s = string_of_term (concl th) in
    String.length s > 500 &&
    (let has sub = let sl=String.length s and bl=String.length sub in
      let rec ck j = if j>sl-bl then false else if String.sub s j bl=sub then true else ck(j+1) in ck 0 in
     List.exists (fun n -> has ("read Q"^string_of_int n^" ")) keepset));;

(* Collapse the all-ones partial-block mask on the block-1 ciphertext: the dec
   less_than_1 path applies `and v9,v9,v0` with an all-ones mask v0, so the GHASH
   multiply (rev64 v8,v9) carries `word_and <mask> cph1` inside Q8/Q17/Q18/Q19.
   For a full block the mask is all-ones (its 64-bit lanes are 0xff..ff, the
   aes-junk base fully overwritten), so `word_and <mask> cph1 = cph1` by WORD_BLAST.
   This tactic finds that masked term inside Q8 and rewrites it to cph1 everywhere,
   so the bridge merge sees the clean `word_reversefields 8 cph1` block.  (Without
   this the block-1 pmul atoms carry the masked form and the merge cannot pair them
   with the spec's brev cph1 atoms.) *)
let MASK_COLLAPSE_CPH1_TAC : tactic = fun (asl,w) ->
  let q8 = tryfind (fun (_,th)-> if (try string_of_term(rand(rator(lhs(concl th))))="Q8" with _->false) then th else fail()) asl in
  let mterm = hd (find_terms (fun t-> try fst(dest_const(rator(rator t)))="word_and" && rand t = `cph1:int128` with _->false) (rhs(concl q8))) in
  let eqn = mk_eq(mterm, `cph1:int128`) in
  (SUBGOAL_THEN eqn (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)
    THENL [CONV_TAC WORD_BLAST; ALL_TAC]) (asl,w);;

(* The flatten-and-blast close for the 2-product reduction structural identity. *)
let FINISH_2BLK_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_SUBWORD_SUBWORD] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN
  REPEAT CONJ_TAC THEN WORD_BITWISE_TAC;;

(* ========================================================================= *)
(* GMULT2 fast-reduce bridge (the ~35s route, replacing the ~73s MERGE/FINISH *)
(* reduce-blast).  GMULT2_FULL_CORRECT_BA is the scalable 2-block fused        *)
(* multiply+reduce: the assembly's byteform that XOR-accumulates TWO Karatsuba *)
(* triples then runs the shared W-reduction equals                            *)
(*   polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1).               *)
(* Built from PMUL_KARATSUBA + GMULT_REDUCE_PROP3 (W-reduction proven ONCE in  *)
(* the dec 1-block file), so the reduction is NEVER re-blasted.  This is OUR-  *)
(* binary analog of Mila's GHASH_NBLOCK_KARATSUBA_EQ_PROP3; the per-block      *)
(* operand transpose (rev64/h <-> brev/byteswap128) is reconciled by MERGE_2BLK *)
(* and the W-reduction *surface* arrangement is closed by the r1/u/r2 hand     *)
(* staging in DEC_2BLK_GMULT2_BRIDGE_TAC (generalized from the dec 1-block      *)
(* s351 W-staging, 3 atoms -> 6).  See _docs/gmult2-fused-reduce-lemma.md and   *)
(* _docs/dec-2block-gmult2-finish-handoff.md.                                  *)
(* ------------------------------------------------------------------------- *)

(* GMULT2_FULL_CORRECT_BA: the 2-block fused multiply+reduce byteform =          *)
(* polyval_reduce_prop3 (word_pmul a0 b0 XOR word_pmul a1 b1).  Built INSTANTLY  *)
(* by the shared fast GMULTn builder (common/gmult_nblock_lemmas.ml); the build *)
(* reproduces the old hand-written dec2_tL + PACK2_ID derivation's concl exactly. *)
let PACK2_ID, GMULT2_FULL_CORRECT_BA = build_GMULTn_fast 2;;

(* XOR-commutativity helper for the wal lane (the two byteforms present the     *)
(* wa-round lane sum in opposite operand order).                               *)
let DEC2_WXSYM = WORD_RULE `word_xor qq6l qq1l = word_xor qq1l qq6l`;;

(* Targeted lane closer: fold ONLY the 64-bit lane-subword equations (rhs a    *)
(* qqNl/qqNh var), NOT the pmul atom defs (which would re-expand qq atoms),     *)
(* then a flat 64-bit WORD_RULE (XOR-ACI over the named lanes).                 *)
let LANE_CLOSE_TAC : tactic = fun (asl,w) ->
  let is_lane_def (_,th) =
    let c = concl th in is_eq c &&
    (try let r = rhs c in is_var r &&
       (let n = fst(dest_var r) in String.length n>=3 && String.sub n 0 2="qq" &&
        (let last = n.[String.length n-1] in last='l' || last='h'))
     with _ -> false) &&
    (try let l = lhs c in is_comb l && fst(dest_const(rator(rator l)))="word_subword" with _ -> false) in
  let lane_ths = map snd (filter is_lane_def asl) in
  (REWRITE_TAC lane_ths THEN CONV_TAC WORD_RULE) (asl,w);;

(* The full GMULT2 bridge close.  Assumes the goal is
     <gq19 s370 byteform> = ghash_polyval_acc (byteswap128 h)(brev xi)
                              [brev cph0; brev cph1]
   with the hk preconditions + the H^2 relation (asm25) in the assumptions.
   Steps: (1) fold the spec RHS to the GMULT2-instantiated byteform (operands
   a0=brev xi^brev cph0, b0=byteswap128 h2, a1=brev cph1, b1=byteswap128 h) via
   GHASH_POLYVAL_ACC_2 + asm25 GSYM + GMULT2_FULL_CORRECT_BA; (2) MERGE_2BLK the
   block products to the 6 atoms {qq0,qq1,qq4,qq5,qq6,qq10}; (3) the r1/u/r2
   W-reduction hand staging (generalized from the dec 1-block, 3 atoms -> 6) then
   a flat per-lane WORD_RULE.  ~30s total (was ~73s MERGE/FINISH). *)
let DEC_2BLK_GMULT2_BRIDGE_TAC : tactic =
  let a0t = `word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`
  and a1t = `word_bytereverse cph1:int128` in
  let gmult2_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [a0t; `byteswap128 h2:int128`; a1t; `byteswap128 h:int128`] GMULT2_FULL_CORRECT_BA) in
  let r1def = `word_xor (word_xor (word_shl (word_zx (wal:64 word):128 word) 63) (word_shl (word_zx wal:128 word) 62)) (word_shl (word_zx wal:128 word) 57)` in
  let udef = `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l))))` in
  (* spec -> prop3(...) -> GMULT2 byteform LHS *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th)=`byteswap128 h2` with _->false)
    then GEN_REWRITE_TAC RAND_CONV
           [REWRITE_RULE[GSYM gmult2_dec]
             (GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th]
               (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
                       `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`]
                 GHASH_POLYVAL_ACC_2))]
    else NO_TAC) THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
  REWRITE_TAC[PMUL_W_64_128] THEN REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  EVERY (map (fun a ->
    let av = mk_var(a,`:int128`) in
    ABBREV_TAC (mk_eq(mk_var(a^"l",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(0,64)`))) THEN
    ABBREV_TAC (mk_eq(mk_var(a^"h",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(64,64)`))))
    ["qq0";"qq1";"qq4";"qq5";"qq6";"qq10"]) THEN
  ABBREV_TAC `wal:64 word = word_xor qq1l qq6l` THEN
  REWRITE_TAC[DEC2_WXSYM] THEN
  FIRST_ASSUM(fun th -> if (try rhs(concl th)=`wal:64 word` && lhs(concl th)=`word_xor qq1l qq6l:64 word` with _->false) then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_TAC (mk_eq(`r1:128 word`, r1def)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (0,64):64 word) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (64,64):64 word) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (0,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (0,64):64 word)) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (64,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (64,64):64 word)) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`u:64 word`, udef)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor qq10l qq4l) (word_xor wal (word_xor qq0l qq5l))) (word_xor (word_xor qq1h qq6h) (word_subword (r1:128 word) (0,64):64 word)) = u`
   (fun th -> REWRITE_TAC[th]) THENL [MAP_EVERY EXPAND_TAC ["u";"wal"] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l)))) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `us57:128 word = word_shl (word_zx (u:64 word):128 word) 57` THEN
  ABBREV_TAC `us62:128 word = word_shl (word_zx (u:64 word):128 word) 62` THEN
  ABBREV_TAC `us63:128 word = word_shl (word_zx (u:64 word):128 word) 63` THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_CLOSE_TAC;;

(* -------------------------------------------------------------------------
   PROGRESS (dec 2-block, mirror of enc 2-block + dec tail dataflow)
   -------------------------------------------------------------------------
   HYBRID: dec binary (dec mc/EXEC, dec step->PC map, dec tail dataflow where
   Q9 = input ciphertext is GHASHed and Q12 = plaintext is stored) + the enc
   2-block STRATEGY (keep Q1/ctr1, cascade to more_than_1 then less_than_1,
   GHASH_POLYVAL_ACC_2 bridge).

   STEP->PC MAP DISCOVERED (dec binary, this proof):
     1--5   prologue 0x18..0x28; s5 pc+0x2c, X9=32, X1=256.
     6--30  CTR setup (per-step fold, keep Q0,Q1,Q30); s30 pc+0x90.
     31--84 AES bulk; s84 pc+360.  85--173; s173 pc+716, X5=word 0.
     174--177 GHASH tag load+rev64 + GCM_SIMD_SIMPLIFY -> Q19 stable
              reversefields(xi) form.  178--184; 185--254; s254 pc+1040.
     [255] cmp x0,x5/b.ge -> tail (INT_SUB_REFL).  256--265; s265 pc+3788.
       set X5=word 32 (WORD_RULE).  Q9 s265 = cph0; Q16 = partial tag.
     266--272 tail+eor3 v12,v9,v0,v29 -> s272 pc+3816 Q12 = block-0 plaintext.
       Abbrev Q12 -> pt0 = word_xor cph0 (aes256_encrypt ctr0 keys) (spec form).
     273--312 cascade movs (DISCARD_OLDSTATE at s312 to flatten pile!).
       *** Use ARM_VSTEPS_FOLD then DISCARD_OLDSTATE; do NOT keep all states
       (the mov v_k cascade copies Q1's 2666-char keystream into Q2..Q7 across
       40 states = pile blow-up).
     [313] RESOLVE_BRANCH (x5=32>16, b.gt) -> s313 pc+4340 = 0x10f4 = more_than_1.
       Q7 = block-1 keystream; Q9 = cph0; Q12 = pt0; Q17/18/19 = 0.

   NEXT (more_than_1 0x10f4..0x1134, dec block-0 GHASH vs H^2):
     - st1 v12,[x2],#16 stores pt0 to out_p, advances X2 to out_p+16.
       *** capture out_p block-0 readback = pt0 BEFORE discard.
     - rev64 v8,v9 (v9=cph0 ATOM, so no tower blow-up unlike enc's ct0);
       eor v8,v8,v16 (feed tag); pmull2/pmull/mid vs Q22=h2 + Q21=hk hi lane;
       accumulate Q17/Q19/Q18.  ldr q9,[x0]=cph1; eor3 v12,v9,v7 = block-1 PT.
       *** abbrev block-1 Q12 -> pt1 = word_xor cph1 (aes256_encrypt ctr1 keys);
       ctr1 keystream input = gcm_ctr_inc ctr0 (GCM_CTR_INC_LANES on Q7/Q1).
     - less_than_1 0x1450..: X1=128 -> mask all-ones, Q9=cph1; block-1 GHASH vs
       Q20=h; accumulate; single Prop3 reduction folds BOTH blocks.  store pt1.
     - BRIDGE at dec s351-analog (NOT s350): the dec MODULO splits enc's 3 eor3
       into 6 eors, so the final eor lands one step later.  Find the analog of
       enc s367 (clean polyval) empirically; assert read Q19 =
         ghash_polyval_acc (byteswap128 h)(brev xi)[brev cph0; brev cph1]
       via DEC_2BLK_GMULT2_BRIDGE_TAC (GMULT2 fast route, ~30s; the old
         GHASH_POLYVAL_ACC_2 + MERGE_2BLK + FINISH_2BLK reduce-blast was ~73s).
     - ext+rev64 -> word_bytereverse gval; store xi_p; exit pc+0x11e4.

   UPDATE: bridge state is s370 (pc+4568), the analog of dec 1-block s351 (after
   the final `eor v19,v19,v18`, before `ext v19`).  out_p block-0 store readback
   = pt0 (captured at s320), block-1 = pt1 (captured at s363).  pt0/pt1 abbreviated
   to the spec forms word_xor cph_i (aes256_encrypt ctr_i keys).
   ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* The 2-block decrypt theorem.  Direct C_ARGUMENTS entry at pc+0x18.          *)
(* ===========================================================================
   The whole-2-block theorems AESV8_GCM_8X_DEC_256_2BLOCK and
   AESV8_GCM_8X_DEC_256_2BLOCK_BYTELIST have been REMOVED: the whole-2-block
   (32-byte) case is the bl1=16 endpoint of AESV8_GCM_8X_DEC_256_LE2BLOCK
   (band [17,32], all-ones mask = full block), so the dedicated theorems were
   redundant.  They were referenced nowhere outside this file.  This file is
   retained only for its SHARED bridge infrastructure (JOIN_EQ_SPLIT, RF8_SUBWORD,
   the SUBW_* lane lemmas, MERGE_ONE_2BLK_TAC / MERGE_2BLK_TAC, mk_discard2,
   MASK_COLLAPSE_CPH1_TAC, FINISH_2BLK_TAC, GMULT2_FULL_CORRECT_BA,
   DEC_2BLK_GMULT2_BRIDGE_TAC, LANE_CLOSE_TAC), which le2block/le3block/le4block use.
   =========================================================================== *)
