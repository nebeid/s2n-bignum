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
       via GHASH_POLYVAL_ACC_2 + PMUL_KARATSUBA + MERGE_2BLK_TAC + FINISH_2BLK_TAC.
     - ext+rev64 -> word_bytereverse gval; store xi_p; exit pc+0x11e4.

   UPDATE: bridge state is s370 (pc+4568), the analog of dec 1-block s351 (after
   the final `eor v19,v19,v18`, before `ext v19`).  out_p block-0 store readback
   = pt0 (captured at s320), block-1 = pt1 (captured at s363).  pt0/pt1 abbreviated
   to the spec forms word_xor cph_i (aes256_encrypt ctr_i keys).
   ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* The 2-block decrypt theorem.  Direct C_ARGUMENTS entry at pc+0x18.          *)
(* ========================================================================= *)

let AESV8_GCM_8X_DEC_256_2BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4612) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4612) (out_p:int64, 32) /\
    nonoverlapping (word pc, 4612) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4612) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (xi_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 32) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 240) /\
    nonoverlapping (out_p, 32) (htbl_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 0x11e4) /\
          read (memory :> bytes128 out_p) s =
          EL 0 (aes_ctr ctr0 [cph0;cph1]
                 [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          EL 1 (aes_ctr ctr0 [cph0;cph1]
                 [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[AES_CTR_2_EL; AES_CTR_2_MAP_BREV] THEN
  ABBREV_TAC `ctr1:int128 = gcm_ctr_inc ctr0` THEN
  FIRST_X_ASSUM(fun th ->
    if (try rhs(concl th) = `ctr1:int128` with _ -> false)
    then ASSUME_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  (* prologue 0x18..0x28 (5 instrs): X9=32, X16, X11, Prop3 const at [sp+64] *)
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (1--5) THEN
  (* CTR setup (6..30): per-step fold, keep Q0,Q1,Q30. *)
  EVERY (map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (i--i) THEN
              GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [2;3;4;5;6;7]) (6--30)) THEN
  (* AES bulk: keep Q0,Q1 (block-0/1 keystreams), drop Q2-Q7,Q30. *)
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (31--84) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (85--173) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  (* GHASH tag load + rev64 + fold (stable reversefields xi form in Q19). *)
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (174--177) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (178--184) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (185--254) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  GCM_SIMD_SIMPLIFY_TAC THEN
  (* cmp x0,x5 / b.ge tail: in_p - in_p = 0 -> branch to tail. *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [255] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (256--265) THEN mk_discard2 [2;3;4;5;6;30] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word 32)) in_p = word 32:int64`]) THEN
  (* tail eor3 v12,v9,v0,v29 forms block-0 plaintext in Q12 -> abbrev pt0 (spec). *)
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC (266--272) THEN mk_discard2 [2;3;4;5;6;30] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor cph0 (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC
    `pt0:int128 = word_xor cph0 (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  (* cascade movs: VSTEPS_FOLD then DISCARD_OLDSTATE to flatten (mov v_k routes
     Q1 keystream into Q2..Q7 across ~40 states). *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (273--312) THEN
  DISCARD_OLDSTATE_TAC "s312" THEN
  (* x5=32>16 b.gt -> more_than_1 (pc+0x10f4). *)
  RESOLVE_BRANCH_TAC THEN ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [313] THEN
  (* more_than_1: st1 v12,[x2],#16 stores pt0; capture readback then continue. *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (314--320) THEN
  SUBGOAL_THEN `read (memory :> bytes128 out_p) (s320:armstate) = pt0`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s320" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (321--328) THEN
  (* ldr q9,[x0]=cph1; eor3 v12,v9,v7 forms block-1 plaintext -> abbrev pt1.
     ct1 keystream input = aes over gcm_ctr_inc ctr0 (GCM_CTR_INC_LANES). *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor cph1 (aes256_encrypt (ctr1:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try lhs(concl th) = `ctr1:int128` with _ -> false)
      then GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th] else NO_TAC) THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ABBREV_TAC
    `pt1:int128 = word_xor cph1 (aes256_encrypt (ctr1:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  (* into less_than_1 (pc+0x144c); flatten then drop dead Q1-Q7. *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (329--335) THEN
  DISCARD_OLDSTATE_TAC "s335" THEN mk_discard2 [1;2;3;4;5;6;7] THEN
  (* less_than_1 mask setup + store; X1=0 -> mask all-ones. *)
  ARM_VSTEPS_RESOLVE_SIMD_TAC AESV8_GCM_8X_DEC_256_EXEC (336--350) THEN
  (* re-assert Q9 = cph1 (all-ones AND) and Q12 = pt1 (all-ones bif). *)
  FIRST_X_ASSUM(MP_TAC o SPEC `cph1:int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL [CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pt1:int128`
    o MATCH_MP (MESON[] `read Q12 s = a ==> !a'. a = a' ==> read Q12 s = a'`)) THEN
  ANTS_TAC THENL [EXPAND_TAC "pt1" THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  (* block-1 GHASH multiply vs Q20=h, accumulate into block-0's Q17/18/19,
     store pt1 to out_p+16, single MODULO reduction folding both blocks. *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (351--363) THEN
  DISCARD_OLDSTATE_TAC "s363" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (364--369) THEN
  DISCARD_OLDSTATE_TAC "s369" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC [370] THEN
  DISCARD_OLDSTATE_TAC "s370" THEN
  (* collapse the all-ones block-1 mask so the GHASH block is the clean brev cph1 *)
  MASK_COLLAPSE_CPH1_TAC THEN
  (* === GHASH bridge at s370 (pc+4568), the dec s351-analog (after the final
     `eor v19,v19,v18`, before `ext v19`).  GHASH_POLYVAL_ACC_2 + the 2-product
     Karatsuba/Prop3 merge, exactly as enc 2-block. === *)
  SUBGOAL_THEN
    `read Q19 (s370:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s370`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s370` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
   FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `byteswap128 h2` with _ -> false)
     then GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th] else NO_TAC) THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [polyval_reduce_prop3] THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV)
     [REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
   REWRITE_TAC[byteswap128] THEN
   REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] KARATSUBA_LIMBS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   REWRITE_TAC[WORD_XOR_0; SUBWORD0_LEMMAS] THEN REWRITE_TAC[WORD_XOR_0] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   FINISH_2BLK_TAC;
   ALL_TAC] THEN
  (* === ext+rev64 (371-372): Q19 -> word_bytereverse gval; store xi_p (373). === *)
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_EXEC (371--372) THEN
  SUBGOAL_THEN `read Q19 (s372:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s372`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s372` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_EXEC [373] THEN
  (* === close ===  out_p block-0 = pt0, block-1 = pt1 (both via store readbacks);
     xi_p = word_bytereverse gval; fold ctr1 = gcm_ctr_inc ctr0 so block-1 matches. *)
  ENSURES_FINAL_STATE_TAC THEN
  FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `ctr1:int128` with _ -> false)
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC));;
