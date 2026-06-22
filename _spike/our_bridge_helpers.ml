(* ===== OUR GHASH-bridge helpers, materialized standalone for the spike ===== *)
(* NOTE: rebinds KARATSUBA_LIMBS to our LET-form; her bridge thm already closed. *)

let WORD_INSERT_SUBWORD = prove(
  `(!x:int128 y:64 word. word_subword (word_insert x (0,64) y : int128) (64,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128 y:64 word. word_subword (word_insert x (64,64) y : int128) (0,64) : 64 word = word_subword x (0,64)) /\
   (!x:int128 y:64 word. word_subword (word_insert x (0,64) y : int128) (0,64) : 64 word = y) /\
   (!x:int128 y:64 word. word_subword (word_insert x (64,64) y : int128) (64,64) : 64 word = y)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let WORD_SUBWORD_SUBWORD = prove(
  `(!x:int128. word_subword (word_subword x (0,128) : int128) (0,64) : 64 word = word_subword x (0,64)) /\
   (!x:int128. word_subword (word_subword x (0,128) : int128) (64,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128. word_subword (word_subword x (64,128) : int128) (0,64) : 64 word = word_subword x (64,64)) /\
   (!x:int128. word_subword (word_subword x (0,64) : 64 word) (0,64) : 64 word = word_subword x (0,64))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* GHASH bridge lemmas (recovered from the standalone gcm_gmult proof).       *)
(* These prove the Karatsuba + Prop3 reduction the assembly computes equals   *)
(* the spec-level polyval_dot / ghash_polyval_acc, so the symbolic Q19 result *)
(* at the xi_p store can be bridged to the postcondition.  All are BITBLAST / *)
(* WORD_RULE proofs (no CHEAT, no axioms).                                    *)
(* ------------------------------------------------------------------------- *)

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

let JOIN_SUBWORD_RULES = prove(
  `(!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
   (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN BITBLAST_TAC);;

let PMUL_CONG_128 = prove(
  `!a b c d:64 word. a = c /\ b = d ==> (word_pmul a b:int128) = word_pmul c d`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let SUBWORD_XOR_JOIN_DIST = prove(
  `(!x y:int128. word_subword (word_xor x y) (0,64) : 64 word =
      word_xor (word_subword x (0,64)) (word_subword y (0,64))) /\
   (!x y:int128. word_subword (word_xor x y) (64,64) : 64 word =
      word_xor (word_subword x (64,64)) (word_subword y (64,64))) /\
   (!a b:64 word. word_subword (word_join a b : int128) (0,64) : 64 word = b) /\
   (!a b:64 word. word_subword (word_join a b : int128) (64,64) : 64 word = a)`,
  REPEAT CONJ_TAC THEN TRY(REPEAT GEN_TAC) THEN BITBLAST_TAC);;

let SUBWORD0_LEMMAS = prove(
  `(word_subword (word 0:int128) (0,64):64 word = word 0) /\
   (word_subword (word 0:int128) (64,64):64 word = word 0)`,
  CONJ_TAC THEN BITBLAST_TAC);;

(* Half projection helpers for the manual W-reduction lane-fold (ported from the dec proof). *)
let JOINMID = prove(
  `!q:int128. word_subword (word_join q q :(256)word) (64,128):int128 =
     word_join (word_subword q (0,64):64 word) (word_subword q (64,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let QQ0SPLIT = prove(
  `!q:int128. q = word_join (word_subword q (64,64):64 word) (word_subword q (0,64):64 word)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Abbreviate every currently-innermost fully-applied word_pmul to a fresh qqN:int128. *)
let ABBREV_INNER_PMULS_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t = try let (h,args)=strip_comb t in
        fst(dest_const h)="word_pmul" && length args=2 with _ -> false in
  let pmuls = setify(find_terms is_pmul_app w) in
  let contains_pmul_strict t = exists (fun p -> p <> t &&
     (let rec occ u = u=p ||
        (match u with Comb(a,b)->occ a||occ b|Abs(_,b)->occ b|_->false) in occ t)) pmuls in
  let inner = filter (fun t -> not(contains_pmul_strict t)) pmuls in
  let allvars = itlist (fun (_,th) acc ->
        union (map (fun v -> fst(dest_var v)) (frees(concl th))) acc)
        asl (map (fun v -> fst(dest_var v)) (frees w)) in
  let used = ref allvars in
  let fresh () = let rec go i = let n = "qq"^string_of_int i in
                   if mem n !used then go (i+1) else (used := n :: !used; n) in go 0 in
  EVERY (map (fun t -> ABBREV_TAC (mk_eq(mk_var(fresh(), `:int128`), t))) inner) (asl,w);;

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

(* Collapse a 64-bit lane of subword(subword(join a a)(64,128)) -- the duplicated *)
(* mid-half the wv W-reduction operand produces -- to a plain lane of a.  Lets the *)
(* wv operand equality close as a flat WORD_BITWISE identity instead of a ~90s     *)
(* WORD_BLAST (see FAST_OPERAND_TAC / the merge speedup note below).               *)
let SUBSUB_JOIN_DUP = prove(
  `(!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (0,64) :64 word
                 = word_subword a (64,64)) /\
   (!a:128 word. word_subword (word_subword (word_join a a :256 word) (64,128) :128 word) (64,64) :64 word
                 = word_subword a (0,64))`,
  CONJ_TAC THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Abbreviate EVERY `word_subword (a:int128) (lo,64)` subterm occurring in the goal
   (a any term, typically a qqN atom or its lane) to a fresh 64-bit var.  After this
   no `word_subword`-over-int128 survives, so the residual is a flat word_xor
   identity over 64-bit vars that WORD_BITWISE_TAC closes.  (Used by both
   FAST_OPERAND_TAC for the merge and FINISH_2BLK_TAC for the final close.) *)
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

(* Fast closer for a merge's operand-equality subgoal.  Both operands are the SAME *)
(* GF product's structural lane form (word_zx/word_shl/word_subword over the qq    *)
(* atoms, NO pmul), so collapse the 256-bit Karatsuba lanes to 64-bit (the SUBW_*  *)
(* lemmas + SUBSUB_JOIN_DUP), abbreviate the residual atom-lanes, and close by      *)
(* WORD_BITWISE_TAC (<1s).  This replaces a ~90s WORD_BLAST per W-reduction operand. *)
let FAST_OPERAND_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; SUBSUB_JOIN_DUP; WORD_SUBWORD_SUBWORD;
              JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  WORD_BITWISE_TAC;;

(* Targeted pmul-atom merge for the 2-block bridge.  The post-Karatsuba goal   *)
(* has matched LHS/RHS word_pmul atoms (same GF(2^128) product in different    *)
(* arg-order / lane nesting).  The generic all-pairs MERGE_PMUL_ATOMS_TAC is   *)
(* O(pairs) WORD_BLASTs and too slow here (~30 min) because each FAILED         *)
(* PMUL_CONG WORD_BLAST on the big W-reduction operands costs ~90s.  Instead we *)
(* pick exactly ONE structurally-determined pair per call and blast only it.    *)
(*                                                                              *)
(* Two atom classes, each paired without trial-blasting non-matches:            *)
(*  (a) PRODUCT atoms (operand 2 = a key lane: word_subword h/h2, or an XOR of  *)
(*      two such): the LHS (assembly) and RHS (spec) forms of the same GF       *)
(*      product agree on the set of non-key free vars of operand 1, on the set  *)
(*      of free vars of operand 2, and on operand 2's subword lane index.       *)
(*      Key vars k0..k14 are excluded from operand 1's signature because the    *)
(*      assembly's `ins` leaves a spurious k13 in one mid-term form.            *)
(*  (b) W-REDUCTION atoms (operand 2 = the same word-CONSTANT 0xc200...): the   *)
(*      two forms (wa round, then wv round) differ structurally in operand 1    *)
(*      but multiply the same constant, so they are paired by `operand 2 is the *)
(*      identical word-constant`.                                               *)
(* On success the merge equality is propagated into the hypotheses (RULE_ASSUM) *)
(* so later atom DEFINITIONS that reference the merged-away atom are updated to  *)
(* the canonical one -- essential for the 2-round W-reduction pmuls (the wv      *)
(* atom's def references the wa atom we merged the round before).  Fails         *)
(* (failwith) if no structurally-matched pair remains.                          *)
let MERGE_ONE_2BLK_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  (* only consider atoms actually occurring in the goal conclusion *)
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
      (* Close each operand equality with FAST_OPERAND_TAC (flatten lanes +
         WORD_BITWISE, <1s) and only fall back to WORD_BLAST if that doesn't apply.
         The W-reduction (wv) operand is ~90s under WORD_BLAST but ~1s under the
         flatten route -- this is the bridge's dominant cost, see FAST_OPERAND_TAC. *)
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

(* Tactic: abbreviate the current read Q9 (a ciphertext tower) to the given atom var. *)
let ABBREV_Q9_TAC vname state =
  fun (asl,w) ->
    let pat = "read Q9 "^state^" =" in
    let th = find (fun (_,t)->let s=string_of_term(concl t) in
      String.length s >= String.length pat && String.sub s 0 (String.length pat) = pat) asl in
    ABBREV_TAC (mk_eq(mk_var(vname,`:int128`), rhs(concl(snd th)))) (asl,w);;

(* The flatten-and-blast close for the 2-product reduction structural identity:
   collapse the 256-bit Karatsuba assembly to 64-bit lanes, abbreviate atom halves,
   split the word_join equality lane-wise, finish each lane with WORD_BITWISE_TAC.
   (ABBREV_ALL_SUBWORDS_TAC is defined above, shared with FAST_OPERAND_TAC.) *)
let FINISH_2BLK_TAC : tactic =
  REWRITE_TAC[SUBW_XOR_256; SUBW_ZX_256; SUBW_SHL64_256; SUBW_SHL128_256;
              SUBW_ZX128_256; SUBW_SHL64_128_256; SUBW_SHL128_128_256] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_SUBWORD_SUBWORD] THEN
  (* expose all lanes via QQ0SPLIT + JOINMID, THEN abbreviate every residual
     word_subword-over-int128 so the goal is flat 64-bit before WORD_BITWISE *)
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  ABBREV_ALL_SUBWORDS_TAC THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN
  REPEAT CONJ_TAC THEN WORD_BITWISE_TAC;;
