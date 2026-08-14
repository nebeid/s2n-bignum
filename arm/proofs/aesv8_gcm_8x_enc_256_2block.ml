(* ========================================================================= *)
(* AES-256-GCM encrypt, the genuine 2-block path of aesv8_gcm_8x_enc_256.     *)
(*                                                                            *)
(* Mirror/extension of the 1-block proof arm/proofs/aesv8_gcm_8x_enc_256_1block *)
(* (theorem AESV8_GCM_8X_ENC_256_1BLOCK).                                       *)
(*                                                                            *)
(* No CHEAT_TAC, no new axioms.                                               *)
(*                                                                            *)
(* FULL postcondition: out_p block-0 = ct0,                                    *)
(* out_p block-1 = word_xor plaintext1 (aes256_encrypt ctr1 keys), and          *)
(* xi_p = word_bytereverse (ghash_polyval_acc (byteswap128 h)(brev xi)          *)
(* [brev ct0; brev ct1]).  The block-1 AES counter ctr1 is exposed as a spec    *)
(* var pinned by the precond ctr1 = gcm_ctr_inc ctr0 (the rev32+ADD+rev32 of    *)
(* the top 32-bit lane); GCM_CTR_INC_LANES bridges it to the lane-byte form.    *)
(* The 2-product GHASH bridge closes via the targeted MERGE_2BLK_TAC (products  *)
(* paired by free-var/lane signature, W-reduction pmuls by shared word-const,    *)
(* operand equalities closed by FAST_OPERAND_TAC: flatten lanes + WORD_BITWISE,  *)
(* much cheaper than WORD_BLAST) + FINISH_2BLK_TAC.  Direct C_ARGUMENTS entry at  *)
(* pc+0x18 (no ENSURES_TRANS wrapper), exit pc+0x11d8.                           *)
(* ========================================================================= *)

(* -------------------------------------------------------------------------
   BINARY STRUCTURE AND PROOF NOTES (2-block, bit_len = 256)

   Control flow: the front computes the CTR blocks and AES towers, then the
   length cascade at .L256_enc_tail routes x5 = 32 to more_than_1 (block-0
   GHASH) and then less_than_1 (block-1 GHASH + the single Prop3 reduction).
   A `mov` cascade in the tail SHIFTS the keystream registers so the block the
   body consumes lands in the slot it expects: `mov v7,v1` routes block-1's
   keystream to Q7, which less_than_1 reads for block-1's ciphertext.  Any
   assumption-discard filter used across the cascade MUST keep Q7 alive.

   At less_than_1 entry X1 = word 128, NOT 256: the cascade decremented bit_len
   by the one block more_than_1 already processed.  So less_than_1 sees a FULL
   last block, its mask v0 is ALL-ONES, and `and v9,v9,v0` is the identity on
   ct1.  That AND re-expands ct1's AES tower, so the ct1 abbreviation must be
   re-asserted afterwards (all-ones mask, then WORD_BLAST), exactly as the
   full-block 1-block proof does.

   Two term-explosion hazards, both handled by folding rather than brute force:
     - the 4-lane 32-bit counter increment `add v30.4s,v30.4s,v31.4s` over the
       symbolic rev32 tree blows Q30 up by orders of magnitude;
       GCM_SIMD_SIMPLIFY_TAC collapses it back to a clean word_join byte-shuffle
       of ctr0 with `word_add (...) (word 1)`.  Fold after EACH step of the CTR
       setup so the derived block counters stay bounded, and do NOT discard Q30
       mid-setup (the 1-block proof can, since it needs only block 0 = ctr0).
     - both ciphertexts MUST be abbreviated to atoms BEFORE the rev64 + pmull
       that feeds GHASH, or the multiply blows up the product registers.

   GHASH bridge: block 0 multiplies against H^2 (= polyval_dot K K, read from
   htbl+32) and block 1 against H (= K, from htbl+0), accumulating into shared
   registers so ONE Prop3 reduction at the end folds both blocks.  The pre-store
   Q19 is bridged to
     ghash_polyval_acc (byteswap128 h) (brev xi) [brev ct0; brev ct1]
   via GHASH_POLYVAL_ACC_2 and the 1-block Karatsuba/Prop3 machinery over TWO
   products.  Packed-mid lanes: subword hk (0,64) = mid(h) is the block-1 / H
   lane, subword hk (64,64) = mid(h2) the block-0 / H^2 lane.
   ------------------------------------------------------------------------- *)

needs "arm/proofs/base.ml";;
needs "common/aes.ml";;
needs "arm/proofs/utils/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
needs "common/karatsuba_pmul.ml";;
needs "common/polyval_ghash.ml";;
(* Counter-mode spec layer: gcm_ctr_inc + GCM_CTR_INC_LANES (+ inc32 bridge and *)
(* the gcm_ctr_inc_iter iterator) now live in the shared utils file.            *)
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;
(* Recursive list-based CTR ciphertext spec (aes_ctr) + its 2-block reductions  *)
(* AES_CTR_2_EL / AES_CTR_2_MAP_BREV, used to state the out_p / GHASH postcond.  *)
needs "arm/proofs/utils/aes_ctr_spec.ml";;

(* The machine code + EXEC rule are shared with the 1-block proof; load that
   file so aesv8_gcm_8x_enc_256_mc / _EXEC and all helper lemmas are in scope.
   (We only ADD the 2-block theorem; we never edit the 1-block file.) *)
needs "arm/proofs/aesv8_gcm_8x_enc_256_1block.ml";;

(* -------------------------------------------------------------------------
   ENTRY CONVENTION.  bit_len = 256 (two whole blocks), so X9 = 32 and the
   length cascade takes more_than_1 then less_than_1.  Entry is DIRECT at
   pc+0x18 with the seven C arguments still in registers (X0=in_p, X1=word 256,
   X2=out_p, X3=xi_p, X4=ivec_p, X5=key_p, X6=htbl_p) and Q30=ctr0, so the
   precondition is stated with C_ARGUMENTS and needs no ENSURES_TRANS wrapper.
   The prologue at 0x18-0x28 (lsr x9; mov x16; mov x11; mov x5,#0xc2..;
   stp x5,xzr,[sp,64]) steps inline and establishes X9/X16/X11 and the Prop3
   constant at [sp+64] -- the constant needs NO precondition because the
   prologue writes it; the (sp,80) stack disjointness in the precondition
   covers that store.

   Plaintext: two blocks at in_p, in_p+16.  Block 0's AES input is ctr0;
   block 1's is ctr1, exposed as a spec variable pinned by
   ctr1 = gcm_ctr_inc ctr0.

   htable preconditions: h = read htbl_p (= byteswap128 H), hk = the packed
   mids at +16, h2 = read (htbl_p+32) (= byteswap128 H^2, used by more_than_1).
   The bridge needs the mid lanes split as
     subword hk (0,64)  = mid(h)   [block-1 / H,    less_than_1 pmull low lane]
     subword hk (64,64) = mid(h2)  [block-0 / H^2, more_than_1 pmull2 hi lane]
   ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* The AES-GCM counter increment (block-1's CTR input) + its lane-byte form    *)
(* now live in the shared utils file arm/proofs/utils/gcm_ctr_helpers.ml       *)
(* (needs'd above): gcm_ctr_inc, GCM_CTR_INC_LANES (used by the ctr1 fold), the *)
(* NIST inc32 bridge GCM_CTR_INC_INC32, and the gcm_ctr_inc_iter iterator.      *)
(* They were lifted byte-identically out of this file; nothing else changes.   *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Helper lemmas for the 2-product GHASH bridge.                             *)
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

(* ========================================================================= *)
(* The 2-block theorem.  Direct C_ARGUMENTS entry at pc+0x18 (NO wrapper):    *)
(* the 5 prologue setup instructions (0x18..0x28) are stepped inline.          *)
(* bit_len = 256, two whole blocks; exit pc+0x11d8 (epilogue not simulated).   *)
(* ========================================================================= *)

(* The spec variable ctr1 is the block-1 AES counter: the lane-level
   once-incremented ctr0 (rev32 of the byte-shuffled top 32-bit lane + 1), as
   produced by the front's CTR setup; pinned by the precond below. *)

let AESV8_GCM_8X_ENC_256_2BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    plaintext0 plaintext1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4600) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4600) (out_p:int64, 32) /\
    nonoverlapping (word pc, 4600) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (ivec_p:int64, 16) /\
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
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = plaintext0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = plaintext1 /\
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
     (\s. read PC s = word (pc + 0x11d8) /\
          read (memory :> bytes128 out_p) s =
          EL 0 (aes_ctr ctr0 [plaintext0;plaintext1]
                 [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          EL 1 (aes_ctr ctr0 [plaintext0;plaintext1]
                 [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              (MAP word_bytereverse
                (aes_ctr ctr0 [plaintext0;plaintext1]
                  [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* The out_p / GHASH postcond is stated via the shared list spec aes_ctr:
       out_p block i = EL i (aes_ctr ctr0 [pt0;pt1] keys)
       GHASH input    = MAP word_bytereverse (aes_ctr ctr0 [pt0;pt1] keys).
     Reduce those to the concrete per-block ciphertext forms (block 0 uses
     ctr0, block 1 uses gcm_ctr_inc ctr0) via the proven reductions, then
     re-introduce the spec atom ctr1 = gcm_ctr_inc ctr0 by abbreviation (flipped
     to lhs = ctr1) so the rest of the proof body runs verbatim as before. *)
  REWRITE_TAC[AES_CTR_2_EL; AES_CTR_2_MAP_BREV] THEN
  ABBREV_TAC `ctr1:int128 = gcm_ctr_inc ctr0` THEN
  FIRST_X_ASSUM(fun th ->
    if (try rhs(concl th) = `ctr1:int128` with _ -> false)
    then ASSUME_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  (* prologue 0x18..0x28 (5 instrs): X9=32, X16, X11, Prop3 const at [sp+64] *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (1--5) THEN
  (* CTR setup (6..30): step 1-at-a-time, fold each, keep Q0,Q1,Q30 (DKctr). *)
  EVERY (map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (i--i) THEN
              GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [2;3;4;5;6;7]) (6--30)) THEN
  (* AES bulk: keep Q0,Q1 (block-0/1 keystreams), drop Q2-Q7,Q30. *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (31--89) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (90--178) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  (* GHASH tag load + fold (keeps Q19 the byteswapped xi tag). *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (179--189) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  mk_discard2 [2;3;4;5;6;7;30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (190--259) THEN mk_discard2 [2;3;4;5;6;7;30] THEN
  (* cmp x0,x5 / b.ge tail: in_p - in_p = 0 -> branch to .tail (pc+3768). *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [260] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  (* tail entry: sub x5,x4,x0; set X5 = word 32; cascade auto-resolves; keep Q7. *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (261--265) THEN mk_discard2 [2;3;4;5;6;30] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word 32)) in_p = word 32:int64`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (266--315) THEN mk_discard2 [2;3;4;5;6;30] THEN
  (* abbreviate ct0 (block-0 ciphertext) to the SPEC FORM word_xor plaintext0
     (aes256_encrypt ctr0 keys) BEFORE the rev64+pmull, so the out_p postcond
     closes by ASM_REWRITE (1-block s265 MESON-SPEC idiom). *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor plaintext0 (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]; DISCH_TAC] THEN
  ABBREV_TAC
    `ct0:int128 = word_xor plaintext0 (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (316--325) THEN
  (* abbreviate ct1 (block-1 ciphertext) to its SPEC FORM word_xor plaintext1
     (aes256_encrypt ctr1 keys) -- same MESON-SPEC idiom as ct0.  The ANTS
     rewrites the spec var ctr1 to gcm_ctr_inc ctr0 (its precond) and then to
     the explicit lane-byte form (GCM_CTR_INC_LANES) the Q9 readback carries,
     then expands aes256_encrypt to the raw aese/aesmc tower. *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `word_xor plaintext1 (aes256_encrypt (ctr1:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if (try lhs(concl th) = `ctr1:int128` with _ -> false)
      then GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th] else NO_TAC) THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
    ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
    REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
    REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]; DISCH_TAC] THEN
  ABBREV_TAC
    `ct1:int128 = word_xor plaintext1 (aes256_encrypt (ctr1:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (326--333) THEN
  DISCARD_OLDSTATE_TAC "s333" THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (334--345) THEN
  (* less_than_1 sees X1=128 -> mask all-ones; re-assert Q9 = ct1. *)
  FIRST_X_ASSUM(MP_TAC o SPEC `ct1:int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL [EXPAND_TAC "ct1" THEN CONV_TAC WORD_BLAST; DISCH_TAC] THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (346--353) THEN
  (* capture the block-1 ciphertext store (st1 v9,[x2] @ 0x1188, x2=out_p+16)
     BEFORE discarding the store state; mask v0 is all-ones (x1=128) so the
     stored masked/bif value is exactly ct1.  Carry it to the final state. *)
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s353:armstate) = ct1`
    ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DISCARD_OLDSTATE_TAC "s353" THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (354--367) THEN
  DISCARD_OLDSTATE_TAC "s367" THEN
  (* === GHASH bridge: read Q19 s367 = ghash_polyval_acc (byteswap128 h)(brev xi)[brev ct0;brev ct1] *)
  SUBGOAL_THEN
    `read Q19 (s367:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse ct0; word_bytereverse ct1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s367`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s367` with _ -> false)
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
  (* === ext+rev64 (368-369): Q19 -> word_bytereverse gval; store (370). === *)
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse ct0; word_bytereverse ct1]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_ENC_256_EXEC (368--369) THEN
  SUBGOAL_THEN `read Q19 (s369:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s369`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s369` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC [370] THEN
  (* === close ===
     The postcondition has four conjuncts: out_p block-0 ciphertext, out_p
     block-1 ciphertext, xi_p GHASH tag, and the MAYCHANGE frame.  After
     ENSURES_FINAL_STATE_TAC + ASM_REWRITE_TAC the block-1 (= ct1 via its store
     readback) and xi_p (= word_bytereverse gval, with gval = the spec GHASH over
     brev ct0/ct1, and ct0/ct1 now in spec form) goals close by ASM; only the
     block-0 goal needs the ct0 spec-form expansion (its store predates the ct0
     abbreviation, so the readback is the RAW aese/aesmc tower) and the MAYCHANGE
     frame needs MONOTONE_MAYCHANGE_TAC. *)
  ENSURES_FINAL_STATE_TAC THEN
  (* Fold `ctr1 = gcm_ctr_inc ctr0` UNIFORMLY into the goal AND the ct0/ct1
     spec-form def hypotheses, so ctr1 is eliminated consistently everywhere.
     (Discarding the precond is wrong -- the postcond's block-1 clause carries
     gcm_ctr_inc ctr0 in the final state, so the ct1-def must too for them to
     match; just unfolding the goal but not the def hypotheses leaves a residual.) *)
  FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `ctr1:int128` with _ -> false)
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC) THEN
  (* block-1 (= ct1 via its store readback) and xi_p (= word_bytereverse gval,
     gval = the spec GHASH over brev ct0/ct1) now match ct1's spec-form def under
     ASM_REWRITE (both sides in terms of gcm_ctr_inc ctr0). *)
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  (* the only remaining goal is out_p block-0: <raw aese/aesmc tower> = ct0
     (the block-0 store predates the ct0 abbreviation).  Rewrite ct0 to its
     spec form (GSYM the ct0 def) and expand aes256_encrypt to the same tower. *)
  TRY(FIRST_X_ASSUM(fun th ->
        if (try rhs(concl th) = `ct0:int128` with _ -> false)
        then GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [SYM th] else NO_TAC) THEN
      ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC]));;

(* ========================================================================= *)
(* List-based ciphertext postcondition (the XTS-style single-buffer form):     *)
(* the out_p output is one byte_list_at clause over the recursive CTR spec     *)
(* aes_ctr_bytes, instead of two per-block bytes128 reads.  Derived from the    *)
(* main theorem by postcondition-weakening (ENSURES_POSTCONDITION_THM): the     *)
(* two EL-form reads imply byte_list_at via the shared readback bridge          *)
(* BYTE_LIST_AT_2BLOCKS_CTR (whole-block, mask all-ones at bit_len = 256).  No  *)
(* re-simulation -- this is a cheap corollary of AESV8_GCM_8X_ENC_256_2BLOCK.   *)
(* This is the postcondition shape that scales to general length via            *)
(* byte_list_at(out_p, len) and matches AES-XTS / aes256_gcm_encrypt.           *)
(* ========================================================================= *)

let AESV8_GCM_8X_ENC_256_2BLOCK_BYTELIST = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    plaintext0 plaintext1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 4600) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 4600) (out_p:int64, 32) /\
    nonoverlapping (word pc, 4600) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (ivec_p:int64, 16) /\
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
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0x18) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = plaintext0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = plaintext1 /\
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
     (\s. read PC s = word (pc + 0x11d8) /\
          byte_list_at
            (aes_ctr_bytes ctr0 [plaintext0;plaintext1]
               [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])
            out_p (word 32) s /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              (MAP word_bytereverse
                (aes_ctr ctr0 [plaintext0;plaintext1]
                  [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC
   `\s. read PC s = word (pc + 0x11d8) /\
        read (memory :> bytes128 out_p) s =
          EL 0 (aes_ctr ctr0 [plaintext0;plaintext1]
                 [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
        read (memory :> bytes128 (word_add out_p (word 16))) s =
          EL 1 (aes_ctr ctr0 [plaintext0;plaintext1]
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
        read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              (MAP word_bytereverse
                (aes_ctr ctr0 [plaintext0;plaintext1]
                  [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])))` THEN
  CONJ_TAC THENL
   [BETA_TAC THEN GEN_TAC THEN REWRITE_TAC[AES_CTR_2_EL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BYTE_LIST_AT_2BLOCKS_CTR THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC AESV8_GCM_8X_ENC_256_2BLOCK THEN ASM_REWRITE_TAC[]]);;
