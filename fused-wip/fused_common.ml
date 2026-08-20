(* ============================================================================
   fused_common.ml — shared tactic library for the d5 fused small-path arc.

   Extracted (refine-094, MODE=elegance) from the four canonical fused block
   proofs, which each redefined these helpers verbatim (byte-identical, md5-
   confirmed) because each is loaded STANDALONE on the fused DMTCP checkpoint.
   Collapsing them here removes ~190 lines of cross-file duplication with no
   change to behaviour: the definitions below are copied verbatim from the
   canonical files.

   Load prereq: the fused checkpoint (hol-wb-dec-fused-rebased.ckpt), which
   supplies GCM_SIMD_SIMPLIFY_CORE_TAC, CLARIFY_TAC, ARM_VERBOSE_STEP_TAC,
   DISCARD_ASSUMPTIONS_TAC, WORD_PMUL_SYM, polyval_dot, etc.  Each fused block
   proof `needs "fused-wip/fused_common.ml"` at its top and drops its local
   copies.

   Contents:
     DISCARD_OLDSTATE_KEEPGHALL_TAC   (was in k=1,2,3,4)
     ARM_STEPS_FOLD_KEEPGHALL_TAC     (was in k=1,2,3,4)
     JOIN_IS_CTR0                     (was in k=1,2,3,4)
     INLINE_SELFCONTAINED             (was in k=2,3,4)
     POLYVAL_DOT_SYM                  (was in k=3,4)
   ============================================================================ *)

(* ---- state-discard helper that keeps the GHASH accumulator regs + htbl loads ---- *)
let DISCARD_OLDSTATE_KEEPGHALL_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_htbl t = match t with
      Var("htbl_p",_) -> true
    | Comb(a,b) -> mentions_htbl a || mentions_htbl b | Abs(_,t2) -> mentions_htbl t2 | _ -> false in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19"||n="Q20"||n="Q21"||n="Q22"||n="Q23"||n="Q24"||n="Q25"||n="Q26"||n="Q30" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    if (match concl thm with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),cmp),_)),_) -> mentions_htbl cmp
        | _ -> false) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;

(* ---- per-window symbolic-execution stepper (single-pass GCM_SIMD, refine-093) ----
   MAP_EVERY over the step range: verbose-step, single-pass GCM_SIMD_SIMPLIFY_CORE_TAC
   (the 2nd CORE pass of the old double-pass is a no-op except on block-boundary REV64
   folds, which the bridge re-does downstream via RF8_SUBWORD), keep-GHALL discard,
   clarify.  Measured -18..-38% replay per k on the rebased fused ckpt (refine-093). *)
let ARM_STEPS_FOLD_KEEPGHALL_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_TAC THEN
              DISCARD_OLDSTATE_KEEPGHALL_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* ---- ctr0 rebuild: the byte-shuffled reconstruction of the 128-bit counter ---- *)
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

(* ---- collapse a Q-register's accumulator chain self-contained at state st ---- *)
let INLINE_SELFCONTAINED reg st npass : tactic = fun (asl,w) ->
  let lhs_t = parse_term (Printf.sprintf "read %s %s" reg st) in
  let rec nonSt tm = match tm with
      Comb(Comb(Const("read",_),_),stv) ->
        (match stv with Var(n,_) when n<>st -> [stv] | _ -> [])
    | Comb(a,b) -> union (nonSt a) (nonSt b) | Abs(_,t) -> nonSt t | _ -> [] in
  let target_rhs aslx =
    try rhs(concl(snd(List.find (fun (_,th) -> try lhs(concl th)=lhs_t with _->false) aslx)))
    with Not_found -> `T` in
  let rec go n (asl,w) =
    if n <= 0 then ALL_TAC (asl,w)
    else if nonSt (target_rhs asl) = [] then ALL_TAC (asl,w)
    else
      let picks = mapfilter (fun (_,th) ->
        match concl th with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),stv)),_)
            when (match stv with Var(nm,_)->nm<>st|_->false) -> th
        | _ -> fail()) asl in
      (RULE_ASSUM_TAC(fun th ->
         if (try lhs(concl th) = lhs_t with _ -> false)
         then REWRITE_RULE picks th else th) THEN go (n-1)) (asl,w) in
  go npass (asl,w);;

(* ---- polyval_dot symmetry (was redefined in k=3,4) ---- *)
let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;

(* ---- parameterised route-b bridge close (was BRIDGE_CLOSE_{2,3,4}_CPH*_TAC) ----
   For k>=2 the three per-k bridge tactics were structurally identical (same prelude
   + finisher, md5-confirmed) and differed ONLY in the spec-equation `spec_eq` and the
   three karatsuba-mid qq-distribution identities the machine (LHS, DISTRIBUTED) needs
   to match the spec (RHS, GMULTk byteform, COMBINED).  Two of the three are "LAND-shape"
   (subword-level, CONJUNCT1 WORD_PMUL_XOR + WORD_XOR_ACI) and one is "MID-shape"
   (nested subword(join..) operands, GSYM CONJUNCT1 + PMUL_CONG_128 + WORD_BLAST).
   The caller passes sN, the pre-built spec_eq (from its own spec_to_byteform_wbK /
   dec_bridge_specl / GMULTk_FULL_CORRECT_BA + h-assumptions), and the (lo,hi,mid) triples. *)
let bridge_qq_land (a,b,c) : tactic =
  SUBGOAL_THEN (parse_term (Printf.sprintf "(%s:int128) = word_xor %s %s" a b c))
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC [a;b;c] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
    REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC];;

let bridge_qq_mid (a,b,c) : tactic =
  SUBGOAL_THEN (parse_term (Printf.sprintf "(%s:int128) = word_xor %s %s" a b c))
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC [a;b;c] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
    MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC];;

let DEC_BRIDGE_ROUTEB_TAC sN spec_eq (lo_triple,hi_triple,mid_triple) : tactic =
  fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->
    try lhs(concl th)=parse_term(Printf.sprintf "read Q19 s%d" sN) with _->false) asl) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   bridge_qq_land lo_triple THEN
   bridge_qq_land hi_triple THEN
   bridge_qq_mid mid_triple THEN
   REWRITE_TAC[WORD_SUBWORD_XOR] THEN
   WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC)
  (asl,w);;
