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
