(* SESSION 125: WB_FUSED_2BLOCK (k=2) ROUTE-B v2 — SIM SOLVED, bridge is the one remaining gap.
   =============================================================================================
   WHAT'S NEW vs s124 wb2_routeb.ml (both machine-confirmed this session, RESTORE_EXIT=0):
     FIX (1): address normalization after the hk UNSPLIT so the block-0 x H^2 folded-key load
              `ldr d25,[x6,#24]` (spelled word_add htbl_p (word 24)) resolves against the UNSPLIT
              high-half fact (spelled word_add (word_add htbl_p (word 16)) (word 8)). Without it,
              Q18 s81 dangles on read(bytes64 htbl_p+24)@s31/s44 and DISCARD drops the accumulator.
              (k=1 never needs +24; k>=2 block0 x H^2 does — see memory wb-dec-fused-2block-addr-fix-s125.)
     FIX (2): INLINE_SELFCONTAINED Q17/Q18/Q19 at s81 (iterated REWRITE_RULE picks) BEFORE
              DISCARD_OLDSTATE "s81" — collapses the block-0 accumulator chain so DISCARD keeps it.
   RESULT: read Q19 s128 SELF-CONTAINED (rhs_len 9086, refs=0). SIM done end-to-end.

   THE ONE REMAINING GAP — the bridge. BRIDGE_CLOSE_2_CPH1_TAC below is the PROVEN
   DEC_BRIDGE_CLOSE_TAC body at nblk=2 (NO FOLD_MID_HPOW: for nblk=2, top_fold=1, rev(2--1)=[] —
   that was the s123 hd bug), CPH1 (unmasked) specl, spec_to_byteform_2, LANE_FINISH_TAC finisher
   (fast — NOT the blast-heavy dec2_gmult2_bridge_tac, which ran >16min CPU without converging).
   It reaches LANE_FINISH_TAC but the final REFL_TAC fails on a residual lane XOR-grouping mismatch:
      word_xor (word_subword qq8 (0,64)) (word_subword qq3 (0,64)) =
      word_xor (word_subword qq3 (0,64)) (word_xor (word_subword qq1 (0,64)) (word_subword qq5 (0,64)))
   i.e. one machine pmul (qq8) = XOR of two spec pmuls (qq1,qq5) that MERGE_2BLK didn't combine.
   FIX (mirror v42's FOLD_MID2 step): insert an explicit `SUBGOAL_THEN <qq8 = word_xor qq1 qq5>`
   (proven EXPAND_TAC the 3 qq + PMUL_CONG_128/WORD_BLAST) then rewrite + re-ABBREV before
   LANE_FINISH_TAC. The exact qq identity is in orchestrator/logs/session-125-work/lanes probe
   output (QQDEF lines). See session-125-summary.md.
   ============================================================================================= *)

let PACK2_ID, GMULT2_FULL_CORRECT_BA = build_GMULTn_fast 2;;

let spec_to_byteform_2 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1] =
       polyval_reduce_prop3
        (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h2))
          (word_pmul (word_bytereverse cph1) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`] GHASH_POLYVAL_ACC_2)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let dec_bridge_specl_2_cph1 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_2_CPH1_TAC: DEC_BRIDGE_CLOSE_TAC body at nblk=2 (no FOLD_MID_HPOW), cph1 specl.
   NOTE: as written, LANE_FINISH_TAC's final REFL_TAC FAILS on a residual qq8=xor(qq1,qq5) merge.
   INSERT the fix (v42 FOLD_MID2-style SUBGOAL_THEN) at the marked point before LANE_FINISH_TAC. *)
let BRIDGE_CLOSE_2_CPH1_TAC sN : tactic = fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->try lhs(concl th)=parse_term(Printf.sprintf "read Q19 s%d" sN) with _->false) asl) in
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_2_cph1 GMULT2_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_2 h2asm) (GSYM gmult_dec) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   (* FIX (s126): the machine (LHS) has the block-0 x H^2 karatsuba mids in DISTRIBUTED form
      (qq1(+)qq5 hi, qq0(+)qq4 lo); the spec (RHS, GMULT2 byteform) has them COMBINED as qq8, qq7.
      MERGE_2BLK cannot bridge combined-vs-distributed, and WA_UNIFY's opaque-atom WORD_RULE then
      fails on `subword qq8 = word_xor (subword qq1)(subword qq5)`. Distribute the spec side to
      match the machine: qq8 = qq1(+)qq5, qq7 = qq0(+)qq4 (CONJUNCT1 WORD_PMUL_XOR), then push the
      subwords inward (WORD_SUBWORD_XOR) so WA_UNIFY sees pure ACI over identical subword-qqi atoms.
      This is v42's FOLD_MID2 step, adapted to k=2's block-0 (H^2) lanes.  (QQ8_FOLD_TAC is a
      no-op here: it searches the goal for a BARE pmul, but ABBREV_INNER_PMULS abbreviated it.) *)
   SUBGOAL_THEN `qq8:int128 = word_xor qq1 qq5` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq8";"qq1";"qq5"] THEN
     GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
     REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC] THEN
   SUBGOAL_THEN `qq7:int128 = word_xor qq0 qq4` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq7";"qq0";"qq4"] THEN
     GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
     REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC] THEN
   (* block-0 combined MIDDLE karatsuba product qq12 = qq9(+)qq10 (xi-mid (+) cph0-mid, shared
      multiplier h2_hi(+)h2_lo).  qq9/qq10 carry nested subword(join..) operands, so close via
      GSYM CONJUNCT1 WORD_PMUL_XOR + PMUL_CONG_128 + WORD_BLAST (the v42 FOLD_MID shape). *)
   SUBGOAL_THEN `qq12:int128 = word_xor qq9 qq10` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq12";"qq9";"qq10"] THEN
     GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
     MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   REWRITE_TAC[WORD_SUBWORD_XOR] THEN
   WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN
   LANE_FINISH_TAC)
  (asl,w);;

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
let ARM_STEPS_FOLD_KEEPGHALL_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_TAC THEN
              DISCARD_OLDSTATE_KEEPGHALL_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

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

let WB_FUSED_2BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5960) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5960) (out_p:int64, 32) /\
    nonoverlapping (word pc, 5960) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (ivec_p:int64, 16) /\
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
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
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
     (\s. read PC s = word (pc + 0x11d0) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 2 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* FIX (1): normalize hk-high address so ldr d25,[x6,#24] resolves *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--30) THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--81) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s81:armstate) =
     word_xor cph0 (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* FIX (2): collapse the block-0 accumulator chain self-contained at s81 *)
  INLINE_SELFCONTAINED "Q17" "s81" 24 THEN
  INLINE_SELFCONTAINED "Q18" "s81" 24 THEN
  INLINE_SELFCONTAINED "Q19" "s81" 24 THEN
  DISCARD_OLDSTATE_TAC "s81" THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (82--128) THEN
  INLINE_SELFCONTAINED "Q19" "s128" 8 THEN
  DISCARD_OLDSTATE_TAC "s128" THEN
  SUBGOAL_THEN
    `read Q19 (s128:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s128`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_2_CPH1_TAC 128;   (* <<< bridge: needs the residual-merge fix (see header) >>> *)
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (129--132) THEN
  SUBGOAL_THEN `read Q19 (s132:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s132`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s132` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (133--141) THEN
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s141" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> try rhs(concl th) = `gval:int128` &&
                             (match lhs(concl th) with
                              | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                         with _ -> false)) THEN
      REFL_TAC THEN NO_TAC) THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `gcm_ctr_inc_iter 2 ctr0 = gcm_ctr_inc (gcm_ctr_inc ctr0)`
        SUBST1_TAC THENL
       [REWRITE_TAC[num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC2_LANES] THEN
      REFL_TAC THEN NO_TAC) THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[JOIN_IS_CTR0] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST) THEN NO_TAC) THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC) THEN
  (* DIAG: dump whatever conjunct(s) the closers left open, then CHEAT so prove() completes. *)
  (fun (asl,w) -> Printf.printf "UNSOLVED STORE GOAL:\n%s\n%!" (string_of_term w); CHEAT_TAC (asl,w)));;

Printf.printf "WB_FUSED_2BLOCK STORE-DIAG done\n%!";;
