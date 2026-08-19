(* SESSION 127: WB_FUSED_3BLOCK (k=3) FULL PROOF. Route-b, extended from the VALIDATED
   k=2 proof (session-126-work/wb2_v3_qq8fold.ml) using the s127 diagnostic (wb3_diag.ml,
   RESTORE_EXIT=0) which confirmed: SIM self-contains at s80/s123/s170; bridge = the SAME
   three block-0 (H^3) mid distributions as k=2 (index-shifted qq11=qq1⊕qq7, qq10=qq0⊕qq6,
   qq16=qq12⊕qq13); NO FOLD_MID_HPOW (ABBREV_INNER_PMULS folds the block1×H² mid combined).

   htable (le3block:600-604): htbl+0=h,+16=hk,+32=h2,+48=h3,+64=h3k.
   hk=[fold(h)@16, fold(h2)@24]; h3k=[fold(h3)@64, fold(h4)@72]. k=3 reads fold(h)@16,
   fold(h2)@24 (needs +24 norm), fold(h3)@64. UNSPLIT hk@16 AND h3k@64.
   SIM windows: (1--30); g3/blk0 KEEPGHALL (31--80),pt0@s80; g2/blk1 (81--123),pt1@s123;
   g1/blk2+reduce (124--170), bridge s170. Tail s170->s183: xi@s177,ivec@s180,pt2@s182. *)

(* s130 CURE for the environmental MAYCHANGE spin (see wb-dec-fused-3block-s130.md): the real
   accumulated k=3 frame is aconv-identical to a term whose `frame subsumed goal` closes in ~5s in
   a CLEAN environment, but SUBSUMED_MAYCHANGE_TAC spins ~6min after the full fused SIM (env-degraded,
   closer-independent — both the discard and plain variants spin, s130 v7f/v10).  FIX: prove the exact
   subsumption as a lemma HERE, at file top BEFORE the SIM (clean env, ~5s), then at the MAYCHANGE goal
   apply it via MATCH_MP transport + ETA + ACCEPT (instant), never re-running SUBSUMED post-SIM.
   NB: pure frame algebra, NO fused deps — provable/checkable on the base polyval-aes MCP. *)
let WB3_MC_TRANSPORT = MESON[subsumed]
  `(R:armstate->armstate->bool) s s' ==> R subsumed R' ==> R' s s'`;;

let WB3_FRAME_SUBSUMED = prove(
 `(MAYCHANGE [PC] ,, MAYCHANGE [X9] ,, MAYCHANGE [X16] ,, MAYCHANGE [X11] ,,
   MAYCHANGE [X5] ,, MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 64))] ,,
   MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 72))] ,, MAYCHANGE [events] ,,
   MAYCHANGE [X10] ,, MAYCHANGE [NF] ,, MAYCHANGE [ZF] ,, MAYCHANGE [CF] ,, MAYCHANGE [VF] ,,
   MAYCHANGE [Q30] ,, MAYCHANGE [Q19] ,, MAYCHANGE [X15] ,, MAYCHANGE [Q31] ,, MAYCHANGE [Q16] ,,
   MAYCHANGE [Q29] ,, MAYCHANGE [Q1] ,, MAYCHANGE [Q2] ,, MAYCHANGE [Q3] ,, MAYCHANGE [Q4] ,,
   MAYCHANGE [Q5] ,, MAYCHANGE [Q6] ,, MAYCHANGE [Q7] ,, MAYCHANGE [Q8] ,, MAYCHANGE [Q9] ,,
   MAYCHANGE [Q10] ,, MAYCHANGE [Q11] ,, MAYCHANGE [Q12] ,, MAYCHANGE [Q13] ,, MAYCHANGE [Q14] ,,
   MAYCHANGE [Q15] ,, MAYCHANGE [Q24] ,, MAYCHANGE [Q25] ,, MAYCHANGE [Q21] ,, MAYCHANGE [Q17] ,,
   MAYCHANGE [Q18] ,, MAYCHANGE [Q26] ,, MAYCHANGE [X0] ,, MAYCHANGE [Q0] ,, MAYCHANGE [Q20] ,,
   MAYCHANGE [Q22] ,, MAYCHANGE [Q23] ,, MAYCHANGE [memory :> bytes128 out_p] ,, MAYCHANGE [X2] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 16))] ,, MAYCHANGE [memory :> bytes128 xi_p] ,,
   MAYCHANGE [memory :> bytes128 ivec_p] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 32))]
   :armstate->armstate->bool) subsumed
  (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 48); memory :> bytes(xi_p:int64,16);
              memory :> bytes(ivec_p:int64,16);
              memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
   MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
              Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;

(* Pre-compute the DIRECT implication `frame s0 s183 ==> goal s0 s183` (clean env, at file top):
   REWRITE_RULE[subsumed] turns `frame subsumed goal` into `!x y. frame x y ==> goal x y`, then
   SPECL to the real states s0/s183.  RHS has NO eta-redex (goal applied directly), so the fused
   proof closes with a single MATCH_MP+ACCEPT — no REWRITE[ETA_AX] traversal (env-slow post-SIM). *)
let WB3_FRAME_IMP =
  SPECL [`s0:armstate`; `s183:armstate`] (REWRITE_RULE[subsumed] WB3_FRAME_SUBSUMED);;

(* ---- wb.ml-only deps (NOT in fused ckpt; ckpt loads only up to le4block) ---- *)
let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;
let spec_to_byteform_wb3 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h3))
          (word_pmul (word_bytereverse cph1) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph2) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`] GHASH_POLYVAL_ACC_3)] THEN
  SUBGOAL_THEN `polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h)) = byteswap128 h3`
    (fun th -> REWRITE_TAC[th]) THENL
  [ONCE_REWRITE_TAC[POLYVAL_DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* unmasked cph2 last-block specl (mirror k=2's dec_bridge_specl_2_cph1) *)
let dec_bridge_specl_3_cph2 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_3_CPH2_TAC: DEC_BRIDGE_CLOSE body at nblk=3, cph2 unmasked, NO FOLD_MID_HPOW,
   + the 3 block-0(H^3) mid distributions (s127 diagnostic). *)
let BRIDGE_CLOSE_3_CPH2_TAC sN : tactic = fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->try lhs(concl th)=parse_term(Printf.sprintf "read Q19 s%d" sN) with _->false) asl) in
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_3_cph2 GMULT3_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb3 (CONJ h2asm h3asm)) (GSYM gmult_dec) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   SUBGOAL_THEN `qq11:int128 = word_xor qq1 qq7` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq11";"qq1";"qq7"] THEN
     GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
     REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC] THEN
   SUBGOAL_THEN `qq10:int128 = word_xor qq0 qq6` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq10";"qq0";"qq6"] THEN
     GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
     REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC] THEN
   SUBGOAL_THEN `qq16:int128 = word_xor qq12 qq13` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq16";"qq12";"qq13"] THEN
     GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
     MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   REWRITE_TAC[WORD_SUBWORD_XOR] THEN
   WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC)
  (asl,w);;

(* ---- route-b SIM helpers (verbatim from wb2_v3_qq8fold.ml) ---- *)
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

let tprovestart = Sys.time();;
let gcprovestart = (Gc.stat()).Gc.major_collections;;
Printf.printf "PROVE-CALL-START cpu=%f major_colls=%d\n%!" tprovestart gcprovestart;;
let WB_FUSED_3BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 cph2 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 h3 h3k.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5960) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5960) (out_p:int64, 48) /\
    nonoverlapping (word pc, 5960) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 48) (xi_p, 16) /\
    nonoverlapping (out_p, 48) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 48) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 48) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 48) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 48) (in_p, 48) /\
    nonoverlapping (out_p, 48) (key_p, 240) /\
    nonoverlapping (out_p, 48) (htbl_p, 192) /\
    nonoverlapping (out_p, 48) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    word_subword h3k (0,64) :64 word =
      word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 384; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
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
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k)
     (\s. read PC s = word (pc + 0x11d0) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 32))) s =
          word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 3 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 48); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  (* UNSPLIT hk (htbl+16): g1 fold(h)@16 lo + g2 fold(h2)@24 hi *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* UNSPLIT h3k (htbl+64): g3 fold(h3)@64 lo *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 64))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* normalize hk-high address so g2 ldr d25,[x6,#24] resolves *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--30) THEN
  (* g3 window (block0 x H^3): steps 31-80, pt0 store @ s80 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--80) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s80:armstate) =
     word_xor cph0 (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s80" 30 THEN
  INLINE_SELFCONTAINED "Q18" "s80" 30 THEN
  INLINE_SELFCONTAINED "Q19" "s80" 30 THEN
  DISCARD_OLDSTATE_TAC "s80" THEN
  (* g2 window (block1 x H^2): steps 81-123, pt1 store @ s123.  Capture pt1 (counter
     gcm_ctr_inc ctr0) before DISCARD -- GCM_CTR_INC_LANES then the aes tower. *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (81--123) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s123:armstate) =
     word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST);
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s123" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s123" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s123" 40 THEN
  DISCARD_OLDSTATE_TAC "s123" THEN
  (* g1 window (block2 x H + reduce): steps 124-170, bridge s170 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (124--170) THEN
  INLINE_SELFCONTAINED "Q19" "s170" 12 THEN
  DISCARD_OLDSTATE_TAC "s170" THEN
  SUBGOAL_THEN
    `read Q19 (s170:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s170`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_3_CPH2_TAC 170;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  (* tail s170->s183: ext@s173, rev64 v19@s174 (=brev gval) *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (171--174) THEN
  SUBGOAL_THEN `read Q19 (s174:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s174`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s174` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (175--183) THEN
  (* split the s183 bytes128 store readbacks into bytes64 halves *)
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s183" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  (* normalize block-1/block-2 store hi-half addresses *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`]) THEN
  (* Peel MAYCHANGE first (else REPEAT CONJ_TAC splits its ,, structure). *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`] THEN
  (* s127 store-diag (wb3_stores_diag.ml): after ASM_REWRITE the block-1 (out_p+16, captured
     pt1@s123) and xi halves ALREADY CLOSE.  The 7 remaining conjuncts are: block-0 lo/hi
     (RHS aes256_encrypt ctr0), block-2 lo/hi (RHS aes256_encrypt (gcm_ctr_inc(gcm_ctr_inc ctr0))),
     ivec lo/hi (gcm_ctr_inc_iter 3), and MAYCHANGE.  The earlier full run HUNG because the
     block-0 closer (JOIN_IS_CTR0 + WORD_RULE, no blast) cross-fired on a block-2 conjunct and
     WORD_RULE spun on the un-normalized +2 tower.  FIX: guard each closer to its own RHS
     counter (bare ctr0 vs gcm_ctr_inc(gcm_ctr_inc)) so it never touches the wrong conjunct. *)
  (fun (asl,w) -> Printf.printf "POST-ENSURES-FINAL reached, goal-len=%d nasl=%d\n%!" (String.length(string_of_term w)) (length asl); ALL_TAC (asl,w)) THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w) -> Printf.printf "SUBGOAL len=%d\n%!" (String.length(string_of_term w)); ALL_TAC (asl,w)) THEN
  (* s128 ROOT CAUSE (localized via wb3_v4_probe ENTER/DONE timing on the fused ckpt): the STORE
     closers are FAST (blk0 0.01s, blk2 0.03s, ivec 0.00s).  The ~7-min spin was the block-0
     closer CROSS-FIRING onto the XI conjunct: xi's goal (word_bytereverse gval = word_bytereverse
     GPA) has NO gcm_ctr_inc, so the s127/v3 block-0 guard ("fail if gcm_ctr_inc") ACCEPTED it and
     ran AP_THM+JOIN_IS_CTR0+expand+WORD_BLAST on the ghash_polyval_acc poly => WORD_BLAST descended
     into the poly => spin.  FIX: POSITIVE, mutually-exclusive guards; run XI first; guard block-0
     POSITIVELY on aes256_encrypt (so it never touches the ghash goal). *)
  (* XI (RHS = word_bytereverse of ghash_polyval_acc / gval): strip word_bytereverse, then fold the
     goal's GPA back to gval via a TARGETED check-based SUBST of the gval ABBREV assumption (proven
     s122/v42 pattern) — NEVER EXPAND_TAC "gval" (it FIRST_X_ASSUM-scans, may hit read-Q19=gval asms
     over the 1242-asm context).  s129 instrumentation: XI-ENTER at guard, XI-CLOSED after body — if
     both print then spin, the spin is the final prove-replay (b), not the xi closer (a). *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
              || can (find_term (fun t -> t = `gval:int128`)) w)
        then failwith "not-xi" else
        (Printf.printf "XI-ENTER len=%d\n%!" (String.length(string_of_term w));
         let r =
           (TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
            FIRST_X_ASSUM(SUBST1_TAC o SYM o
              check (fun th -> try rhs(concl th) = `gval:int128` &&
                                   (match lhs(concl th) with
                                    | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                               with _ -> false)) THEN
            REFL_TAC) (asl,w) in
         Printf.printf "XI-CLOSED\n%!"; r))
      THEN NO_TAC) THEN
  (* ivec half (RHS = gcm_ctr_inc_iter 3) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc_iter" with _->false)) w)
        then failwith "not-ivec" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         SUBGOAL_THEN `gcm_ctr_inc_iter 3 ctr0 = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`
           SUBST1_TAC THENL
          [REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
         GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC3_LANES] THEN REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* out block-2 (out_p+32): RHS = aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)).  le4block
     WORD_XOR_ASSOC+WORD_BLAST closer (proven 0.03s in the probe). *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w)
        then failwith "not-blk2" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block-0 (out_p, bare ctr0): POSITIVE guard = has aes256_encrypt AND NOT gcm_ctr_inc/ghash,
     so it fires ONLY on the two block-0 halves.  le4block WORD_XOR_ASSOC+WORD_BLAST (probe 0.01s). *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="aes256_encrypt" with _->false)) w)
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc" with _->false)) w
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
        then failwith "not-blk0" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[JOIN_IS_CTR0] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* MAYCHANGE (len=377): s129 FINAL DIAGNOSIS. This is the SOLE remaining blocker — all store
     (blk0/blk1/blk2), xi and ivec closers work (all 7 SUBGOAL prints fire).  v7f proved with an
     MC-PRE-MONO probe: after DISCARD to nasl=1, `REWRITE[ABI] THEN REPEAT CONJ_TAC THEN MONOTONE`
     STILL SPINS 6min.  Yet the EXACT dumped frames (v8) reproduced on the base MCP close in 4.6s
     (nasl=1) / 8.4s (with 1241 junk asms) — WITH or WITHOUT discard, WITH or WITHOUT trailing
     ASM_REWRITE.  So the real accumulated MAYCHANGE assumption differs from the pretty-printed
     dump in a way that makes SUBSUMED_MAYCHANGE_TAC's SUBSUMED_SEQ_LEFT/RIGHT recursion explode
     (O(2^n) backtracking over the ~52 single-component `,,` chain).
     PROVEN CURE (next session): adopt le4block full_le4_tac_stores Q12-interleaved-respec
     (..._le4block.ml:246-281): respec plaintext reg Q12 -> opaque pt_i BEFORE each st1{v12} and
     DISCARD_OLDSTATE after each capture, so the accumulated frame stays MINIMAL and ORDERED the
     way le4block's proven closer (:353) handles — le4block closes THIS machine's MAYCHANGE. *)
  (* s130 CURE rev2: close via the PRE-COMPUTED direct implication WB3_FRAME_IMP (built at file
     top, clean env: `frame s0 s183 ==> goal s0 s183`, NO eta-redex since REWRITE_RULE[subsumed]
     specializes to the states directly).  rev1 (transport + REWRITE[ETA_AX]) spun AFTER
     MC-PRE-APPLY nasl=1 — the REWRITE[ETA_AX] traversal (or the transport MATCH_MP) is env-slow
     post-SIM.  rev2 removes REWRITE[ETA] entirely: discard to nasl=1, then one MATCH_MP+ACCEPT. *)
  (fun (asl,w) -> Printf.printf "MC-ENTER len=%d nasl=%d\n%!" (String.length(string_of_term w)) (length asl); ALL_TAC (asl,w)) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th -> not(maychange_term(concl th))) THEN
  (fun (asl,w) -> Printf.printf "MC-PRE-APPLY nasl=%d\n%!" (length asl); ALL_TAC (asl,w)) THEN
  FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP WB3_FRAME_IMP th)) THEN
  (fun (asl,w) -> Printf.printf "MC-DONE-LEMMA\n%!"; ALL_TAC (asl,w)));;
Printf.printf "ALL-SUBGOALS-DONE, entering prove-replay\n%!";;

Printf.printf "PROVE-CALL-DONE cpu_elapsed=%f major_colls_delta=%d\n%!" (Sys.time() -. tprovestart) ((Gc.stat()).Gc.major_collections - gcprovestart);;
Printf.printf "WB_FUSED_3BLOCK RESULT: hyps=%d\n%!" (List.length (hyp WB_FUSED_3BLOCK));;
