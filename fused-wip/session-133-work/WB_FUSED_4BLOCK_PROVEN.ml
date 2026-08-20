(* SESSION 133: WB_FUSED_4BLOCK (k=4) FINAL PROOF (prove()).
   SIM step-map + bridge distributions + all data closers VALIDATED by wb4_close.ml stage-2
   (RESTORE_EXIT=0, BRIDGE-CLOSED-s214 fired, POST-ENSURES-FINAL nasl=1303).
   Structure = WB_FUSED_3BLOCK_PROVEN.ml extended to 4 windows.
     plain (1--30); w0 blk0xH^4 KEEPGHALL (31--81) pt0@s81; w1 blk1xH^3 (82--124) pt1@s124;
     w2 blk2xH^2 (125--167) pt2@s167; w3 blk3xH+reduce (168--214) bridge@s214;
     brev@s218; tail VSTEPS (215--227): xi@s221, ivec@s224, blk3 store@s226, b@s227.
   Bridge: qq14=qq9(+)qq1 (hi), qq13=qq8(+)qq0 (lo), qq20=qq15(+)qq16 (mid).
   Closers THEN-chained (apply to ALL post-conjuncts): xi, ivec(iter4), blk3(inc^3), blk2(inc^2),
     blk1(inc^1), blk0(bare ctr0). MAYCHANGE via WB4_FRAME_IMP (built clean at file top). *)

(* ---- MAYCHANGE frame lemma (clean env at file top; frame algebra, no fused deps) ---- *)
let WB4_MC_TRANSPORT = MESON[subsumed]
  `(R:armstate->armstate->bool) s s' ==> R subsumed R' ==> R' s s'`;;

let WB4_FRAME_SUBSUMED = prove(
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
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 16))] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 32))] ,,
   MAYCHANGE [memory :> bytes128 xi_p] ,,
   MAYCHANGE [memory :> bytes128 ivec_p] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 48))]
   :armstate->armstate->bool) subsumed
  (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 64); memory :> bytes(xi_p:int64,16);
              memory :> bytes(ivec_p:int64,16);
              memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
   MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
              Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;

let WB4_FRAME_IMP =
  SPECL [`s0:armstate`; `s227:armstate`] (REWRITE_RULE[subsumed] WB4_FRAME_SUBSUMED);;

(* GCM_CTR_INC4_LANES is le5block-only -> define in-file (base GCM_CTR_INC_LANES is in ckpt) *)
let GCM_CTR_INC4_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`,
        subst [`word 4:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;

(* ---- wb.ml-only deps ---- *)
let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;

let spec_to_byteform_wb4 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3] =
       polyval_reduce_prop3
        (word_xor (word_xor (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h4))
          (word_pmul (word_bytereverse cph1) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph3) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`] GHASH_POLYVAL_ACC_4)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let dec_bridge_specl_4_cph3 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph3:int128`; `byteswap128 h:int128`];;

let BRIDGE_CLOSE_4_CPH3_TAC sN : tactic = fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->try lhs(concl th)=parse_term(Printf.sprintf "read Q19 s%d" sN) with _->false) asl) in
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_4_cph3 GMULT4_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb4 (CONJ h2asm (CONJ h3asm h4asm))) (GSYM gmult_dec) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   SUBGOAL_THEN `qq14:int128 = word_xor qq9 qq1` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq14";"qq9";"qq1"] THEN
     GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
     REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC] THEN
   SUBGOAL_THEN `qq13:int128 = word_xor qq8 qq0` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq13";"qq8";"qq0"] THEN
     GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
     REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC] THEN
   SUBGOAL_THEN `qq20:int128 = word_xor qq15 qq16` (fun th -> REWRITE_TAC[th]) THENL
    [MAP_EVERY EXPAND_TAC ["qq20";"qq15";"qq16"] THEN
     GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
     MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   REWRITE_TAC[WORD_SUBWORD_XOR] THEN
   WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC)
  (asl,w);;

(* ---- route-b SIM helpers (verbatim from WB_FUSED_3BLOCK_PROVEN) ---- *)
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
(* SPEED (refine-093): single-pass GCM_SIMD_SIMPLIFY_CORE_TAC (was double-pass).
   Mirrors s084 (wb.ml:1784); bridge RF8_SUBWORD re-folds the boundary REV64 trees.
   MEASURED on the rebased fused ckpt: WB_FUSED_4BLOCK prove 1111.60s -> 692.54s
   (-37.7%), hyps=0 axioms=3 RESTORE_EXIT=0 (POST-ENSURES-FINAL goal-len/nasl
   IDENTICAL to double-pass: 16112/1303, so same proof state, just faster). *)
let ARM_STEPS_FOLD_KEEPGHALL_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_TAC THEN
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

let WB_FUSED_4BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 cph2 cph3 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 h3 h3k h4.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5960) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5960) (out_p:int64, 64) /\
    nonoverlapping (word pc, 5960) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 64) (xi_p, 16) /\
    nonoverlapping (out_p, 64) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 64) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 64) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 64) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 64) (in_p, 64) /\
    nonoverlapping (out_p, 64) (key_p, 240) /\
    nonoverlapping (out_p, 64) (htbl_p, 192) /\
    nonoverlapping (out_p, 64) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    word_subword h3k (0,64) :64 word =
      word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64):64 word) /\
    word_subword h3k (64,64) :64 word =
      word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 512; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
          read (memory :> bytes128 (word_add in_p (word 48))) s = cph3 /\
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
          read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k /\
          read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4)
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
          read (memory :> bytes128 (word_add out_p (word 48))) s =
          word_xor cph3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 4 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 64); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  (* UNSPLIT hk (htbl+16): fold(h)@16 lo + fold(h2)@24 hi *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0` with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN STRIP_TAC)
    else NO_TAC) THEN
  (* UNSPLIT h3k (htbl+64): fold(h3)@64 lo + fold(h4)@72 hi *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 64))) s0` with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN STRIP_TAC)
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`;
    WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 64)) (word 8) = word_add htbl_p (word 72)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--30) THEN
  (* w0 (block0 x H^4): steps 31-81, pt0 store @ s81 *)
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
  INLINE_SELFCONTAINED "Q17" "s81" 30 THEN
  INLINE_SELFCONTAINED "Q18" "s81" 30 THEN
  INLINE_SELFCONTAINED "Q19" "s81" 30 THEN
  DISCARD_OLDSTATE_TAC "s81" THEN
  (* w1 (block1 x H^3): steps 82-124, pt1 store @ s124 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (82--124) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s124:armstate) =
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
  INLINE_SELFCONTAINED "Q17" "s124" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s124" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s124" 40 THEN
  DISCARD_OLDSTATE_TAC "s124" THEN
  (* w2 (block2 x H^2): steps 125-167, pt2 store @ s167 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (125--167) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 32))) (s167:armstate) =
     word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST);
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s167" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s167" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s167" 40 THEN
  DISCARD_OLDSTATE_TAC "s167" THEN
  (* w3 (block3 x H + reduce): steps 168-214, bridge s214 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (168--214) THEN
  INLINE_SELFCONTAINED "Q19" "s214" 12 THEN
  DISCARD_OLDSTATE_TAC "s214" THEN
  SUBGOAL_THEN
    `read Q19 (s214:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s214`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_4_CPH3_TAC 214;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]` THEN
  (* tail s214->s227: rev64 v19@s218 (=brev gval) *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (215--218) THEN
  SUBGOAL_THEN `read Q19 (s218:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s218`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s218` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (219--227) THEN
  (* split the s227 bytes128 store readbacks into bytes64 halves *)
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s227" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 48)) (word 8) = word_add out_p (word 56)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 48)) (word 8) = word_add out_p (word 56)`] THEN
  (fun (asl,w) -> Printf.printf "POST-ENSURES-FINAL goal-len=%d nasl=%d\n%!" (String.length(string_of_term w)) (length asl); ALL_TAC (asl,w)) THEN
  REPEAT CONJ_TAC THEN
  (* XI (RHS = word_bytereverse of ghash_polyval_acc / gval) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
              || can (find_term (fun t -> t = `gval:int128`)) w)
        then failwith "not-xi" else
        (TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
         FIRST_X_ASSUM(SUBST1_TAC o SYM o
           check (fun th -> try rhs(concl th) = `gval:int128` &&
                                (match lhs(concl th) with
                                 | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                            with _ -> false)) THEN
         REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* ivec half (RHS = gcm_ctr_inc_iter 4) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc_iter" with _->false)) w)
        then failwith "not-ivec" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         SUBGOAL_THEN `gcm_ctr_inc_iter 4 ctr0 = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`
           SUBST1_TAC THENL
          [REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
         GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC4_LANES] THEN REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* out block-3 (out_p+48): RHS = aes256_encrypt (gcm_ctr_inc^3 ctr0) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`)) w)
        then failwith "not-blk3" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC3_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block-2 (out_p+32): RHS = aes256_encrypt (gcm_ctr_inc^2 ctr0). Guard: inc^2 AND NOT inc^3 *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w)
           || can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`)) w
        then failwith "not-blk2" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block-1 (out_p+16): RHS = aes256_encrypt (gcm_ctr_inc ctr0). Guard: inc^1 AND NOT inc^2 *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc ctr0:int128`)) w)
           || can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w
        then failwith "not-blk1" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block-0 (out_p, bare ctr0): POSITIVE guard = aes256_encrypt AND NOT gcm_ctr_inc/ghash *)
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
  (* MAYCHANGE: discard non-maychange to nasl=1, then MATCH_MP the pre-computed WB4_FRAME_IMP.
     Safety net: if MATCH_MP fails (frame ordering mismatch), DUMP the exact accumulated frame. *)
  (fun (asl,w) -> Printf.printf "MC-ENTER len=%d nasl=%d\n%!" (String.length(string_of_term w)) (length asl); ALL_TAC (asl,w)) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th -> not(maychange_term(concl th))) THEN
  (fun (asl,w) -> Printf.printf "MC-PRE-APPLY nasl=%d\n%!" (length asl);
     (List.iter (fun (_,th) -> if maychange_term(concl th) then
        Printf.printf "=== ACTUAL-FRAME:\n%s\n%!" (string_of_term (concl th))) asl);
     ALL_TAC (asl,w)) THEN
  FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP WB4_FRAME_IMP th)) THEN
  (fun (asl,w) -> Printf.printf "MC-DONE-LEMMA\n%!"; ALL_TAC (asl,w)));;
Printf.printf "WB_FUSED_4BLOCK RESULT: hyps=%d\n%!" (List.length (hyp WB_FUSED_4BLOCK));;
