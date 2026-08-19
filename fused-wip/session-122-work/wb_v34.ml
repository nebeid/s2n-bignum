(* v33 DIAGNOSTIC: reach s97, print the 3 store readback assumptions (out/xi/ivec) at s97
   BEFORE ENSURES_FINAL, so we know their exact RHS machine forms. Then CHEAT. *)

(* ---- prelude: the folds + bridge close from bridge_close_validated.ml ---- *)
let FOLD_LO = prove(
  `word_xor (word_pmul (word_subword (word_reversefields 8 (cph:int128)) (64,64):64 word)
                       (word_subword (h:int128) (0,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                       (word_subword h (0,64):64 word)) : int128
   = word_pmul (word_subword h (0,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                 (word_reversefields 8 (word_subword cph (0,64):64 word)))`,
  REWRITE_TAC[RF8_SUBWORD] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_HI = prove(
  `word_xor (word_pmul (word_subword (word_reversefields 8 (cph:int128)) (0,64):64 word)
                       (word_subword (h:int128) (64,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (64,64):64 word))
                       (word_subword h (64,64):64 word)) : int128
   = word_pmul (word_subword h (64,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                 (word_reversefields 8 (word_subword cph (64,64):64 word)))`,
  REWRITE_TAC[RF8_SUBWORD] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_LO_N = prove(
  `word_xor (word_pmul (word_reversefields 8 (word_subword (cph:int128) (0,64):64 word))
                       (word_subword (h:int128) (0,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                       (word_subword h (0,64):64 word)) : int128
   = word_pmul (word_subword h (0,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                 (word_reversefields 8 (word_subword cph (0,64):64 word)))`,
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_HI_N = prove(
  `word_xor (word_pmul (word_reversefields 8 (word_subword (cph:int128) (64,64):64 word))
                       (word_subword (h:int128) (64,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (64,64):64 word))
                       (word_subword h (64,64):64 word)) : int128
   = word_pmul (word_subword h (64,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                 (word_reversefields 8 (word_subword cph (64,64):64 word)))`,
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_MID = prove(
  `word_xor
    (word_pmul
      (word_subword
        (word_xor
          (word_subword (word_join (word_reversefields 8 (cph:int128)) (word_reversefields 8 cph):256 word) (64,128):128 word)
          (word_reversefields 8 cph)) (0,64):64 word)
      (word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)))
    (word_pmul
      (word_subword
        (word_xor
          (word_subword
            (word_join
              (word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                         (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)
              (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                         (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word):256 word)
            (64,128):128 word)
          (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                     (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)) (0,64):64 word)
      (word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word))) : int128
   = word_pmul (word_xor (word_subword h (64,64):64 word) (word_subword h (0,64):64 word))
       (word_xor
         (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                   (word_reversefields 8 (word_subword cph (64,64):64 word)))
         (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                   (word_reversefields 8 (word_subword cph (0,64):64 word))))`,
  REWRITE_TAC[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
  MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;
let FOLD_MID2 = prove(
  `word_xor
     (word_pmul
       (word_xor
         (word_subword
           (word_subword
             (word_join (word_reversefields 8 (cph:int128)) (word_reversefields 8 cph):256 word) (64,128):128 word)
            (0,64):64 word)
         (word_reversefields 8 (word_subword cph (64,64):64 word)))
       (word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)))
     (word_pmul
       (word_xor
         (word_subword
           (word_subword
             (word_join
               (word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                          (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)
               (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                          (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word):256 word)
             (64,128):128 word)
            (0,64):64 word)
         (word_reversefields 8 (word_subword xi (64,64):64 word)))
       (word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word))) : int128
   = word_pmul (word_xor (word_subword h (64,64):64 word) (word_subword h (0,64):64 word))
       (word_xor
         (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                   (word_reversefields 8 (word_subword cph (64,64):64 word)))
         (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                   (word_reversefields 8 (word_subword cph (0,64):64 word))))`,
  REWRITE_TAC[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
  MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let BRIDGE_CLOSE_FULL_TAC =
  GEN_REWRITE_TAC RAND_CONV
    [GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
       (ISPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph) : int128`;
         `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  REWRITE_TAC[GSYM (CONJUNCT1 SUBWORD_XOR_JOIN_DIST); GSYM (CONJUNCT2 SUBWORD_XOR_JOIN_DIST)] THEN
  REWRITE_TAC[FOLD_LO; FOLD_HI; FOLD_MID; FOLD_LO_N; FOLD_HI_N] THEN
  ABBREV_INNER_PMULS_TAC THEN
  SUBGOAL_THEN `word_xor (qq4:int128) qq3 = qq2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["qq2";"qq3";"qq4"] THEN ACCEPT_TAC FOLD_MID2; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `word_xor (qq4:int128) qq3 = qq2` then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_INNER_PMULS_TAC THEN
  FINISH_WV_TAC;;

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


(* ---- store-tail closer lemmas ---- *)
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

let WB_FUSED_1BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5960) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5960) (out_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (xi_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 240) /\
    nonoverlapping (out_p, 16) (htbl_p, 192) /\
    nonoverlapping (out_p, 16) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 128; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph /\
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
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk)
     (\s. read PC s = word (pc + 0x11d0) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 1 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 16); memory :> bytes(xi_p, 16);
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
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--33) THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (34--84) THEN
  (fun (asl,w) ->
     let picks = mapfilter (fun (_,th) ->
       match concl th with
       | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),st)),_)
           when (match st with Var(n,_)->n<>"s84"|_->false) -> th
       | _ -> fail()) asl in
     RULE_ASSUM_TAC(fun th ->
       if (try lhs(concl th) = `read Q19 s84` with _ -> false)
       then REWRITE_RULE picks th else th) (asl,w)) THEN
  DISCARD_OLDSTATE_TAC "s84" THEN
  SUBGOAL_THEN
    `read Q19 (s84:armstate) =
     polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph))
       (byteswap128 h)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s84`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s84` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   BRIDGE_CLOSE_FULL_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse cph)) (byteswap128 h)` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (85--88) THEN
  SUBGOAL_THEN `read Q19 (s88:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s88`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s88` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (89--97) THEN
  (* Transform the 3 bytes128 store readbacks (out/xi/ivec) at s97 to SPEC form while gval is LIVE,
     BEFORE ENSURES_FINAL_STATE_TAC (which discards gval and splits into bytes64 halves). *)
  (* --- out: word_xor(word_xor cph TOWER) k14 = word_xor cph (aes256_encrypt ctr0 keys) --- *)
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) s97 =
     word_xor cph (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read (memory :> bytes128 out_p) s97` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `read (memory :> bytes128 out_p) s97` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* --- xi: word_bytereverse gval = word_bytereverse (ghash_polyval_acc ...) --- *)
  SUBGOAL_THEN
    `read (memory :> bytes128 xi_p) s97 =
     word_bytereverse
       (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
         [word_bytereverse cph])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read (memory :> bytes128 xi_p) s97` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `read (memory :> bytes128 xi_p) s97` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   EXPAND_TAC "gval" THEN AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT];
   ALL_TAC] THEN
  (* --- ivec: machine lane-shuffle = gcm_ctr_inc_iter 1 ctr0 --- *)
  SUBGOAL_THEN
    `read (memory :> bytes128 ivec_p) s97 = gcm_ctr_inc_iter 1 ctr0`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read (memory :> bytes128 ivec_p) s97` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if (try lhs(concl th) = `read (memory :> bytes128 ivec_p) s97` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[num_CONV `1`; gcm_ctr_inc_iter; GCM_CTR_INC_LANES];
   ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

Printf.printf "WB_FUSED_1BLOCK v34 RESULT: hyps=%d\n%!" (List.length (hyp WB_FUSED_1BLOCK));;
