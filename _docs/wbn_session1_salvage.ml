(* ===== salvaged from session 01d76082 eval @ 2026-07-24T06:42:36.502Z ===== *)
let WBN_FRONT_PREP_BUF_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_TAC; ALL_TAC];;
let wbn_init_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_TAC;;
(try ignore(e wbn_init_tac); "OK" with Failure s -> "FAIL: " ^ String.sub s 0 (min 300 (String.length s)));;

(* ===== salvaged from session 01d76082 eval @ 2026-07-24T07:07:31.631Z ===== *)
(* input lanes 0..7 needed by the bulk-8 ldp block at 0x430 *)
let WBN_LANES_TAC =
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s0 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;
"WBN_LANES_TAC defined";;

(* ===== salvaged from session 01d76082 eval @ 2026-07-24T07:09:11.083Z ===== *)
(* Fact: with nblk >= 17, the loop bound d = 128*((nblk-1) DIV 8) satisfies 128 < d *)
let D_GT_128 = prove
 (`!nblk. 17 <= nblk ==> (128 < 128 * (nblk - 1) DIV 8 <=> T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 128 < 128 * q`) THEN
  SUBGOAL_THEN `16 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC);;
(* resolver for the 0x49c b.ge: x0 = in_p+128 vs x5 = in_p + d *)
let WBN_RESOLVE_49C_TAC : tactic = fun (asl,w) ->
  (MP_TAC(SPECL [`in_p:int64`; `128`; `128 * (nblk - 1) DIV 8`] WB_PTRCMP_FLAGS) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_TAC;
       MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
       MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN NBLK_ARITH_TAC];
     ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   MP_TAC(SPEC `nblk:num` D_GT_128) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) (asl,w);;
"resolvers ok";;

(* ===== salvaged from session 01d76082 eval @ 2026-07-24T08:02:31.873Z ===== *)
(* keep ONLY the latest read Q30 fact; drop older big Q30 facts *)
let state_num_of_read_q30 th =
  let c = concl th in
  try (match lhs c with
       | Comb(Comb(Const("read",_),q),st) when string_of_term q = "Q30" ->
           let s = fst(dest_var st) in
           if String.length s > 1 && s.[0] = 's'
           then int_of_string (String.sub s 1 (String.length s - 1))
           else (-1)
       | _ -> (-1))
  with _ -> (-1);;
let DISCARD_STALE_Q30_TAC : tactic = fun (asl,w) ->
  let nums = List.filter (fun n -> n >= 0)
    (List.map (fun (_,th) -> state_num_of_read_q30 th) asl) in
  if nums = [] then ALL_TAC (asl,w) else
  let mx = itlist max nums (-1) in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let n = state_num_of_read_q30 th in n >= 0 && n < mx) (asl,w);;
(* also drop >500ch facts that mention read Q30 IN THE RHS (the rev32 towers copied out),
   but NOT the Q30 fact itself... actually towers land in Q0..Q4; keep those. *)
"discard tactics defined";;

(* ===== salvaged from session 01d76082 eval @ 2026-07-24T08:09:50.035Z ===== *)
let WBN_FRONT_STEP_TAC =
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--5) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--84) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (85--173) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (174--177) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (178--189) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (190--254) THEN
  DISCARD_STALE_Q30_TAC THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [255] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (256--259);;
g wbn_min_goal;;
e wbn_init_tac;;
e WBN_LANES_TAC;;
"restart ready";;

(* ===== salvaged from session 01d76082 eval @ 2026-07-24T08:35:10.716Z ===== *)
(* generic-w lemma: the rev32-lane shape = rev32 of gcm_ctr_add w ctr0.
   First define the symbolic counter add: adds w to the byte-reversed top lane. *)
let gcm_ctr_add = new_definition
 `gcm_ctr_add (w:32 word) (ivec:128 word) : 128 word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse (word_subword ivec (96,32):(32)word)) w))`;;
(* sanity: gcm_ctr_add (word 1) = gcm_ctr_inc *)
let GCM_CTR_ADD_1 = prove
 (`gcm_ctr_add (word 1) = gcm_ctr_inc`,
  REWRITE_TAC[FUN_EQ_THM; gcm_ctr_add; gcm_ctr_inc]);;
"gcm_ctr_add defined";;

(* ===== wbn_min_goal @ 2026-07-24T06:41:40.602Z ===== *)
b();; (* drop the failed prep attempt state *)
let wbn_front_hyps_tm = subst [`128 * nblk < 2 EXP 62`,`16 * nblk < 2 EXP 62`] wbn_front_hyps_tm;;
let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;
let wbn_min_goal = mk_wbn_front_goal `\s:armstate. read PC s = word (pc + 0x4a0)`;;
"regenerated";;

(* ===== NBLK_ARITH_TAC @ 2026-07-24T06:41:40.602Z ===== *)
b();; (* drop the failed prep attempt state *)
let wbn_front_hyps_tm = subst [`128 * nblk < 2 EXP 62`,`16 * nblk < 2 EXP 62`] wbn_front_hyps_tm;;
let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;
let wbn_min_goal = mk_wbn_front_goal `\s:armstate. read PC s = word (pc + 0x4a0)`;;
"regenerated";;

