(* ===== WBN FRONT-N sim recipe, VALIDATED LIVE session-002 2026-07-25 =====
   Front sim entry 0x20 -> loop head 0x4a0 (pc+1184) for nblk >= 17 (nblk>8).
   Reached s288 = loop head with 73 hyps.  This is the i=0 invariant state.

   Prereqs (all in aesv8_gcm_8x_dec_256_wb_mainloop.ml + wb.ml, loaded):
   USHR_128NBLK_ANY, AND_MASK_16NBLK_ANY, WB_LOOPENTER_FLAGS, WB_PTRCMP_FLAGS,
   D_GT_128, INPUT_BYTES_TO_BYTE128_LANES, Q19_BREVXI, GCM_SIMD_SIMPLIFY_TAC,
   ARM_VSTEPS_FOLD_TAC, AESV8_GCM_8X_DEC_256_WB_EXEC, wb_front_pre_tm/frame_tm,
   wb_front_vars.

   IMPORTANT gotcha: HOL MCP process CWD = .../hol-light, NOT s2n-bignum-kiro.
   Must `Sys.chdir "/home/ubuntu/workplace/git-code/s2n-bignum-kiro"` before the
   `needs` that reads the .o (define_assert_from_elf uses a raw relative path).
   The hol-wb-dec-mainloop.ckpt bakes the chdir in, so restarts onto it skip it.
   ========================================================================= *)

(* ---- nblk>8 front hypotheses (swap 1<=nblk/\nblk<=8 for the nblk>=17 regime) *)
let wbn_front_hyps_tm =
  let base = wb_front_hyps_tm in
  let _,rest1 = dest_conj base in
  let _,rest = dest_conj rest1 in
  let newpre = `17 <= nblk /\ 128 * nblk < 2 EXP 62 /\ val (in_p:int64) + 16 * nblk < 2 EXP 63` in
  mk_conj(newpre, rest);;

let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;

let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

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

let wbn_init_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_TAC;;

(* keep only latest read Q30 fact *)
let state_num_of_read_q30 th =
  let c = concl th in
  try (match lhs c with
       | Comb(Comb(Const("read",_),q),st) when string_of_term q = "Q30" ->
           let s = fst(dest_var st) in
           if String.length s > 1 && s.[0] = 's'
           then int_of_string (String.sub s 1 (String.length s - 1)) else (-1)
       | _ -> (-1))
  with _ -> (-1);;
let DISCARD_STALE_Q30_TAC : tactic = fun (asl,w) ->
  let nums = List.filter (fun n -> n >= 0)
    (List.map (fun (_,th) -> state_num_of_read_q30 th) asl) in
  if nums = [] then ALL_TAC (asl,w) else
  let mx = itlist max nums (-1) in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let n = state_num_of_read_q30 th in n >= 0 && n < mx) (asl,w);;

(* steps 1..259: identical to wb.ml WB_FRONT_STEP_TAC but DISCARD_STALE_Q30_TAC
   for mk_discard2[30], and stops at 259 (before the 0x42c branch at step 260);
   OMITS the <=8 INT_SUB_REFL/WORD_RULE collapses (X5 != in_p for nblk>8). *)
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

(* 0x42c b.ge (step 260): nblk>=17 => X0=in_p, X5=in_p+d, NF=T VF=F, falls thru *)
let WBN_RESOLVE_42C_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* 0x49c b.ge (step 288): X0=in_p+128, X5=in_p+d, 128<d for nblk>=17 => NF=T
   VF=F, falls through to loop head 0x4a0 *)
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

(* Full front sim to the loop head.  Ends at s288, PC = pc+1184 (0x4a0). *)
let WBN_FRONT_FULL_TAC =
  wbn_init_tac THEN WBN_LANES_TAC THEN WBN_FRONT_STEP_TAC THEN
  WBN_RESOLVE_42C_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (260--260) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (261--287)) THEN
  WBN_RESOLVE_49C_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (288--288);;

(* NEXT: harvest s288 assumptions (via build_state_postcond_tms2 "s288") into
   WBN_FRONT_BUF's postcond (fold aes13 + GSYM GCM_CTR_INC*_LANES like
   wb_front_fold_tac / wb_front_postcond), then prove WBN_FRONT_BUF =
   prove(mk_wbn_front_goal <harvested>, WBN_FRONT_FULL_TAC THEN wb_front_fold_tac
   THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN REPEAT CONJ_TAC
   THEN MONOTONE_MAYCHANGE_TAC).  This s288 postcond is the i=0 invariant.
   Remember (pipelined): q8..q15 = RAW ct blocks 0..7 pending fold, Q19 = tag
   only (GHASH acc over blocks 0..-1 = empty), two-stream invariant form. *)
