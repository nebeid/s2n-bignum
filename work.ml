(* ============================================================================
   WORK FILE — readable WB band theorems (2026-07-24).
   Executing _docs/wb-readable-bands-plan.md.

   HIGH-LEVEL STRUCTURE (English):
   Goal: replace the builder-generated AESV8_GCM_8X_DEC_256_WB_{1..8}BLOCK
   wrappers with 8 literal, hand-written theorems in JRH vocabulary:
     C1: nonoverlapping via ALLPAIRS + PAIRWISE + ALL (24 conjuncts -> 3
         clauses; NOTE: plan's packaging missed (out_p,xi_p)/(out_p,ivec_p) —
         fixed with PAIRWISE nonoverlapping [out_p,..; xi_p,16; ivec_p,16])
     C2: keys via wordlist_from_memory (key_p,15) s = rk  (rk:int128 list)
     C3: tag postcondition = word_reversefields 8 (nist_ghash H tag0
         (list_of_seq (nist_input_block ibytes) N)); htable precondition =
         htable_mem_8 (ghash_twist H) htbl_p s
   Derivation (sim-free, per band k): take the old byte-list wrapper theorem
   (internal, over _BUF_kBLOCK), instantiate
     ki := EL i rk, h := byteswap128 (ghash_twist H),
     xi := word_reversefields 8 tag0,
   rewrite with HTABLE_MEM_DEC_IS_HTABLE_MEM_8 + GCM_DEC_FINAL_XI_NIST +
   BREV_RF8_128/INV + GSYM LIST_OF_SEQ_NIST_INPUT_k; then close the readable
   goal by ENSURES_PRECONDITION_THM with KEY_READS_FROM_WORDLIST bridging the
   key reads, RK_ETA_15 folding [EL 0 rk;...;EL 14 rk] -> rk, and
   ALLPAIRS/PAIRWISE/ALL + NONOVERLAPPING_SYM hitting the band hypotheses.

   PROGRESS (session 2026-07-24):
   - [x] nist_input_block defined
   - [x] LIST_OF_SEQ_NIST_INPUT 1..8 via build_list_of_seq_nist (instant)
   - [x] RK_ETA_15, KEY_READS_FROM_WORDLIST
   - [x] prove_wb_readable k: ALL 8 close (~1s total), hyps=0
   - [x] WB_READABLE_DISPATCH (hand statement, symbolic nblk 1..8) closes,
         hyps=0, axioms()=3
   - [x] wb.ml tail REWRITTEN: NIST bridge layer folded in (from wb_nist.ml),
         8 literal band statements + literal DISPATCH; statements verified
         term-identical to the session-proven goals (parse check = true x9);
         composed WB_READABLE_TAC k BUF_k tested on band 1.  wb_nist.ml
         DELETED (git rm); needs "common/ghash_nist_bridge.ml" added to wb.ml.
   - [ ] cold verify (fresh checkpoint: loadt wb.ml; axioms=3, hyps=0 x10)
   - [ ] masked-chain sanity (core -> le1block)
   - [ ] commit + wb-main-loop-plan.md vocabulary update

   NOTE: everything below was the work.ml scaffold; the file content has been
   PROMOTED into arm/proofs/aesv8_gcm_8x_dec_256_wb.ml (NIST-vocabulary bridge
   layer + readable-band prover).  Kept here only until cold verify passes.
   ============================================================================ *)

(* ---- the NIST (big-endian) view of input block i --------------------------- *)
let nist_input_block = new_definition
 `nist_input_block (x:byte list) (i:num) : int128 =
    word_reversefields 8 (bytes_to_int128 (SUB_LIST (16 * i, 16) x))`;;

(* list_of_seq (nist_input_block x) N = MAP word_bytereverse (gcm_dec_ghash_blocks (16*N) x) *)
let ghash_wholes = [GCM_DEC_GHASH_BLOCKS_WHOLE_1;GCM_DEC_GHASH_BLOCKS_WHOLE_2;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_3;GCM_DEC_GHASH_BLOCKS_WHOLE_4;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_5;GCM_DEC_GHASH_BLOCKS_WHOLE_6;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_7;GCM_DEC_GHASH_BLOCKS_WHOLE_8];;
let build_list_of_seq_nist n =
  let goal = list_mk_forall([`x:byte list`],
    mk_eq(list_mk_comb(`list_of_seq:(num->int128)->num->int128 list`,
            [mk_comb(`nist_input_block`,`x:byte list`); mk_small_numeral n]),
          mk_comb(`MAP (word_bytereverse:int128->int128)`,
            list_mk_comb(`gcm_dec_ghash_blocks`, [mk_small_numeral(16*n);`x:byte list`])))) in
  prove(goal,
    GEN_TAC THEN REWRITE_TAC[el (n-1) ghash_wholes; MAP] THEN
    REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--n)))) THEN
    REWRITE_TAC[LIST_OF_SEQ; o_DEF; nist_input_block; BREV_RF8_128] THEN
    CONV_TAC NUM_REDUCE_CONV);;
let LIST_OF_SEQ_NIST_INPUT = map build_list_of_seq_nist (1--8);;

(* list-eta at 15 for the round-key list *)
let RK_ETA_15 = prove
 (`!rk:int128 list. LENGTH rk = 15
     ==> rk = [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
               EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk;
               EL 13 rk; EL 14 rk]`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_LIST_OF_SEQ] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--15)))) THEN
  REWRITE_TAC[LIST_OF_SEQ; o_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* keys: wordlist_from_memory eq -> the 15 bytes128 read equations *)
let KEY_READS_FROM_WORDLIST = prove
 (`!(key_p:int64) (rk:int128 list) s.
     wordlist_from_memory (key_p,15) s = rk
     ==> read (memory :> bytes128 key_p) s = EL 0 rk /\
         read (memory :> bytes128 (word_add key_p (word 16))) s = EL 1 rk /\
         read (memory :> bytes128 (word_add key_p (word 32))) s = EL 2 rk /\
         read (memory :> bytes128 (word_add key_p (word 48))) s = EL 3 rk /\
         read (memory :> bytes128 (word_add key_p (word 64))) s = EL 4 rk /\
         read (memory :> bytes128 (word_add key_p (word 80))) s = EL 5 rk /\
         read (memory :> bytes128 (word_add key_p (word 96))) s = EL 6 rk /\
         read (memory :> bytes128 (word_add key_p (word 112))) s = EL 7 rk /\
         read (memory :> bytes128 (word_add key_p (word 128))) s = EL 8 rk /\
         read (memory :> bytes128 (word_add key_p (word 144))) s = EL 9 rk /\
         read (memory :> bytes128 (word_add key_p (word 160))) s = EL 10 rk /\
         read (memory :> bytes128 (word_add key_p (word 176))) s = EL 11 rk /\
         read (memory :> bytes128 (word_add key_p (word 192))) s = EL 12 rk /\
         read (memory :> bytes128 (word_add key_p (word 208))) s = EL 13 rk /\
         read (memory :> bytes128 (word_add key_p (word 224))) s = EL 14 rk`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--14)))) THEN
  REWRITE_TAC[EL; HD; TL]);;

(* ---- band k byte-list wrapper, instantiated + rewritten into NIST shape ---- *)
let bsw_inv = SPEC `ghash_twist H` BYTESWAP128_INVOLUTION;;
let mk_wrapper_nist k wrapper_thm =
  let winst = SPECL ([`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
                      `in_p:int64`;`key_p:int64`;`htbl_p:int64`;`ibytes:byte list`;
                      `word_reversefields 8 (tag0:int128)`;`ctr0:int128`] @
                     map (fun i -> list_mk_comb(`EL:num->(int128)list->int128`,
                            [mk_small_numeral i; `rk:int128 list`])) (0--14) @
                     [`byteswap128 (ghash_twist H)`]) wrapper_thm in
  let xi_rw = MP (SPECL [`H:int128`; `byteswap128 (ghash_twist H)`;
                         mk_small_numeral(16*k); `ibytes:byte list`;
                         `word_reversefields 8 (tag0:int128)`] GCM_DEC_FINAL_XI_NIST)
                 bsw_inv in
  REWRITE_RULE[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; BYTESWAP128_INVOLUTION; xi_rw;
               GSYM (el (k-1) LIST_OF_SEQ_NIST_INPUT); BREV_RF8_INV_128; BREV_RF8_128] winst;;

(* ---- readable-band statement builder (used ONLY to cross-check the literal
   statements pasted into wb.ml; deleted from the final wb.ml) --------------- *)
let mk_readable_goal k =
  let n16 = mk_small_numeral(16*k) and n128 = mk_small_numeral(128*k) in
  subst [n16,`sss:num`; n128,`bbb:num`]
   `!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
     ibytes (rk:int128 list) (H:int128) tag0 ctr0.
      LENGTH ibytes = sss /\ LENGTH rk = 15 /\
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [out_p,sss; xi_p,16; ivec_p,16]
        [word pc,4560; in_p,sss; key_p,240; htbl_p,192; stackpointer,80] /\
      PAIRWISE nonoverlapping [out_p,sss; xi_p,16; ivec_p,16] /\
      ALL (nonoverlapping (stackpointer,80))
        [word pc,4560; in_p,sss; key_p,240; htbl_p,192]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
                read PC s = word (pc + 0x20) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [in_p; word bbb; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
                byte_list_at ibytes in_p (word sss) s /\
                read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
                read (memory :> bytes128 ivec_p) s = ctr0 /\
                wordlist_from_memory (key_p,15) s = rk /\
                htable_mem_8 (ghash_twist H) htbl_p s)
           (\s. read PC s = word (pc + 4528) /\
                byte_list_at (gcm_dec_pt_bytes sss ibytes ctr0 rk) out_p (word sss) s /\
                read (memory :> bytes128 xi_p) s =
                word_reversefields 8
                  (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) kkk)))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(out_p,sss); memory :> bytes(xi_p,16);
                       memory :> bytes(ivec_p,16);
                       memory :> bytes(stackpointer,80)] ,,
            MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                       Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`
  |> subst [mk_small_numeral k,`kkk:num`];;

(* ---- the shared close tactic + all 8 (against session names) --------------- *)
let wrappers = [AESV8_GCM_8X_DEC_256_WB_1BLOCK;AESV8_GCM_8X_DEC_256_WB_2BLOCK;
                AESV8_GCM_8X_DEC_256_WB_3BLOCK;AESV8_GCM_8X_DEC_256_WB_4BLOCK;
                AESV8_GCM_8X_DEC_256_WB_5BLOCK;AESV8_GCM_8X_DEC_256_WB_6BLOCK;
                AESV8_GCM_8X_DEC_256_WB_7BLOCK;AESV8_GCM_8X_DEC_256_WB_8BLOCK];;
let RK15 = `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
             EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk;
             EL 13 rk; EL 14 rk]:int128 list`;;
let prove_wb_readable k =
  let wn = mk_wrapper_nist k (el (k-1) wrappers) in
  prove(mk_readable_goal k,
    REPEAT GEN_TAC THEN REWRITE_TAC[ALLPAIRS;PAIRWISE;ALL] THEN STRIP_TAC THEN
    MP_TAC wn THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(RK15,`rk:int128 list`)) SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RK_ETA_15 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    FIRST_X_ASSUM(fun th ->
      EXISTS_TAC (rand(rator(rator(concl th)))) THEN MP_TAC th) THEN
    DISCH_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th ->
      try MP_TAC(MATCH_MP KEY_READS_FROM_WORDLIST th)
      with Failure _ -> failwith "no wordlist assumption") THEN
    SIMP_TAC[]);;
let readables = map prove_wb_readable (1--8);;

(* ---- the readable dispatch (hand statement, symbolic 1 <= nblk <= 8) ------- *)
let wb_readable_dispatch_goal =
 `!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
   nblk ibytes (rk:int128 list) (H:int128) tag0 ctr0.
    1 <= nblk /\ nblk <= 8 /\
    LENGTH ibytes = 16 * nblk /\ LENGTH rk = 15 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [out_p,16 * nblk; xi_p,16; ivec_p,16]
      [word pc,4560; in_p,16 * nblk; key_p,240; htbl_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
      [word pc,4560; in_p,16 * nblk; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
              read PC s = word (pc + 0x20) /\
              read SP s = stackpointer /\
              C_ARGUMENTS [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
              byte_list_at ibytes in_p (word (16 * nblk)) s /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s = ctr0 /\
              wordlist_from_memory (key_p,15) s = rk /\
              htable_mem_8 (ghash_twist H) htbl_p s)
         (\s. read PC s = word (pc + 4528) /\
              byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p (word (16 * nblk)) s /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
                (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) nblk)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(out_p,16 * nblk); memory :> bytes(xi_p,16);
                     memory :> bytes(ivec_p,16);
                     memory :> bytes(stackpointer,80)] ,,
          MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                     Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`;;
let WB_READABLE_DISPATCH = prove(wb_readable_dispatch_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nblk = 1 \/ nblk = 2 \/ nblk = 3 \/ nblk = 4 \/ nblk = 5 \/ nblk = 6 \/ nblk = 7 \/ nblk = 8`
    MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  FIRST (map (fun w -> MATCH_MP_TAC w THEN ASM_REWRITE_TAC[]) readables));;

(* sanity *)
let () =
  if exists (fun th -> hyp th <> []) (WB_READABLE_DISPATCH :: readables) then
    failwith "readable bands: unexpected hypotheses"
  else if List.length (axioms()) <> 3 then
    failwith "unexpected axiom count"
  else Format.print_string "readable bands + dispatch: hyps=0, axioms=3\n";;
