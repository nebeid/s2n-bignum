(* ========================================================================= *)
(* Functional correctness proof for aesv8_gcm_8x_enc_256 1-block path.       *)
(* Proves BOTH ciphertext output AND GHASH tag update.                       *)
(* No CHEAT_TAC, no new axioms. ~75s total.                                  *)
(* ========================================================================= *)

needs "common/karatsuba_pmul.ml";;

(* Tactic to abbreviate all word_pmul subterms of type :128 word *)
let ABBREV_ALL_PMUL_TAC =
  let pmul_tm = `word_pmul` in
  fun (asl,w) ->
    let pmuls = find_terms (fun t ->
      try fst(strip_comb t) = pmul_tm && type_of t = `:128 word`
      with _ -> false) w in
    let unique_pmuls = setify pmuls in
    let n = ref 0 in
    let tacs = List.map (fun t ->
      incr n;
      let name = "pmul_"^string_of_int !n in
      ABBREV_TAC (mk_eq(mk_var(name, type_of t), t))
    ) unique_pmuls in
    (EVERY tacs) (asl,w);;

(* Discard counter registers but keep Q16-Q21 for GHASH *)
let DISCARD_COUNTER_ONLY_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let s = string_of_term(concl th) in
    try String.sub s 0 7 = "read PC" ||
        String.sub s 0 7 = "read NF" ||
        String.sub s 0 7 = "read ZF" ||
        String.sub s 0 7 = "read CF" ||
        String.sub s 0 7 = "read VF"
    with _ -> false)));;

let AESV8_GCM_8X_ENC_256_1BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    plaintext xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk.
    nonoverlapping (word pc, 4600) (out_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4600) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (xi_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (ivec_p, 16) (word_add stackpointer (word 64):int64, 8) /\
    nonoverlapping (xi_p, 16) (in_p, 16) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (word_add stackpointer (word 64):int64, 8) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 240) /\
    nonoverlapping (out_p, 16) (htbl_p, 192) /\
    nonoverlapping (out_p, 16) (word_add stackpointer (word 64):int64, 8) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_mc /\
          read PC s = word (pc + 0x2c) /\ read SP s = stackpointer /\
          read X0 s = in_p /\ read X1 s = word 128 /\
          read X9 s = word 16 /\ read X2 s = out_p /\
          read X3 s = xi_p /\ read X16 s = ivec_p /\
          read X11 s = key_p /\ read X6 s = htbl_p /\
          read Q30 s = ctr0 /\
          read (memory :> bytes128 in_p) s = plaintext /\
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
     (\s. read (memory :> bytes128 out_p) s =
          word_xor plaintext (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc h (word_bytereverse xi)
              [word_bytereverse
                (word_xor plaintext
                  (aes256_encrypt ctr0
                    [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 16); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 8)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  (* === AES-256 encryption: steps 1-265 === *)
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (1--11) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (12--13) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (14--15) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (16--17) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (18--19) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (20--21) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (22--23) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (24--25) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (26--84) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (85--184) THEN DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (185--255) THEN DISCARD_COUNTER_REGS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (256--265) THEN DISCARD_COUNTER_REGS_TAC THEN
  (* === Assert Q9 = ciphertext === *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(word_xor plaintext (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])):int128`
    o MATCH_MP (MESON[] `read Q9 s = a ==> !a'. a = a' ==> read Q9 s = a'`)) THEN
  ANTS_TAC THENL
  [ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[WORD_XOR_ASSOC];
   DISCH_TAC] THEN
  (* === Steps 266-324 === *)
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_ENC_256_EXEC (266--310) THEN
  DISCARD_COUNTER_REGS_TAC THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_ENC_256_EXEC (311--324) THEN
  DISCARD_COUNTER_REGS_TAC THEN
  (* === VSTEPS 325-332: ciphertext store + assertion === *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_ENC_256_EXEC (325--332) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s332:armstate) =
     word_xor plaintext (aes256_encrypt (ctr0:int128)
       [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  (* === GHASH: steps 333-352 === *)
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_ENC_256_EXEC (333--352) THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  (* === Close proof === *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_BLAST) THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]) THEN
  (* === GHASH functional correctness === *)
  REWRITE_TAC[ghash_polyval_acc; polyval_dot; polyval_reduce_prop3; PMUL_KARATSUBA] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_ALL_PMUL_TAC THEN
  CONV_TAC WORD_BLAST);;
