set_goal([], `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk.
    nonoverlapping (word pc, 4612) (out_p:int64, 16) /\
    nonoverlapping (word pc, 4612) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 4612) (ivec_p:int64, 16) /\
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
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_mc /\
          read PC s = word (pc + 0x2c) /\ read SP s = stackpointer /\
          read X0 s = in_p /\ read X1 s = word 128 /\
          read X9 s = word 16 /\ read X2 s = out_p /\
          read X3 s = xi_p /\ read X16 s = ivec_p /\
          read X11 s = key_p /\ read X6 s = htbl_p /\
          read Q30 s = ctr0 /\
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
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes64 (word_add stackpointer (word 64))) s =
            word 13979173243358019584)
     (\s. read PC s = word (pc + 0x11e4) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph]))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 16); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 8)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`
);;
