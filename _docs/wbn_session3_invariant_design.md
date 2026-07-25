# WBN Phase 2 — two-stream ENSURES_WHILE invariant design (session-003)

Cold-load of `arm/proofs/aesv8_gcm_8x_dec_256_wb_mainloop.ml` CONFIRMED
end-to-end: `hol_load` 2647s (~44 min), `WBN_FRONT_BUF` present, hyps=0.
The background make_checkpoint ALSO materialized
`hol-light/hol-wb-dec-mainloop.ckpt/` (1194 MB, ckpt_*.dmtcp + restart script) —
independently re-confirms cold-load and is a reusable checkpoint (orchestrator
should point hol-mcp.toml checkpoint = "wb-dec-mainloop"). Session-002 caveat RESOLVED.

## Loop control flow (objdump, frozen .o)
- Loop head  pc1 = 0x4a0 (PC=pc+1184). WBN_FRONT_BUF postcond lands here = i=0 invariant.
- Back-edge: 0x9e4 `cmp x0,x5`; 0x9e8 `stp q6,q7,[x2],#32`; 0x9ec `b.lt 0x4a0`.
- Exit fall-through: 0x9f0 (prepretail). So ENSURES_WHILE_UP_TAC pc1=pc+0x4a0, pc2=pc+0x9ec.
- Count q = (nblk-9) DIV 8  (per STATE.md/plan). Bound ptr X5 = in_p + 128*((nblk-1)DIV8).

## i=0 state layout harvested off WBN_FRONT_BUF postcond (47 conjuncts)
Read via structural walk (session-003). Confirms the TWO-STREAM pipelined form:

### Pointer / counter stream — AHEAD, at 8(i+1)
- X0 = in_p  + 128        -> generalize  in_p  + word(128*(i+1))
- X2 = out_p + 128        -> generalize  out_p + word(128*(i+1))
- Q0..Q4 = counter towers word_join(...gcm_ctr_inc^k...) ; Q2/Q3/Q4 carry `word_add _ (word 10/11/12)` inner adds
- Q5 = word_xor(word_xor ct5 (aes13 (gcm_ctr_inc^5 ctr0) k0..k13)) k14   (already-XORed pt, next group)
- Q6 = ... gcm_ctr_inc^6 ...
- Q7 = ... gcm_ctr_inc^7 ...
  (Q0..Q7 = the in-flight keystream/counter for the NEXT group being produced.)

### GHASH stream — LAGS, at 8i
- Q19 = word_bytereverse xi          (i=0: fold over 0 blocks = byte-reversed tag only)
   generalize -> the GHASH acc over blocks 0..8i-1 (byteswap/nist_ghash fold form)
- q8..q15 = RAW ct blocks pending fold:
    Q8  = bytes_to_int128 (SUB_LIST (0,16)  ibytes)
    Q9  = ... (16,16) ...   Q10 (32,16)  Q11 (48,16)
    Q12 = (64,16)  Q13 (80,16)  Q14 (96,16)  Q15 (112,16)
   generalize -> Q(8+k) = bytes_to_int128 (SUB_LIST (16*(8*i+k),16) ibytes), k=0..7
   (i.e. raw ct blocks 8i..8i+7, loaded but not yet GHASH-folded).

### Stores DONE for blocks 0..8(i+1)-1 (the store stream is ahead)
- memory bytes128 (out_p + word(16*j)) = word_xor(keystream) ... for j < 8  at i=0
   generalize -> !j. j < 8*(i+1) ==> read(out_p+16*j) = plaintext block j
   NB at i=0 the front already stored 8 blocks (out_p..out_p+112). matches X2=out_p+128.

### Loop-constant registers (constant across i — must be RE-ASSERTED)
- X4  = in_p + word(16*nblk)         (input end pointer)
- X5  = word(128*((nblk-1)DIV8)) + in_p   (loop bound ptr; drives cmp x0,x5)
- X9  = word(16*nblk)
- X10 = stackpointer + word 64
- X1  = word(128*nblk)
- X15 = word 4294967296   (= 2^32, the ctr increment constant lane)
- X31/Q31 = word 79228162514264337593543950336 (= 2^96, ctr hi lane const)
- X16 = ivec_p ; X6 = htbl_p ; X3 = xi_p ; X11 = key_p ; SP = stackpointer
- Q26 = k12, Q27 = k13, Q28 = k14 (some round keys live in regs)
- htable predicate (htable_mem_dec h htbl_p) — loop constant, re-assert
- input read-only: !j. j < 16*nblk (or block form) ==> read(in_p...) = ibytes — re-assert

### Flag facts at the head (from front's last cmp) — likely NOT in invariant
- CF, ZF present at i=0 (residue of front's cmp). The ENSURES_WHILE_UP form uses an
  UNCONDITIONAL cbnz-style back-edge; but this loop's back-edge is `b.lt` (signed,
  flag-conditional). => may need ENSURES_WHILE_PUP/PAUP (P variant) with a ZF/NF flag
  conjunct, OR the UP form if the cmp+b.lt is folded into the body's last steps.
  DECIDE during entry-subgoal bootstrap. (STATE.md says UP; but back-edge is b.lt so
  the flag test must be handled — see WB_PTRCMP_FLAGS which resolves the signed compare.)

## Template (proven JRH enc x4, _docs/jargh_gcm/aes_gcm_enc_kernel_x4_basic.ml:895)
- GHASH clause: read Q11 s = byteswap128(nist_ghash H tag0 (list_of_seq (nist_cipher_block..) (4*i)))
- counter: read Q31 s = word_reversefields 32 (ctr_block nonce (4*i+2))
- ptr: word_add in_p (word(64*i)); stores: !j. j<4*i ==> ...
- keys in Q18..Q28, htable_mem_4, input !j.j<nblocks re-asserted. ZERO ghosts.
- entry subgoal closed by: ARM_SIM_TAC EXEC [1] then REWRITE list_of_seq/nist_ghash.

## NEXT (session continues / next session)
1. Build symbolic invariant term `\i s. ...` from the table above (counters via
   GCM_CTR_INC_ITER_ADD; q8..q15 via SUB_LIST at 8i+k; Q19 GHASH fold at 8i; stores j<8(i+1)).
2. ENSURES_WHILE_UP_TAC (or PUP if b.lt flag needed) `q=(nblk-9)DIV8` `pc+0x4a0` `pc+0x9ec` inv.
3. Prove ONLY entry subgoal: i=0 instance = WBN_FRONT_BUF postcond. Should discharge by
   MATCH_MP_TAC WBN_FRONT_BUF (after arith-normalizing 128*(0+1)=128, 8*0=0, list_of_seq..0).
4. Read register/counter roles off the *step* goal; FREEZE the invariant term.
