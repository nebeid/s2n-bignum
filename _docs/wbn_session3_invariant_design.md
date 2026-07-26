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
- Q0..Q4 counter towers FOLD (GSYM GCM_CTR_ADD_LANES) to:
    Q0 = gcm_ctr_add (word 8)  ctr0   (= gcm_ctr_inc_iter 8  ctr0)
    Q1 = gcm_ctr_add (word 9)  ctr0
    Q2 = gcm_ctr_add (word 10) ctr0
    Q3 = gcm_ctr_add (word 11) ctr0
    Q4 = gcm_ctr_add (word 12) ctr0
- Q5 = word_xor(word_xor ct5 (aes13 (gcm_ctr_inc^5 ctr0) k0..k13)) k14   (already-XORed pt block 5)
- Q6 = ... gcm_ctr_inc^6 ...  (pt block 6)
- Q7 = ... gcm_ctr_inc^7 ...  (pt block 7)
  So at i=0 the in-flight counter/keystream state spans block indices 5..12.
  Q5/Q6/Q7 = keystream-XOR at 5,6,7 (< 8 = already-stored blocks!) => pipeline in-flight
  recompute for next group.  Q0..Q4 = raw counter blocks 8..12 (next group).
  GENERALIZE (hypothesis, VERIFY in step case): all indices shift by +8*i, i.e.
    Q0..Q4 = gcm_ctr_add (word (8*i + {8,9,10,11,12})) ctr0
    Q5..Q7 = word_xor(word_xor ct_{8i+{5,6,7}} (aes13 (gcm_ctr_inc_iter (8*i+{5,6,7}) ctr0)..))k14
  *** The exact +8*i offset for Q5..Q7 (indices <8 at i=0) is the #1 thing to READ OFF
      the step-case goal, NOT guess — plan-rationale risk #2. ***

### GHASH stream — LAGS, at 8i
- Q19 = word_bytereverse xi          (i=0: fold over 0 blocks)
   GENERALIZE (VERIFIED i=0 reduction):
     Q19 at iter i = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
                       (MAP word_bytereverse (raw ct blocks 0..8i-1))
     i.e. ghash_polyval_acc HB (word_bytereverse xi)
            (MAP word_bytereverse (list_of_seq (\k. bytes_to_int128 (SUB_LIST(16*k,16) ibytes)) (8*i)))
   Def (common/polyval_ghash.ml:56): ghash_polyval_acc h acc [] = acc;
     ghash_polyval_acc h acc (CONS x xs) = ghash_polyval_acc h (polyval_dot (word_xor acc x) h) xs.
   At i=0: empty list => ghash_polyval_acc _ (word_bytereverse xi) [] = word_bytereverse xi  ✓ (matches front)
   NOTE: the running acc has NO outer word_bytereverse (that is applied only in gcm_dec_final_xi
   at the very end). This is the ASM-NATIVE (polyval, keyed by byteswap128 h) form, keeping xi/h
   free like WBN_FRONT_BUF. NIST-vocabulary (nist_ghash H tag0 (list_of_seq (nist_input_block..) ..))
   reconciliation is deferred to Phase 6/7 recompose (the bands convert the same way).
   Extension across iters uses GHASH_ACC_APPEND (common/polyval_ghash.ml:62) — Phase 3.
- q8..q15 = RAW ct blocks pending fold:
    Q8  = bytes_to_int128 (SUB_LIST (0,16)  ibytes)
    Q9  = ... (16,16) ...   Q10 (32,16)  Q11 (48,16)
    Q12 = (64,16)  Q13 (80,16)  Q14 (96,16)  Q15 (112,16)
   generalize -> Q(8+k) = bytes_to_int128 (SUB_LIST (16*(8*i+k),16) ibytes), k=0..7
   (i.e. raw ct blocks 8i..8i+7, loaded but not yet GHASH-folded).

### Stores DONE for blocks 0..8(i+1)-1 (the store stream is ahead)
- store shape CONFIRMED: read(memory:>bytes128(out_p + word(16*j))) s =
     word_xor (word_xor (bytes_to_int128 (SUB_LIST(16*j,16) ibytes))
                        (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 .. k13)) k14
   (j=0: aes13 ctr0 ..; j=1: aes13 (gcm_ctr_inc ctr0)..; folds via gcm_ctr_inc_iter j)
   generalize -> !j. j < 8*(i+1) ==> read(out_p+16*j) = <above> = plaintext block j
   NB at i=0 the front already stored 8 blocks (out_p..out_p+112). matches X2=out_p+128.
   NB2: WBN_FRONT_BUF spells out only out_p+0..+112 as 8 EXPLICIT conjuncts (not a !j form);
        the invariant needs the quantified !j.j<8*(i+1) form. Entry proof must bridge
        the 8 explicit i=0 stores <- !j.j<8 (EXPAND_CASES_CONV both ways).

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

## SESSION-004 findings (Phase 3 done; route-b tool; a HYP GAP to fix)

### Phase 3 COMPLETE — GHASH 8-block extension algebra (committed 2c8decc0)
Proved as Sec 5 of aesv8_gcm_8x_dec_256_wb_mainloop.ml (pure list/field, no sim,
provable in the polyval-aes checkpoint since polyval_ghash.ml is loaded):
- LIST_OF_SEQ_SPLIT       list_of_seq f (m+n) = APPEND (list_of_seq f m)
                          (list_of_seq (\j. f(m+j)) n)   [induct on n]
- GHASH_ACC_GROUP_EXTEND  ghash_polyval_acc H acc (MAP wbrev (list_of_seq g (m+n)))
                          = ghash_polyval_acc H (fold over m) (MAP wbrev (next n))
- LIST_OF_SEQ_8           list_of_seq f 8 = [f 0;...;f 7] (numerals, no SUC)
- GHASH_ACC_8BLOCK_EXTEND THE deliverable: fold over 8*(i+1) = fold over 8*i then
                          8 explicit Horner steps over blocks 8*i..8*i+7.
The fully-expanded RHS (REWRITE_TAC[MAP; ghash_polyval_acc]) is the nested
polyval_dot/word_xor Horner chain the body's 8 GHASH folds produce — so in Phase 4
the body's Q19 close is: REWRITE with GHASH_ACC_8BLOCK_EXTEND (blk := \k.
bytes_to_int128(SUB_LIST(16*k,16) ibytes)) then MAP/ghash_polyval_acc, matching
the sim output block-by-block.

### Route-(b) tool ENSURES_ADD_PRESERVED (committed 4376c170, Sec 6)
  |- ensures step P Q C /\ (!s s'. P s /\ C s s' ==> R s')
     ==> ensures step P (\s. Q s /\ R s) C
Pure ensures/eventually (EVENTUALLY_MONO). Use to strengthen WBN_FRONT_BUF's
postcond with the 3 frame-preserved loop-constants WITHOUT re-sim:
  MATCH_MP_TAC ENSURES_ADD_PRESERVED (with R = the conjunction of the 3), CONJ:
  leg 1 = WBN_FRONT_BUF; leg 2 = the preservation obligation
  !s s'. wb_front_pre_tm s /\ wb_front_frame_tm s s' ==> R s'.
NB the postcond of ENSURES_ADD_PRESERVED is `\s. Q s /\ R s` — beta/assoc-normalize
so it matches the invariant's conjunct order (the entry closer already tolerates this).

### *** HYP GAP: nonoverlapping (in_p,16*nblk) (out_p,16*nblk) is MISSING ***
wbn_front_hyps_tm (mainloop:342) is built from wb.ml's wb_front_hyps_tm tail, which
does NOT contain `nonoverlapping (in_p) (out_p)`.  BUT the invariant asserts the
loop-constant `read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes`
(input read-only), and the loop body STORES to out_p.  Preserving that read across
the body's out_p stores REQUIRES in_p and out_p to be disjoint.
- The BAND goal (wb.ml:3853, mk_band_goal) DOES carry nonoverlapping (out_p,sss)
  (in_p,sss) — it is a genuine precondition of the whole function (dispatch/subr).
- So the fix for the nblk>8 chain: ADD `nonoverlapping (in_p,16*nblk)(out_p,16*nblk)`
  (and likely the full out_p-vs-everything set from wb.ml:3839-3856) to
  wbn_front_hyps_tm — it holds at the function contract level, we simply need to
  thread it through the FRONT-N lemma + the loop invariant's hypotheses.
- CONSEQUENCE for route (b): the preservation obligation for the in_p read-only
  constant is dischargeable ONLY once this nonoverlapping is in P (wb_front_pre/hyps).
  Add it to wbn_front_hyps_tm BEFORE proving WBN_FRONT_BUF_EXT.  (key_p=k0 and
  htable_mem_dec are already fine: key_p/htbl_p are disjoint from the frame's
  out_p/xi_p/ivec_p/stack via existing nonoverlapping conjuncts.)
- This does NOT require re-running the front SIM (the front doesn't store to out_p
  in a way that touches in_p; it's purely a hypothesis-threading + preservation-proof
  concern for the LOOP body and the EXT wrapper).

### Session-level infra note
hol_restart REUSES the checkpoint frozen at server import (server.py:43); editing
hol-mcp.toml does NOT switch checkpoints on hol_restart — only a full MCP server
relaunch re-reads it.  hol-mcp.toml was edited to checkpoint="wb-dec-mainloop" so the
NEXT session launches fast (~1min).  If a session ever finds WBN_FRONT_BUF absent
after restart, it is on polyval-aes and must cold-load (~44min) — or the orchestrator
must relaunch the server process.
