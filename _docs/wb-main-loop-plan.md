# WB main-loop proof plan (nblk > 8, ENSURES_WHILE)

Status: DESIGN (2026-07-24). Target binary: `arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.S/.o`
(the whole-blocks decrypt; guard rejects bit_len = 0 or not a multiple of 128 —
AESV8_GCM_8X_DEC_256_WB_GUARD already covers the error path for ALL bit_len,
so the loop proof only ever sees bit_len = 128*nblk).

Decision record: we extend the WB chain to symbolic nblk (the aws-lc caller
always passes whole blocks, memory `project_gcm_dec_caller_whole_blocks`);
the masked-partial-block production binary keeps its separate le-band chain.

## 1. Control flow for nblk > 8 (from the .o disassembly)

```
entry+guard (0x0..0x1c)         -- WB_GUARD path if invalid
saves / front (0x20 .. 0x428)   -- 8 keystream towers in flight (aes13 x8)
0x42c: b.ge .L256_dec_tail(0xec0)     -- taken iff nblk <= 8
  [nblk <= 8: proven chain: WB_FRONT_BUF -> WB_TAIL_k -> DISPATCH(_NIST_TAG)]
0x430..0x498: bulk-8 first group: ldp x4 ciphertext, eor3+stp 8 results,
              counters 8..12 prepared
0x49c: b.ge .L256_dec_prepretail(0x9f0)  -- taken iff no full loop iteration left
0x4a0: .L256_dec_main_loop               -- body 0x4a0..0x9ec
0x9ec: b.lt .L256_dec_main_loop          -- backedge (cmp x0,x5 at 0x9e4)
0x9f0: .L256_dec_prepretail              -- GHASH-fold of the last in-flight
                                            8-group, no stores
0xec0: .L256_dec_tail                    -- the proven tail cascade entry
```

Loop body work per iteration: GHASH-accumulate the PREVIOUS 8 ciphertext
blocks (registers q8..q15 loaded last iteration) into q17/18/19 with one
prop3 reduction, generate 8 new keystreams, load next 8 ciphertext blocks,
eor3+store 8 plaintext results. Software-pipelined: GHASH lags stores by
one group.

## 2. Decomposition (ENSURES_TRANS chain, FRAME_SUBSUMED style)

For nblk > 8 write nblk = 8*(q+1) + r' shaped as: first-8 group + q full loop
iterations + prepretail + tail(r), where r = nblk - 8*(q+1) in 1..8
(q = (nblk-9) DIV 8; nblk<=8 stays on the proven DISPATCH).

  A. FRONT-N     entry(0x20) -> 0x4a0-equivalent state (front + bulk-8 +
                 loop-entry compare NOT taken). Generalizes WB_FRONT_BUF:
                 same sim, but the 0x42c branch now falls through, plus the
                 0x430..0x49c segment. Postcondition = harvested literal
                 (aes13 towers + 8 stored plaintexts + counter at 12).
  B. LOOP        ENSURES_WHILE_UP q invariant (see below), body =
                 0x4a0..0x9ec straight-line sim (~340 instrs) proved ONCE.
  C. PREPRETAIL  0x9f0 -> 0xec0: fold GHASH of the final in-flight group.
  D. TAIL        0xec0 -> exit: the r-block tail = EXACTLY the WB_TAIL_r_TAC
                 machinery (r in 1..8, same 8-way dispatch as today).

ENSURES_SEQUENCE_TAC throws MAYCHANGE_IDEMPOT on our 4-region frame; use the
validated FRAME_SUBSUMED + ENSURES_TRANS route (le1block/TASK-4 lesson).
Every seam postcondition MUST include aligned_bytes_loaded (WB_FRONT_BUF fix).

## 3. Loop invariant (iteration i of q, JRH x4_basic quadruple adapted)

State after i body executions, in the NIST vocabulary (now native in wb.ml:
  the readable AESV8_GCM_8X_DEC_256_WB_{1..8}BLOCK + _DISPATCH statements
  speak nist_ghash / nist_input_block / htable_mem_8 / wordlist_from_memory
  directly; wb_nist.ml is gone):

  - PC = 0x4a0-loop-head; X0 = in_p + 128*(i+1) [+128 lookahead offsets as
    the sim dictates]; X2 = out_p + 128*(i+1); X5 loop bound unchanged.
  - Counter: v30 carries gcm_ctr_inc^(8*(i+1)+4-ish) ctr0 — exact lane
    offsets read off the harvested state (gcm_ctr_inc_iter composes).
  - Keystreams in flight: q0..q7 = aes13 towers of counters for group i+1.
  - Ciphertext lookahead: q8..q15 = blocks 8(i+1)..8(i+1)+7 (rev64'd per
    the pipeline stage), from the buffer hypothesis via
    INPUT_BYTES_TO_BYTE128_LANES at symbolic index.
  - GHASH accumulator (the JRH register-invariant move; settles the midacc
    convention): the q17/18/19-fold equals the half-swap/pre-ext form of
      ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        (MAP word_bytereverse (blocks 0 .. 8i-1))
    == via GCM_DEC_FINAL_XI_NIST: word_reversefields 8 (nist_ghash H tag0
        (prefix 8i)) modulo the ext/rev64 permutation (BREV_JOIN_REV8).
    Invariant extension lemma: NIST_GHASH_APPEND / GHASH_ACC_APPEND +
    GHASH_POLYVAL_ACC_8 (the 8-block Horner step, already in
    common/ghash_nblock_karatsuba.ml).
  - Output cells: !j < 8*(i+1). read bytes128(out_p+16j) =
      word_xor (block j) (aes256_encrypt (gcm_ctr_inc^j ctr0) keys)
    (APPEND/SNOC list extension, or byte_list_at over the 128*(i+1) prefix).
  - Frame/loop-invariant memory: htable_mem_8 (ghash_twist H) htbl_p s
    (expand via REWRITE[htable_mem_8] BEFORE stepping the body — fast_tail
    lesson: named memory predicates must be unpacked ahead of the ldrs);
    key cells k0..k14; SP frame untouched.

Hypothesis-pile discipline: NONE of the per-step discard steppers needed in
the body proof — the ENSURES_WHILE framing discards everything not in the
invariant at each iteration boundary (proof-tips doc "Loop invariants ARE a
discard mechanism"). Body is ~340 instructions with 8 GHASH folds; if the
raw pile still blows up mid-body, reuse ARM_STEPS_FOLD_Q18LATEST_TAC
inside the single body proof only.

## 3a. Refinements from JRH's loop-invariant tutorial + his PROVEN kernels

Sources: John's loop-invariant tutorial (2026-06-17, proof-tips doc "Finding
the Loop Invariant") AND his actual proofs on `jargh/gcm` (fetched 2026-07-24:
aes_gcm_enc_kernel_x4_{basic,ilp,fast_tail,scalar_iv_mem_late_tag_scalar_rk}).
Checked against ground truth — corrects two earlier overstatements:

* OUR LOOP IS FULL-BLOCK => LAG-FREE, SINGLE GHASH CLAUSE (the big one). Every
  PROVEN JRH x4 kernel processes a complete 4-block group per iteration and
  carries ONE GHASH clause at the CURRENT index:
    read Q11 s = byteswap128 (nist_ghash H tag0
                   (list_of_seq (nist_cipher_block ...) (4 * i)))
  NO lag, NO "half-updated" split. Our WB body is the exact analog with 8-block
  groups, so mirror it: ONE q17/18/19 GHASH clause at 8*i (blocks 0..8i-1
  folded), output cells current for j < 8*i, counter = gcm_ctr_inc^(8i+off).
  The software-pipeline lag only exists in John's SLOTHY `_swp` variant, which
  is committed as .S with NO proof .ml — he has not proven a pipelined GCM loop.
  Since we process whole blocks (not SLOTHY-rescheduled), we are in the proven
  full-block regime. (Contingency only: IF a future target is pipelined asm,
  split into two disjoint-state clauses at different indices — CTR reads only
  the counter, GHASH only ciphertext. Not needed here.)

  NOTE: this supersedes the earlier §3 phrasing that put the fold at "8i" while
  describing a q8..q15 lookahead "not yet folded" — in the full-block loop the
  8 ciphertext blocks for group i are loaded AND folded within iteration i;
  there is no cross-boundary in-flight group. Re-pin the exact counter offset
  and whether any load is hoisted during the §3b bootstrap sim.

* GHOSTS PROBABLY UNNEEDED. John's proven kernels use ZERO ghost variables — a
  full-block loop names everything crossing the boundary directly (in_p+64*i,
  ctr_block nonce (4*i+2), nist_ghash ...(4*i)). Do NOT pre-emptively add
  ghosts for v30 / q8..q15 / q17-19. Only introduce one if the bootstrap sim
  shows a needed hypothesis vanishing (arm_print_log := true pinpoints the
  erasing instruction).

* RE-ASSERT ALL LOOP-CONSTANTS explicitly (nothing is inherited): round keys
  k0..k14 in their reg/mem cells, htable_mem_8 predicate, input pointer base,
  SP frame, and the X5 loop bound = word(16*nblk). John's kernels re-list every
  round key (Q18..Q28) and htable_mem_4 in the invariant verbatim; omit one and
  the step case silently loses it. Also carry the input-untouched clause
  (!j < nblk. read bytes128(in_p+16j) = inblock j) exactly as he does.

* BOOTSTRAP EMPIRICALLY (§3b below; do before finalizing the §3 term). Skeleton
  invariant -> ENSURES_WHILE_UP_TAC -> prove ONLY the entry subgoal by sim.
  John's own entry-subgoal proof is `ARM_SIM_TAC ... [1]` after an
  `ASM_CASES_TAC loop_count = 0` trivial split — copy that shape.

## 3b. Skeletal ENSURES_WHILE_UP_TAC invariant (bootstrap term)

Modeled on JRH x4_basic (aes_gcm_enc_kernel_x4_basic.ml:895-933). Placeholders
in <angle brackets> are the values to PIN by proving the entry subgoal (§3b
bootstrap) — do NOT trust them until the sim confirms. Key WB-vs-JRH deltas
already baked in:
  - 8 blocks/iter (128 B), so pointer stride is 128*i (JRH: 64*i); loop body is
    0x4a0..0x9ec; head 0x4a0, back-edge target 0x4a0, exit 0x9f0.
  - Our loop RELOADS round keys from memory each iter (ldp q26,q27,[x11]) rather
    than keeping them in Q-regs. So the invariant carries the KEY MEMORY CELLS
    + htable_mem_dec, NOT key registers (JRH lists Q18..Q28; we do not).
  - GHASH accumulator lives in q17/18/19 in our midacc convention; express it
    via the SAME spec fold our bands already use (gcm_dec_final_xi / the
    nist_ghash form), at the CURRENT index 8*i (no lag — §3a).
  - Counter register v30 is well ahead in the pipeline (.S shows "CTR block
    8k+13", "8k+20" inside the body) => the counter offset is NOT 8*i; pin the
    exact gcm_ctr_inc power at entry.

```ocaml
(* loop_count q = number of FULL 8-block main-loop iterations; nblk = 8*? + r.
   Pin q's closed form from the X5/X0 rung lemmas (§4) before this. *)
ENSURES_WHILE_UP_TAC `q:num` `pc + 0x4a0` `pc + 0x9f0`
  `\i s.
     // --- aligned code + control ---
     aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
     read X5 s = word (16 * nblk) /\                 // loop bound, constant
     read X0 s = word_add in_p  (word (128 * i + <in_off>)) /\
     read X2 s = word_add out_p (word (128 * i)) /\  // store ptr (pin exact)
     read X11 s = key_p /\  read X6 s = htbl_p /\     // (pin reg numbers)
     // --- counter (PIN the power: NOT 8*i; body pre-advances v30) ---
     read Q30 s = <ctr_step_const> /\                // the +1 lane increment
     read Q<ctr> s = word_reversefields 32
                       (gcm_ctr_inc_iter (8 * i + <ctr_off>) ctr0) /\
     // --- GHASH accumulator, CURRENT index 8*i (single clause, no lag) ---
     read Q17 s = <midacc_lo i> /\
     read Q18 s = <midacc_hi i> /\
     read Q19 s = <midacc_x i> /\
       // where the (q17,q18,q19) triple = the half-swap/pre-ext image of
       //   ghash over (MAP ... (SUB_LIST (0, 16*8*i) ibytes))
       // stated exactly as the band files' gcm_dec_final_xi fold at 8*i.
     // --- loop-constant memory (re-assert ALL; nothing inherited) ---
     htable_mem_dec h htbl_p s /\
     read (memory :> bytes128 (word_add key_p (word 0)))   s = k0 /\
     // ... k1..k13 ... /\   (all 15 round-key cells)
     read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
     // --- input untouched over the whole buffer ---
     read (memory :> bytes (in_p, 16 * nblk)) s = num_of_bytelist ibytes /\
     // --- output cells written for the first 8*i blocks (CURRENT) ---
     (!j. j < 8 * i
          ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
              word_xor (bytes_to_int128 (SUB_LIST (16*j,16) ibytes))
                       (aes256_encrypt (gcm_ctr_inc_iter j ctr0)
                          [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]))`
```

Bootstrap procedure (copy JRH's shape, x4_basic:886-937):
  1. `REWRITE_TAC[htable_mem_dec; GSYM CONJ_ASSOC]` then `CONJ_TAC`.
  2. Entry subgoal: `ASM_CASES_TAC \`q = 0\`` (trivial: no full iteration ->
     goes straight to prepretail/tail; discharge by short sim), else set up the
     WHILE. For i=0 the entry reduces to the FRONT-N postcond (segment A) with
     the empty-fold base (`list_of_seq ... 0` / gcm_dec_final_xi at 0), closed
     by `ARM_SIM_TAC ... [1]` + `REWRITE_TAC[... nist_ghash/list_of_seq base]`.
  3. Read the ACTUAL X0/X2/Q30/Q<ctr>/Q17-19 values off the resulting goal;
     replace every <placeholder>; re-run entry to green. Only THEN attempt the
     step case (the ~340-instr body sim) with the frozen invariant.

## 4. Scalar lemmas to generalize first (the nblk-dependent rungs)

The two front folding lemmas were proved for the 1..8 range where X5
collapses (AND_MASK_16NBLK gave X5=0 / in_p-vs-in_p compares). For nblk > 8:
  - USHR_128NBLK    : X9 := word(16*nblk) — unchanged shape, wider range.
  - AND_MASK_16NBLK : becomes X5 := word(128 * ((16*nblk) DIV 128 - 1))-ish
    (the main-loop byte bound). Characterize EXACTLY from the .S (and x5,
    ..., #~127 on the decremented length) before any sim; this drives the
    0x42c fall-through, the 0x49c skip decision, and the 0x9e4 backedge
    count q. Expect one MOD/DIV bridge lemma (16*nblk arithmetic, style of
    X1_MOD128_BRIDGE).

## 5. Deliverables / order of work

  1. Scalar rung characterization (item 4) — pure word/arith lemmas, no sim.
  2. FRONT-N harvested statement (regen recipe from wb.ml postcond literal;
     extend the harvest window 0x42c -> 0x4a0) — symbolic nblk > 8.
  3. INVARIANT BOOTSTRAP (§3a): skeletal invariant + prove ONLY the entry
     subgoal by sim; pin the counter-lane offsets and register roles; freeze
     the §3 invariant term. Cheap, de-risks the big step.
  4. LOOP body proof (ENSURES_WHILE_UP_TAC, invariant above) — the big one.
  5. PREPRETAIL segment (one straight-line sim, GHASH-fold close =
     FOLD_MID_HPOW/DEC_BRIDGE_CLOSE machinery on the 8-term bridge). This is
     where the lagging GHASH clause (§3a) catches up to the CTR clause.
  6. Recompose + extend DISPATCH: AESV8_GCM_8X_DEC_256_WB_CORRECT for ALL
     nblk >= 1 (ASM_CASES nblk <= 8 -> existing AESV8_GCM_8X_DEC_256_WB_DISPATCH
     (already in NIST vocabulary);
     nblk > 8 -> A;B;C;D chain), postcondition already in nist_ghash form.
  7. ARM_ADD_RETURN_STACK_TAC subroutine wrapper + GUARD combination =
     the complete whole-function contract.

Template: JRH x4_basic (`_docs/jargh_gcm/aes_gcm_enc_kernel_x4_basic.ml`,
loop close ~940-1060) + our seam recipe (proof-tips doc, WB sections).
