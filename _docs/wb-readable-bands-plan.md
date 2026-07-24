# Plan: readable WB band theorems (8 x N-block, one wrapper layer, JRH vocabulary)

Branch: `aes-gcm-nblock-tail`.  Prereq state: lemmas-split commit `cc299039`
(core/lemmas/wb chain verified, axioms=3, hyps=0 everywhere).

## 1. Problem

The 8 per-path theorems `AESV8_GCM_8X_DEC_256_WB_{1..8}BLOCK` in
`arm/proofs/aesv8_gcm_8x_dec_256_wb.ml` are correct but not readable as specs:

* **Two layers of wrapping**: `_BUF_kBLOCK` (raw per-block stores + explicit
  `ghash_polyval_acc`) -> `_kBLOCK` wrapper (`gcm_dec_pt_bytes`/`gcm_dec_final_xi`)
  -> `_DISPATCH` -> `_DISPATCH_NIST_TAG` (in wb_nist.ml).  A reader must chase
  4 statements to find the NIST-vocabulary one, and only the quantified
  dispatch ever reaches NIST vocabulary — the per-N theorems never do.
* **Builder-generated statements**: `mk_band_goal k` / `mk_wb_wrapper_goal k`
  construct the goals programmatically.  Nothing greppable in the file shows
  what theorem N actually says; you need a REPL (`concl ...`) to read it.
* **Noise swamps payload** (printed 2BLOCK statement = ~90 lines):
  25 pairwise `nonoverlapping` conjuncts; 17 raw `read (memory ...)` key/xi/ivec
  equations; the actual crypto content is 3 lines at the end, phrased over
  `gcm_dec_*` byte-list plumbing that mentions the twisted key `h` instead of
  the NIST GHASH key `H`.

## 2. Reference points (both fetched and inspected 2026-07-24)

### JRH (`jargh/gcm`, e.g. aes_gcm_enc_kernel_x4_basic.ml) — the 3 condensations

* **C1 — nonoverlapping condensation**: region lists via `ALL (nonoverlapping ...)`
  / `ALLPAIRS nonoverlapping [..] [..]` (already used all over s2n-bignum, e.g.
  `bignum_amontifier.ml:290`).  25 conjuncts -> 2-4 lines.
* **C2 — key condensation**: `wordlist_from_memory (key_p, 15) s = rk` with one
  abstract `rk:int128 list` (defined in `common/bignum.ml:672`, N-generic;
  used by mlkem/mldsa proofs).  15 read-equations -> 1 line, and the keys
  variable list shrinks from k0..k14 to `rk`.
* **C3 — NIST payload**: tag postcondition speaks `nist_ghash H tag0 (...)`
  (SP 800-38D objects only; `ghash_twist`/POLYVAL stays inside the proof via
  `NIST_GHASH_IS_POLYVAL`), htable precondition is the named
  `htable_mem_8 (ghash_twist H)` predicate (already exists in wb_nist.ml),
  blocks indexed by a per-index function, GHASH list via `list_of_seq`.

### Mila (`mila/aes256_gcm_tail` + `aes256_gcm_whole`, arm/proofs/aes256_gcm.ml)

Worth copying:
* **Hand-written explicit statements, one per band** (`AES256_GCM_ENCRYPT_LT_kBLOCK_CONCRETE`
  at greppable line numbers) — no goal builders; the file IS the spec document.
* **Single whole-buffer spec layer**: postcondition =
  `byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0..rk14]) out_ptr len s`
  + `read xi_ptr = gcm_final_xi (val len) pt_in ivec [..] xi h`.  Two named
  functions carry ALL the crypto meaning; the ensures-triple stays short.
  (Our `gcm_dec_pt_bytes`/`gcm_dec_final_xi` in utils/aes_gcm_dec_spec.ml are
  the exact dec analogues — this layer we already have.)
* **CONCRETE -> ABS two-tier naming** (raw readback tier kept, readable tier on
  top): matches our BUF->wrapper split; keep it, but with exactly ONE readable tier.

NOT copying from Mila: her rk0..rk14 explosion (JRH's C2 beats it) and her raw
`word_swaphalves128 (polyval_dot (polyval_dot ...))` htable tower + h1k/h3k...
subword side-conditions (our named `htable_mem_8` over `h_power` beats it).

## 3. Target shape (what each of the 8 theorems should read as)

One hand-written theorem per N, in wb.ml (or a new wb_bands.ml), of this form
(N=2 shown; ~25 lines total vs ~90 now):

```
let AESV8_GCM_8X_DEC_256_WB_2BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 32 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,32; xi_p,16; ivec_p,16]
       [word pc,4560; in_p,32; key_p,240; htbl_p,192; stackpointer,80] /\
     ALLPAIRS nonoverlapping
       [out_p,32; xi_p,16] [ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc,4560; in_p,32; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 32) s /\
               wordlist_from_memory (key_p,15) s = rk /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4528) /\
               byte_list_at (gcm_dec_pt_bytes 32 ibytes ctr0 rk) out_p (word 32) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 2)))
          (...same MAYCHANGE frame...)`,
  <derivation, sim-free, from _BUF_2BLOCK>);;
```

Reading guide baked into the statement: "decrypting 2 blocks = CTR output over
the input bytes, and the new tag = standard NIST GHASH of the raw ciphertext
blocks folded onto tag0 under key H".

Layering after this change:
* `WB_FRONT_BUF` + `_BUF_{1..8}BLOCK`: unchanged internal proof artifacts
  (builder-generated is FINE here; nobody audits these as specs).
* `AESV8_GCM_8X_DEC_256_WB_{1..8}BLOCK`: THE eight readable theorems, the only
  wrapper layer, hand-written literal statements, NIST vocabulary.
* `AESV8_GCM_8X_DEC_256_WB_DISPATCH`: quantified 1<=nblk<=8 packaging of the
  eight (statement also hand-written in the same vocabulary).
* wb_nist.ml's separate `_DISPATCH_NIST_TAG` DISAPPEARS — the NIST content is
  now in the theorems themselves.  wb_nist.ml keeps only the bridge lemmas
  (htable_mem_8, GCM_DEC_FINAL_XI_NIST, ...) that the derivation uses, or is
  folded into wb.ml entirely.

Decision points settled here (change only with a reason):
* Output stays `gcm_dec_pt_bytes` (Mila-style whole-buffer function) rather
  than a per-index `cipher_block` conjunct — it is already readable, hides the
  block expansion, and avoids re-proving output plumbing.  If JRH-style
  per-index output is later wanted for the loop invariant, add it as a
  derived lemma, not by restating the bands.
* `H` stays a free variable tied to the htable (kernel never computes E_K(0);
  the E_K(0) = H connection belongs to the htable-init routine's proof).
* `ctr0` stays the raw ivec int128 (our counter helpers own the inc32 view).

## 4. New definitions and bridge lemmas needed (all small, sim-free)

1. `nist_input_block : byte list -> num -> int128`
   `nist_input_block x i = word_reversefields 8 (bytes_to_int128 (SUB_LIST (16*i,16) x))`
   — the NIST (big-endian) view of input block i.  Then prove
   `LIST_OF_SEQ_NIST_INPUT_N` (N=1..8):
   `list_of_seq (nist_input_block x) N = MAP word_bytereverse (gcm_dec_ghash_blocks (16*N) x)`
   via `GCM_DEC_GHASH_BLOCKS_WHOLE_N` unfolds + `LIST_OF_SEQ_CLAUSES` +
   `BREV_RF8_128`.  (Check first: JRH may already have `list_of_seq` clause
   lemmas in common/; search before proving.)
2. `WORDLIST_FROM_MEMORY_15`: unfold `wordlist_from_memory (key_p,15) s = rk`
   to the 15 bytes128 reads with `EL 0 rk`..`EL 14 rk` (there is a conversion
   `WORDLIST_FROM_MEMORY_CONV` or similar near the definition in
   common/bignum.ml — check how mlkem proofs expand it; reuse, don't re-prove).
   Also `LENGTH rk = 15 ==> rk = [EL 0 rk; ...; EL 14 rk]` (list-eta) so the
   BUF theorem's k0..k14 instantiate to `EL i rk`.
3. `ALLPAIRS_NONOVERLAPPING_UNFOLD`: `ALLPAIRS`/`ALL` + `REWRITE_TAC[ALLPAIRS; ALL]`
   already unfolds to the pairwise conjunction — confirm the pairwise set
   matches mk_band_goal's 25 exactly (write the target lists so that it does;
   ordering/symmetry gaps closed by `NONOVERLAPPING_SYM`).
4. Tag bridge: already have `GCM_DEC_FINAL_XI_NIST` + `BREV_RF8_128/INV` in
   wb_nist.ml; only re-target from `gcm_dec_final_xi` to the `list_of_seq` form
   using (1).

## 5. Execution steps (order matters; each step loadt-verified before the next)

1. **Scaffold in work.ml** (never edit wb.ml until the derivation works):
   load the chain through wb_nist.ml; define `nist_input_block`; prove the
   N=1,2 lemmas from step 4; hand-write the 2BLOCK target statement; derive it
   from `_BUF_2BLOCK` sim-free:
   `MATCH_MP_TAC ENSURES_PRECONDITION/POSTCONDITION` route exactly as
   `prove_wb_wrapper` does today, plus: INST h := byteswap128 (ghash_twist H),
   xi := word_reversefields 8 tag0, keys := EL i rk; rewrite with
   HTABLE_MEM_DEC_IS_HTABLE_MEM_8, wordlist unfold, ALLPAIRS unfold, tag bridge.
   Expect the whole close in seconds (it is the existing wrapper proof + 4
   rewrites).
2. **Generalize to a parametric prover** `prove_wb_readable k` in work.ml;
   check all 8 close.  The PROVER may be shared; the 8 STATEMENTS are written
   out literally in the file (that is the point of the exercise).  To avoid
   transcription errors: generate each statement once with a builder, print
   with `string_of_term`, paste as the literal `prove` goal, then DELETE the
   builder from the final file.
3. **Rewrite wb.ml tail**: replace `mk_wb_wrapper_goal`/`prove_wb_wrapper` and
   the 8 wrapper lines with the 8 literal theorems (+ the small prover tactic).
   Restate `_DISPATCH` from the new eight (same ASM_CASES split; statement
   hand-written, `16 * nblk` lengths).  Keep `_GUARD` untouched.
4. **Slim wb_nist.ml**: delete `_DISPATCH_NIST_TAG` (now redundant); move the
   still-needed bridge pieces (htable_mem_8 def, GCM_DEC_FINAL_XI_NIST, ...)
   into wb.ml above the band theorems, or keep wb_nist.ml as the bridge-lemma
   file wb.ml needs — either way ONE file defines the readable theorems.
   Update `needs` chain + any downstream references
   (grep: work.ml PROGRESS notes, _docs, wb-main-loop-plan.md references to
   DISPATCH_NIST_TAG).
5. **Cold re-verify** the WB chain (lemmas -> wb -> [wb_nist]) on a fresh
   checkpoint: axioms()=3, hyps=[] for all 8 + DISPATCH + GUARD.  ~35-40 min.
   Then chain-check the masked chain still loads (core -> le1block suffices,
   ~5 min — it does not depend on wb.ml, this is belt-and-braces).
6. **Commit** on `aes-gcm-nblock-tail`; rebase `aes-gcm-wb-mainloop` on top
   (its loop plan should then state the invariant in the same vocabulary —
   update wb-main-loop-plan.md section 3/3a accordingly, one commit).

## 6. Risks / gotchas

* `wordlist_from_memory` is `N word list`-generic — pin the type instance
  `:int128 list` in the statement or unification produces ugly casts; look at
  an mlkem usage first for the idiomatic form.
* The BUF theorems quantify k0..k14 as separate vars; instantiating with
  `EL i rk` terms is fine (SPECL), but the output spec list
  `[k0;...;k14]` inside `gcm_dec_pt_bytes` must then fold back to `rk` via the
  list-eta lemma — do this with GSYM rewriting AFTER instantiation.
* `list_of_seq` vs our `gcm_dec_ghash_blocks` index direction: verify block 0
  is the FIRST GHASH-folded block in both (it is, but check on N=2 where a
  swap is visible in the tag value; the N=1,2 lemmas in step 5.1 catch this).
* Do NOT touch `mk_band_goal`/`prove_band`/`WB_TAIL_k_TAC` — the sim layer is
  expensive to re-verify and gains nothing from this change.
* The uncommitted `_docs/wb-main-loop-plan.md` JRH-refinements edit and
  `_docs/HOL-Light-Proof-Tips-for-s2n-bignum.md` edit are sitting in the
  working tree (survived the branch moves); commit them with step 6's doc
  update, don't lose them.
* Session hygiene: this is all sim-free — no OOM risk — but the loads are
  long; use the MCP server checkpoint, `Gc.compact()` between chain loads,
  and the stale-`loaded_files` purge recipe if resuming a warm session.

## 7. Definition of done

* wb.ml (or its split) shows 8 literal `prove` statements a reviewer can read
  top-to-bottom, each <= ~30 lines, payload = 3 recognizable lines
  (byte_list_at gcm_dec_pt_bytes / word_reversefields 8 (nist_ghash ...)).
* Exactly one wrapper layer above `_BUF_`; `_DISPATCH_NIST_TAG` gone.
* Statements use C1 (ALLPAIRS/ALL), C2 (wordlist_from_memory + rk list),
  C3 (nist_ghash/htable_mem_8/list_of_seq/nist_input_block).
* Cold load: axioms()=3, hyps=[] for the 8 + DISPATCH + GUARD; masked chain
  unaffected.
