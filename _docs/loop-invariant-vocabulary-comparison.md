# Is the decrypt main-loop invariant in the same vocabulary as Mila's and John's?

Prepared 2026-08-17. Sources, all read directly:

| | file | invariant at |
|---|---|---|
| **John** — x4, AES-128, merged upstream | `arm/proofs/aes_gcm_enc_kernel_x4_basic.ml` @ `ce5340d3` | line 895, `ENSURES_WHILE_UP_TAC` |
| **Mila** — x8 encrypt, AES-256 | `arm/proofs/aesv8_gcm_8x_enc_256_wb.ml` @ `mila/aes_gcm_256_x8_clean` | line 3270, `ENSURES_WHILE_PUP_TAC` |
| **Ours** — x8 decrypt, AES-256 | `arm/proofs/aesv8_gcm_8x_dec_256_wb.ml` @ `c2609cf8` | line 8795, `wbn_loop_invariant` (a `new_definition`), `ENSURES_WHILE_UP_TAC` |

## Short answer

**No — and the split is clean and worth stating precisely.**

- **Mila's encrypt invariant IS John's vocabulary**, term for term, with one deliberate
  divergence (below).
- **Our decrypt invariant is a different dialect** in five specific places.
- **But our *exported* theorems ARE in the shared vocabulary** — that is what the
  2026-08-12 restatement work did. Grepping the exported `AESV8_GCM_8X_DEC_256_CORRECT`
  finds `inblock` (6×), `nist_ghash`, `ctr_block`, `aes_ctr_block`, `ghash_twist`,
  `word_reversefields`. So the alignment landed at the **export boundary**, and the loop
  invariant — a private definition, never exported — was left in the dialect it was
  developed in.

## Term-by-term

| concept | John (x4, AES-128) | Mila (x8 enc) | Ours (x8 dec) |
|---|---|---|---|
| input block | `inblock j` | `inblock j` ✅ | `bytes_to_int128 (SUB_LIST (16*k,16) ibytes)` ❌ |
| input in memory | `!j. j < nblocks ==> read(bytes128 (in_p+16j)) = inblock j` | same ✅ | `read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes` ❌ |
| counter | `ctr_block nonce (4i+2)`, wrapped `word_reversefields 32` | `ctr_block nonce (8i+15)`, same wrapper ✅ | `gcm_ctr_add (word (8i+8)) ctr0`, `gcm_ctr_inc_iter j ctr0`, `gcm_ctr_raw (word (8i+13)) ctr0` ❌ |
| keystream | `aes_ctr_block nonce rk j` | same ✅ | `aes13 (gcm_ctr_inc_iter j ctr0) k0 … k13` then `word_xor _ k14` ❌ |
| output block | `word_xor (aes_ctr_block nonce rk j) (inblock j)` | identical ✅ | `word_xor (word_xor (bytes_to_int128 (SUB_LIST …)) (aes13 …)) k14` ❌ |
| GHASH accumulator | `byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_cipher_block nonce rk inblock) (4i)))` | same, `aes256_cipher`, `8i`, **no `byteswap128`** ⚠️ | `ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) (MAP word_bytereverse (list_of_seq (\k. bytes_to_int128 (SUB_LIST …)) (8i)))` ❌ |
| GHASH key | derived: `aes128_cipher (word 0) rk` | derived: `aes256_cipher (word 0) rk` ✅ | abstract `h` ❌ |
| H-power table | `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))` | `htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk))` ✅ | `htable_mem_dec h htbl_p` ❌ |
| round keys | registers `Q18…Q28` = `word_reversefields 8 (EL n rk)` | memory at `key_p` = `word_reversefields 8 (EL n rk)` ✅ | memory at `key_p` = bare variables `k0 … k14` ❌ |
| tag seed | `word_reversefields 8 tag0` | same ✅ | `xi`, entering the accumulator as `word_bytereverse xi` ❌ |
| MODULO constant | `read Q7 s = word 13979173243358019584` | `read (memory :> bytes64 mod_p) s = word 0xc200000000000000` | `read (memory :> bytes64 (sp+64)) s = word 13979173243358019584` — same constant as John, in memory like Mila |
| loop tactic | `ENSURES_WHILE_UP_TAC`, no flag fact | `ENSURES_WHILE_PUP_TAC` + `(read NF s <=> read VF s) <=> (i = k)` | `ENSURES_WHILE_UP_TAC`, no flag fact — matches John |
| pipeline lag | none: `Q11` folds exactly `4i` | `Q8…Q15` carry the previous group's **ciphertext** | two-stream: store/counter at `8(i+1)`, GHASH at `8i`, bridged by raw ciphertext in `Q8…Q15` |

## The one divergence between Mila and John

John wraps the accumulator conjunct in `byteswap128`; Mila's does **not**. That was a
deliberate choice, not drift — her file records it as the "plain-invariant route" adopted
after sessions 018–028 dead-ended on the byteswapped form (comments at lines 1496, 2850,
2932: under the byteswapped invariant "the body-end reduce (parity 0) could never match").
So the two differ by exactly one `byteswap128`, on the same `nist_ghash` term.

Ours is byte-reversed too, but expressed differently again: `byteswap128` on the key,
`word_bytereverse` on the seed, and `MAP word_bytereverse` over the block list.

## What this means

1. **Nothing is unsound and nothing is blocked.** These are internal invariants. Ours is a
   private `new_definition` and Mila's is inline in her tactic; neither appears in an
   exported statement, so a reviewer reading the contract never sees the dialect.
2. **The reviewer-facing convergence already happened** where it counts — the exports. Our
   per-block output postcondition and encrypt's are now literally the same term.
3. **The cost of the dialect is ours alone**: every bridge between the loop invariant and
   the exported statement has to translate `ibytes`/`SUB_LIST` → `inblock`,
   `gcm_ctr_inc_iter … ctr0` → `ctr_block nonce`, `aes13 … k14` → `aes_ctr_block`, and
   `ghash_polyval_acc` → `nist_ghash`. That translation layer is real proof work that
   Mila's file does not need, because her invariant already speaks the exported language.
4. **If we ever want to share loop machinery with encrypt** — one parameterised loop lemma
   instantiated in both directions — the invariant dialect is the blocker, not the
   exports. Converting would mean restating `wbn_loop_invariant` in
   `inblock`/`ctr_block`/`aes_ctr_block`/`nist_ghash` and re-closing the body, i.e.
   re-running the main-loop simulation. Not a cleanup; a re-proof.

## Suggested framing if this comes up upstream

The honest position: "the exported specifications are unified across all three proofs; the
internal loop invariants are not, and deliberately so — each was shaped by the pipeline
structure of its own kernel (John's has no lag, encrypt lags by one group on ciphertext,
decrypt lags with a two-stream split). Unifying the invariants would require re-running the
main-loop simulations for no change in what is guaranteed."
