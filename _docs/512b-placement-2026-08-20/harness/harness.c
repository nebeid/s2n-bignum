/* pcb4 harness -- AES-256-GCM decrypt kernel, 4 variants + 4 A/A duplicates,
 * 8 message sizes, round-robin interleaved in one process.
 *
 * Method (identical in shape to _docs/percommit-crosscore-benchmark-2026-08-14.md):
 *   - all variants live in ONE binary under distinct symbols dec_s0..dec_s7
 *   - MANDATORY correctness gate first: plaintext, Xi, ivec, return value of
 *     every symbol compared byte-for-byte against the baseline slot at every size
 *   - core clock measured in-process with a dependent scalar-add chain,
 *     before and after the sweep
 *   - explicit warm-up sweep, then best-of-REPS timed reps
 *   - for each rep: for each size: every symbol timed back-to-back, visiting
 *     order rotated by rep index
 *   - Xi/ivec reset to the same seed before every timed batch
 */
#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#define NV 8
#define NS 8
#define BASELINE 1            /* slot 1 = variant B ("ours before") */

typedef size_t (*fn)(const uint8_t *, size_t, uint8_t *, uint8_t *, uint8_t *,
                     const void *, const void *);

extern size_t dec_s0(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s1(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s2(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s3(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s4(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s5(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s6(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s7(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);

static fn F[NV] = { dec_s0, dec_s1, dec_s2, dec_s3, dec_s4, dec_s5, dec_s6, dec_s7 };
/* A  = current aws-lc aesv8_gcm_8x_dec_256
 * B  = ours 5500b7e6 (before the adopted optimisations)
 * C  = ours 91b1ce25 (after the adopted optimisations)
 * D  = fused d5r
 * aaX = byte-identical second copy of X under another symbol name */
static const char *NAME[NV] = { "A_awslc", "B_5500b7e6", "C_91b1ce25", "D_fused",
                                "aaA", "aaB", "aaC", "aaD" };

static const unsigned SZ[NS]    = {   16,   32,   64,   128,  256,  512, 1024, 4096 };
static const unsigned BATCH[NS] = {100000,80000,60000, 40000,25000,12000, 7000, 3000 };

#define MAXBYTES 4096u

typedef struct { uint64_t hi, lo; } u128;
typedef struct { uint32_t rd_key[60]; unsigned rounds; } AES_KEY;
extern int  aes_hw_set_encrypt_key(const uint8_t*, int, AES_KEY*);
extern void aes_hw_encrypt(const uint8_t*, uint8_t*, const AES_KEY*);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

static uint8_t  in_ct[MAXBYTES]            __attribute__((aligned(64)));
static uint8_t  out[MAXBYTES]              __attribute__((aligned(64)));
static uint8_t  ref_out[NV][MAXBYTES]      __attribute__((aligned(64)));
static u128     Htable[16]                 __attribute__((aligned(16)));
static AES_KEY  key                        __attribute__((aligned(16)));
static uint8_t  Xi[16]                     __attribute__((aligned(16)));
static uint8_t  ivec[16]                   __attribute__((aligned(16)));
static uint8_t  ref_Xi[NV][16], ref_ivec[NV][16];
static size_t   ref_ret[NV];

static const uint8_t XI_SEED[16] = {
  0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x00 };
static const uint8_t IV_SEED[16] = {
  0xca,0xfe,0xba,0xbe,0xfa,0xce,0xdb,0xad,0xde,0xca,0xf8,0x88,0x00,0x00,0x00,0x01 };

static uint64_t st = 0x1234567890abcdefULL;
static uint8_t rb(void){ st^=st<<13; st^=st>>7; st^=st<<17; return (uint8_t)(st&0xff); }

static inline uint64_t ns(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
  return (uint64_t)t.tv_sec*1000000000ull + t.tv_nsec; }

/* Dependent scalar-add chain: 1 add/cycle on Neoverse V1/V2/V3. */
static double clock_ghz(void){
  double best = 0.0;
  for (int r = 0; r < 3; r++){
    uint64_t n = 200000000ull;
    uint64_t t0 = ns();
    __asm__ volatile(
      "mov x9, %0\n mov x10, #0\n"
      "1:\n add x10, x10, #1\n add x10, x10, #1\n add x10, x10, #1\n add x10, x10, #1\n"
      "subs x9, x9, #4\n b.ne 1b\n"
      :: "r"(n) : "x9","x10","cc");
    uint64_t t1 = ns();
    double g = (double)n / (double)(t1 - t0);
    if (g > best) best = g;
  }
  return best;
}

static void reset_state(void){
  memcpy(Xi, XI_SEED, 16);
  memcpy(ivec, IV_SEED, 16);
}

/* Returns 0 on PASS, non-zero on FAIL. Prints a full account either way. */
static int correctness_gate(void){
  int fails = 0;
  for (int si = 0; si < NS; si++){
    unsigned nb = SZ[si];
    for (int v = 0; v < NV; v++){
      memset(out, 0xA5, MAXBYTES);
      reset_state();
      ref_ret[v] = F[v](in_ct, (size_t)nb * 8u, out, Xi, ivec, &key, Htable);
      memcpy(ref_out[v], out, MAXBYTES);
      memcpy(ref_Xi[v], Xi, 16);
      memcpy(ref_ivec[v], ivec, 16);
    }
    for (int v = 0; v < NV; v++){
      if (v == BASELINE) continue;
      int bad = 0;
      if (ref_ret[v] != ref_ret[BASELINE])                                  bad |= 1;
      if (memcmp(ref_out[v], ref_out[BASELINE], MAXBYTES) != 0)             bad |= 2;
      if (memcmp(ref_Xi[v], ref_Xi[BASELINE], 16) != 0)                     bad |= 4;
      if (memcmp(ref_ivec[v], ref_ivec[BASELINE], 16) != 0)                 bad |= 8;
      if (bad){
        fails++;
        printf("GATE FAIL size=%u %s vs %s mask=%d (ret %zu vs %zu)\n",
               nb, NAME[v], NAME[BASELINE], bad, ref_ret[v], ref_ret[BASELINE]);
      }
    }
    /* also assert the return value is the byte count */
    if (ref_ret[BASELINE] != (size_t)nb){
      fails++;
      printf("GATE FAIL size=%u baseline ret=%zu expected %u\n", nb, ref_ret[BASELINE], nb);
    }
  }
  printf("GATE %s (%d failures) -- compared plaintext(%u B buffer), Xi, ivec and "
         "return value of all %d symbols against %s at all %d sizes\n",
         fails ? "FAIL" : "PASS", fails, MAXBYTES, NV, NAME[BASELINE], NS);
  return fails;
}

static double best_ns[NS][NV];

int main(int argc, char **argv){
  int reps = (argc > 1) ? atoi(argv[1]) : 200;
  int tag  = (argc > 2) ? atoi(argv[2]) : 0;

  /* ---- key / Htable / message setup ---- */
  uint8_t k[32], zero[16] = {0}, H[16];
  for (int i = 0; i < 32; i++) k[i] = rb();
  aes_hw_set_encrypt_key(k, 256, &key);
  aes_hw_encrypt(zero, H, &key);
  uint64_t Hq[2];
  memcpy(Hq, H, 16);
  gcm_init_v8(Htable, Hq);
  for (unsigned i = 0; i < MAXBYTES; i++) in_ct[i] = rb();

  /* ---- MANDATORY correctness gate, before any timing ---- */
  if (correctness_gate() != 0){
    printf("STOP: correctness gate failed, no timings reported\n");
    return 1;
  }

  double ghz_pre = clock_ghz();

  for (int si = 0; si < NS; si++)
    for (int v = 0; v < NV; v++) best_ns[si][v] = 1e30;

  /* ---- explicit warm-up: one full untimed sweep ---- */
  for (int w = 0; w < 2; w++)
    for (int si = 0; si < NS; si++)
      for (int v = 0; v < NV; v++){
        reset_state();
        for (unsigned i = 0; i < BATCH[si]; i++)
          F[v](in_ct, (size_t)SZ[si] * 8u, out, Xi, ivec, &key, Htable);
      }

  /* ---- timed reps, round-robin, visiting order rotated by rep ---- */
  for (int r = 0; r < reps; r++){
    for (int si = 0; si < NS; si++){
      for (int j = 0; j < NV; j++){
        int v = (j + r) % NV;
        unsigned n = BATCH[si];
        size_t bl = (size_t)SZ[si] * 8u;
        reset_state();
        uint64_t t0 = ns();
        for (unsigned i = 0; i < n; i++)
          F[v](in_ct, bl, out, Xi, ivec, &key, Htable);
        uint64_t t1 = ns();
        double per = (double)(t1 - t0) / (double)n;
        if (per < best_ns[si][v]) best_ns[si][v] = per;
      }
    }
  }

  double ghz_post = clock_ghz();

  printf("CLK %d %.4f %.4f\n", tag, ghz_pre, ghz_post);
  for (int si = 0; si < NS; si++)
    for (int v = 0; v < NV; v++)
      printf("RES %d %u %s %.4f\n", tag, SZ[si], NAME[v], best_ns[si][v]);
  fflush(stdout);
  return 0;
}
