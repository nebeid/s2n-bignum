/* h2.c -- placement / alignment probe harness for the AES-256-GCM whole-blocks
 * decrypt kernel.  NV slots live in ONE binary under symbols dec_s0..dec_s<NV-1>.
 *
 * Kept from the banked pcb4 harness (aead-bench-2026-08-20):
 *   - MANDATORY differential correctness gate before any timing: plaintext
 *     buffer, Xi, ivec and return value of every slot byte-compared against
 *     slot 0, at a size list that covers every code band (not just the timed
 *     sizes);
 *   - explicit warm-up sweeps;
 *   - in-process core-clock measurement (dependent scalar-add chain) before
 *     and after the timed sweep;
 *   - Xi/ivec reset to the same seed before every timed batch;
 *   - batch sizes chosen so every timed batch exceeds 1 ms.
 * Changed on purpose:
 *   - the per-rep visiting order is a fresh RANDOM PERMUTATION (Fisher-Yates
 *     on an xorshift stream seeded from the process tag and rep index), not a
 *     rotation: a rotation leaves the immediate-predecessor relation of every
 *     slot invariant, which is exactly the confound we are chasing.
 *
 * Output: one CLK line and NS*NV RES lines per process.
 */
#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

#ifndef NV
#error "define NV"
#endif

typedef size_t (*fn)(const uint8_t *, size_t, uint8_t *, uint8_t *, uint8_t *,
                     const void *, const void *);
#define DECL(i) extern size_t dec_s##i(const uint8_t*,size_t,uint8_t*,uint8_t*,uint8_t*,const void*,const void*);
DECL(0) DECL(1) DECL(2) DECL(3) DECL(4) DECL(5) DECL(6) DECL(7)
static fn F[8] = { dec_s0,dec_s1,dec_s2,dec_s3,dec_s4,dec_s5,dec_s6,dec_s7 };
static const char *NAME[8] = { SLOTNAMES };

/* timed sizes: 512 B is the target; 256 and 1024 are controls; 64 B is the
 * POSITIVE control (D's fused path genuinely differs there). */
static const unsigned SZ[]    = {    64,   256,   512,  1024 };
static const unsigned BATCH[] = {100000, 30000, 20000, 10000 };
#define NS ((int)(sizeof SZ / sizeof SZ[0]))

/* gate sizes: every band, including the fused nblk=1..4 bodies and the
 * 8k+r tail cascade. */
static const unsigned GSZ[] = { 16,32,48,64,80,96,112,128,144,160,176,192,
                                208,224,240,256,272,384,512,528,1024,1040,
                                2048,4080,4096 };
#define NG ((int)(sizeof GSZ / sizeof GSZ[0]))

#define MAXBYTES 4096u

typedef struct { uint64_t hi, lo; } u128;
typedef struct { uint32_t rd_key[60]; unsigned rounds; } AES_KEY;
extern int  aes_hw_set_encrypt_key(const uint8_t*, int, AES_KEY*);
extern void aes_hw_encrypt(const uint8_t*, uint8_t*, const AES_KEY*);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

static uint8_t  in_ct[MAXBYTES]        __attribute__((aligned(64)));
static uint8_t  out[MAXBYTES]          __attribute__((aligned(64)));
static uint8_t  ref_out[8][MAXBYTES]   __attribute__((aligned(64)));
static u128     Htable[16]             __attribute__((aligned(16)));
static AES_KEY  key                    __attribute__((aligned(16)));
static uint8_t  Xi[16]                 __attribute__((aligned(16)));
static uint8_t  ivec[16]               __attribute__((aligned(16)));
static uint8_t  ref_Xi[8][16], ref_ivec[8][16];
static size_t   ref_ret[8];

static const uint8_t XI_SEED[16] = {
  0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x00 };
static const uint8_t IV_SEED[16] = {
  0xca,0xfe,0xba,0xbe,0xfa,0xce,0xdb,0xad,0xde,0xca,0xf8,0x88,0x00,0x00,0x00,0x01 };

static uint64_t st = 0x1234567890abcdefULL;
static uint8_t rb(void){ st^=st<<13; st^=st>>7; st^=st<<17; return (uint8_t)(st&0xff); }

static inline uint64_t ns(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
  return (uint64_t)t.tv_sec*1000000000ull + t.tv_nsec; }

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

static void reset_state(void){ memcpy(Xi, XI_SEED, 16); memcpy(ivec, IV_SEED, 16); }

static int correctness_gate(void){
  int fails = 0;
  for (int gi = 0; gi < NG; gi++){
    unsigned nb = GSZ[gi];
    for (int v = 0; v < NV; v++){
      memset(out, 0xA5, MAXBYTES);
      reset_state();
      ref_ret[v] = F[v](in_ct, (size_t)nb * 8u, out, Xi, ivec, &key, Htable);
      memcpy(ref_out[v], out, MAXBYTES);
      memcpy(ref_Xi[v], Xi, 16);
      memcpy(ref_ivec[v], ivec, 16);
    }
    for (int v = 1; v < NV; v++){
      int bad = 0;
      if (ref_ret[v] != ref_ret[0])                            bad |= 1;
      if (memcmp(ref_out[v], ref_out[0], MAXBYTES) != 0)        bad |= 2;
      if (memcmp(ref_Xi[v], ref_Xi[0], 16) != 0)               bad |= 4;
      if (memcmp(ref_ivec[v], ref_ivec[0], 16) != 0)           bad |= 8;
      if (bad){ fails++; printf("GATE FAIL size=%u %s vs %s mask=%d (ret %zu vs %zu)\n",
                nb, NAME[v], NAME[0], bad, ref_ret[v], ref_ret[0]); }
    }
    if (ref_ret[0] != (size_t)nb){ fails++;
      printf("GATE FAIL size=%u slot0 ret=%zu expected %u\n", nb, ref_ret[0], nb); }
  }
  printf("GATE %s (%d failures) -- plaintext(%u B), Xi, ivec, retval of all %d slots "
         "vs %s at %d sizes\n", fails?"FAIL":"PASS", fails, MAXBYTES, NV, NAME[0], NG);
  return fails;
}

static double best_ns[NS][8];
static uint64_t rs;
static inline uint64_t xr(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }

int main(int argc, char **argv){
  int reps = (argc > 1) ? atoi(argv[1]) : 60;
  int tag  = (argc > 2) ? atoi(argv[2]) : 0;

  uint8_t k[32], zero[16] = {0}, H[16];
  for (int i = 0; i < 32; i++) k[i] = rb();
  aes_hw_set_encrypt_key(k, 256, &key);
  aes_hw_encrypt(zero, H, &key);
  uint64_t Hq[2]; memcpy(Hq, H, 16);
  gcm_init_v8(Htable, Hq);
  for (unsigned i = 0; i < MAXBYTES; i++) in_ct[i] = rb();

  if (correctness_gate() != 0){ printf("STOP: gate failed, no timings\n"); return 1; }

  double ghz_pre = clock_ghz();
  for (int si = 0; si < NS; si++) for (int v = 0; v < NV; v++) best_ns[si][v] = 1e30;

  for (int w = 0; w < 2; w++)
    for (int si = 0; si < NS; si++)
      for (int v = 0; v < NV; v++){
        reset_state();
        for (unsigned i = 0; i < BATCH[si]; i++)
          F[v](in_ct, (size_t)SZ[si]*8u, out, Xi, ivec, &key, Htable);
      }

  rs = 0x9E3779B97F4A7C15ull ^ ((uint64_t)tag * 0x100000001B3ull);
  if (!rs) rs = 1;
  int ord[8];
  for (int r = 0; r < reps; r++){
    for (int si = 0; si < NS; si++){
      for (int i = 0; i < NV; i++) ord[i] = i;
      for (int i = NV - 1; i > 0; i--){          /* fresh random permutation */
        int j = (int)(xr() % (uint64_t)(i + 1));
        int t = ord[i]; ord[i] = ord[j]; ord[j] = t;
      }
      for (int j = 0; j < NV; j++){
        int v = ord[j];
        unsigned n = BATCH[si];
        size_t bl = (size_t)SZ[si] * 8u;
        reset_state();
        uint64_t t0 = ns();
        for (unsigned i = 0; i < n; i++) F[v](in_ct, bl, out, Xi, ivec, &key, Htable);
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
