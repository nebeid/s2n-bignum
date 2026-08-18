/* bench_mix.c -- MIXED-LENGTH workload.
 *
 * The per-length benchmark (bench12.c) calls one length per pass, so the
 * dispatch compare tree is perfectly predicted and the unexecuted fused bodies
 * never compete for I-cache.  A real workload mixes lengths.  This harness
 * drives a fixed pseudorandom length sequence (identical for every variant) so
 * that
 *   - the dispatch tree mispredicts, and
 *   - the whole retained code footprint is touched,
 * which is exactly where a bigger .text is supposed to hurt.
 *
 * Mix A: nblk uniform in 1..8                       (all-small traffic)
 * Mix B: nblk uniform in 1..8, every 4th call 64    (small + 1 KB records)
 * Mix C: nblk uniform in 1..16                      (straddles the cutoff and
 *                                                    the nblk>8 path)
 * Mix D: nblk uniform in {1,2}                      (EVERY variant with C>=2
 *        handles both fused, and bodies 1 and 2 sit at the same offsets in
 *        every variant -- so D isolates DISPATCH-TREE DEPTH from footprint)
 * Mix E: nblk uniform in 1..4                       (same isolation, C>=4)
 */
#define _POSIX_C_SOURCE 199309L
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <stdlib.h>

#ifndef NV
#define NV 6
#endif
typedef size_t (*fn)(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*,
                     const void*, const void*);
#define DECL(k) extern size_t dec_s##k(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
DECL(0)
#if NV>1
DECL(1)
#endif
#if NV>2
DECL(2)
#endif
#if NV>3
DECL(3)
#endif
#if NV>4
DECL(4)
#endif
#if NV>5
DECL(5)
#endif
#if NV>6
DECL(6)
#endif
#if NV>7
DECL(7)
#endif
#if NV>8
DECL(8)
#endif
#if NV>9
DECL(9)
#endif
#if NV>10
DECL(10)
#endif
#if NV>11
DECL(11)
#endif
static fn F[NV] = { dec_s0
#if NV>1
  ,dec_s1
#endif
#if NV>2
  ,dec_s2
#endif
#if NV>3
  ,dec_s3
#endif
#if NV>4
  ,dec_s4
#endif
#if NV>5
  ,dec_s5
#endif
#if NV>6
  ,dec_s6
#endif
#if NV>7
  ,dec_s7
#endif
#if NV>8
  ,dec_s8
#endif
#if NV>9
  ,dec_s9
#endif
#if NV>10
  ,dec_s10
#endif
#if NV>11
  ,dec_s11
#endif
};
static const char *NAME[12] = {"s0","s1","s2","s3","s4","s5","s6","s7","s8","s9","s10","s11"};

#define BLK 16u
#define MAXB 300u
#define NSEQ 4096
static uint8_t in_ct[MAXB*BLK] __attribute__((aligned(64)));
static uint8_t wout[MAXB*BLK] __attribute__((aligned(64)));
typedef struct { uint64_t hi, lo; } u128;
typedef struct { uint32_t rd_key[60]; unsigned rounds; } AES_KEY;
extern int  aes_hw_set_encrypt_key(const uint8_t*, int, AES_KEY*);
extern void aes_hw_encrypt(const uint8_t*, uint8_t*, const AES_KEY*);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);
static u128 Htable[16] __attribute__((aligned(16)));
static AES_KEY key __attribute__((aligned(16)));
static uint8_t wxi[BLK] __attribute__((aligned(16)));
static uint8_t wiv[BLK] __attribute__((aligned(16)));
#define NMIX 11
static const uint32_t RAT[5] = {1u,2u,3u,4u,6u};
static uint32_t seq[NMIX][NSEQ];

static uint64_t st = 0x1234567890abcdefULL;
static uint8_t rb(void){ st^=st<<13; st^=st>>7; st^=st<<17; return (uint8_t)(st&0xff); }
static void fill(uint8_t*p,size_t n){ for(size_t i=0;i<n;i++) p[i]=rb(); }
static inline uint64_t ns(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
  return (uint64_t)t.tv_sec*1000000000ull + t.tv_nsec; }

static double run_mix(fn f, int m, int reps){
  const uint32_t *s = seq[m];
  for(int i=0;i<NSEQ;i++) f(in_ct,(size_t)s[i]*BLK*8u,wout,wxi,wiv,&key,Htable);
  uint64_t t0=ns();
  for(int r=0;r<reps;r++)
    for(int i=0;i<NSEQ;i++) f(in_ct,(size_t)s[i]*BLK*8u,wout,wxi,wiv,&key,Htable);
  uint64_t t1=ns();
  return (double)(t1-t0)/((double)reps*NSEQ);
}

int main(int argc,char**argv){
  fill(in_ct,sizeof in_ct);
  uint8_t user_key[32]; fill(user_key,sizeof user_key);
  if(aes_hw_set_encrypt_key(user_key,256,&key)!=0) return 4;
  uint8_t zero[16]={0}, H[16]; aes_hw_encrypt(zero,H,&key);
  uint64_t Hbe[2];
  for(int i=0;i<2;i++){ uint64_t w=0; for(int j=0;j<8;j++) w=(w<<8)|H[i*8+j]; Hbe[i]=w; }
  gcm_init_v8(Htable,Hbe);
  fill(wxi,BLK); fill(wiv,BLK);
  uint64_t z=0xC0FFEEULL;
  for(int i=0;i<NSEQ;i++){
    z = z*6364136223846793005ULL + 1442695040888963407ULL;
    uint32_t r8 = 1u + (uint32_t)((z>>33)%8u);
    seq[0][i]=r8;
    seq[1][i]=((i&3)==3)?64u:r8;
    z = z*6364136223846793005ULL + 1442695040888963407ULL;
    seq[2][i]=1u + (uint32_t)((z>>33)%16u);
    z = z*6364136223846793005ULL + 1442695040888963407ULL;
    seq[3][i]=1u + (uint32_t)((z>>33)%2u);
    z = z*6364136223846793005ULL + 1442695040888963407ULL;
    seq[4][i]=1u + (uint32_t)((z>>33)%4u);
    /* F: 60% nblk=8 (128 B), else uniform 1..4 */
    z = z*6364136223846793005ULL + 1442695040888963407ULL;
    seq[5][i] = ((uint32_t)((z>>33)%5u) < 3u) ? 8u
                : (1u + (uint32_t)((z>>45)%4u));
    /* R1..R6: ONLY nblk=8 (128 B) and nblk=5 (80 B), ratio RAT[j]:1 */
    for(int j=0;j<5;j++){
      z = z*6364136223846793005ULL + 1442695040888963407ULL;
      uint32_t rr = RAT[j];
      seq[6+j][i] = ((uint32_t)((z>>33)%(rr+1u)) < rr) ? 8u : 5u;
    }
  }
  for(int v=0; v<NV && v+2<argc; v++) NAME[v]=argv[v+2];
  int reps = (argc>1)? atoi(argv[1]) : 20;
  static double best[NMIX][NV];
  for(int m=0;m<NMIX;m++) for(int v=0;v<NV;v++) best[m][v]=1e18;
  for(int r=0;r<reps;r++)
    for(int m=0;m<NMIX;m++)
      for(int k=0;k<NV;k++){
        int v=(k+r)%NV;
        double t=run_mix(F[v],m,2);
        if(t<best[m][v]) best[m][v]=t;
      }
  printf("%-4s", "mix");
  for(int v=0;v<NV;v++) printf(" | %8s", NAME[v]);
  printf(" ||");
  for(int v=1;v<NV;v++) printf(" %7s%%", NAME[v]);
  printf("\n");
  const char *mn[NMIX]={"A","B","C","D","E","F","R1","R2","R3","R4","R6"};
  for(int m=0;m<NMIX;m++){
    printf("%-4s", mn[m]);
    for(int v=0;v<NV;v++) printf(" | %8.3f", best[m][v]);
    printf(" ||");
    for(int v=1;v<NV;v++) printf(" %+7.2f", 100.0*(best[m][v]-best[m][0])/best[m][0]);
    printf("\n");
  }
  return 0;
}
