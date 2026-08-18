/* bench12.c -- bench.c from _docs/fused-small-path/, widened from 8 to 12 slots
 * so the whole truncation curve (base, A/A, C=2..8, W4 hybrid) fits in ONE
 * binary and is timed round-robin with the slot order rotated per rep.
 * Everything else (self-check, warm-up, sizes, best-of-N, reporting) is
 * unchanged from bench.c.
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
#if NV > 12
#error "NV <= 12"
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
static const char *NM[12] = { "s0","s1","s2","s3","s4","s5","s6","s7",
                              "s8","s9","s10","s11" };
static const char **NAME = NM;
static int VOIDRET[12];

#define BLK 16u
#define MAXB 300u
static uint8_t in_ct[MAXB*BLK] __attribute__((aligned(64)));
static uint8_t out[NV][MAXB*BLK] __attribute__((aligned(64)));
typedef struct { uint64_t hi, lo; } u128;
typedef struct { uint32_t rd_key[60]; unsigned rounds; } AES_KEY;
extern int  aes_hw_set_encrypt_key(const uint8_t*, int, AES_KEY*);
extern void aes_hw_encrypt(const uint8_t*, uint8_t*, const AES_KEY*);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);
static u128 Htable[16] __attribute__((aligned(16)));
static AES_KEY key __attribute__((aligned(16)));
static uint8_t xi0[BLK] __attribute__((aligned(16)));
static uint8_t iv0[BLK] __attribute__((aligned(16)));
static uint8_t xi[NV][BLK] __attribute__((aligned(16)));
static uint8_t iv[NV][BLK] __attribute__((aligned(16)));
static uint8_t wxi[BLK] __attribute__((aligned(16)));
static uint8_t wiv[BLK] __attribute__((aligned(16)));
static uint8_t wout[MAXB*BLK] __attribute__((aligned(64)));

static uint64_t st = 0x1234567890abcdefULL;
static uint8_t rb(void){ st^=st<<13; st^=st>>7; st^=st<<17; return (uint8_t)(st&0xff); }
static void fill(uint8_t*p,size_t n){ for(size_t i=0;i<n;i++) p[i]=rb(); }
static inline uint64_t ns(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
  return (uint64_t)t.tv_sec*1000000000ull + t.tv_nsec; }

static double one(fn f, size_t nblk, int iters){
  size_t bl = (size_t)nblk*BLK*8u;
  for(int i=0;i<200;i++) f(in_ct,bl,wout,wxi,wiv,&key,Htable);
  uint64_t t0=ns();
  for(int i=0;i<iters;i++) f(in_ct,bl,wout,wxi,wiv,&key,Htable);
  uint64_t t1=ns();
  return (double)(t1-t0)/iters;
}

static int selfcheck(void){
  int bad=0; static size_t rv[NV]; int nsz=0;
  for(size_t nb=1; nb<=256; nb++){
    size_t bl=nb*BLK*8u; nsz++;
    for(int v=0;v<NV;v++){
      memcpy(xi[v],xi0,BLK); memcpy(iv[v],iv0,BLK);
      memset(out[v],0xA5,nb*BLK+64);
      rv[v]=F[v](in_ct,bl,out[v],xi[v],iv[v],&key,Htable);
    }
    for(int v=1;v<NV;v++){
      int bo=memcmp(out[v],out[0],nb*BLK)!=0;
      int bx=memcmp(xi[v],xi[0],BLK)!=0;
      int bi=memcmp(iv[v],iv[0],BLK)!=0;
      int br = VOIDRET[v]? 0 : (rv[v]!=rv[0]||rv[v]!=nb*BLK);
      if(bo||bx||bi||br){
        printf("SELFCHECK FAIL nblk=%zu variant %s: out=%d xi=%d ivec=%d ret=%zu(want %zu)\n",
               nb, NAME[v], bo,bx,bi, rv[v], nb*BLK);
        bad=1;
      }
    }
    if(memcmp(out[0],in_ct,nb*BLK)==0){ printf("DEGENERATE out==in at nblk=%zu\n",nb); bad=1; }
  }
  if(!bad) printf("SELFCHECK OK (%d whole-block lengths 1..256 blk x %d variants; out/Xi/ivec/ret byte-identical)\n", nsz, NV);
  return bad;
}

int main(int argc,char**argv){
  fill(in_ct,sizeof in_ct);
  uint8_t user_key[32]; fill(user_key,sizeof user_key);
  if(aes_hw_set_encrypt_key(user_key,256,&key)!=0 || key.rounds!=14){
    printf("FATAL: aes_hw_set_encrypt_key failed\n"); return 4; }
  uint8_t zero[16]={0}, H[16]; aes_hw_encrypt(zero,H,&key);
  uint64_t Hbe[2];
  for(int i=0;i<2;i++){ uint64_t w=0; for(int j=0;j<8;j++) w=(w<<8)|H[i*8+j]; Hbe[i]=w; }
  gcm_init_v8(Htable,Hbe);
  fill(xi0,sizeof xi0); fill(iv0,sizeof iv0);
  memcpy(wxi,xi0,BLK); memcpy(wiv,iv0,BLK);
  for(int v=0; v<NV && v+2<argc; v++){ NAME[v]=argv[v+2];
    if(strstr(argv[v+2],"awslcfb")) VOIDRET[v]=1; }
  int sc = selfcheck();
  if(sc && !getenv("ALLOW_MISMATCH")) return 2;
  if(getenv("SELFCHECK_ONLY")) return sc?3:0;

  int reps = (argc>1)? atoi(argv[1]) : 120;
  if(reps>512) reps=512;
  static const size_t sizes[] = {1,2,3,4,5,6,7,8,16,32,64,256};
  const int NS = (int)(sizeof(sizes)/sizeof(sizes[0]));
  double best[NV], med[NV]; static double all[NV][512];

  printf("%-6s %-5s", "bytes","blks");
  for(int v=0;v<NV;v++) printf(" | %8s", NAME[v]);
  printf(" ||");
  for(int v=1;v<NV;v++) printf(" %7s%%", NAME[v]);
  printf("\n");

  for(int si=0; si<NS; si++){
    size_t nb=sizes[si];
    long long budget = 200000;
    int iters = (int)(budget/(nb*2.5+12));
    if(iters<2000) iters=2000; if(iters>40000) iters=40000;
    for(int r=0;r<reps;r++){
      for(int k=0;k<NV;k++){
        int v = (k + r) % NV;
        all[v][r] = one(F[v], nb, iters);
      }
    }
    for(int v=0;v<NV;v++){
      for(int i=0;i<reps;i++) for(int j=i+1;j<reps;j++)
        if(all[v][j]<all[v][i]){ double t=all[v][i]; all[v][i]=all[v][j]; all[v][j]=t; }
      best[v]=all[v][0]; med[v]=all[v][reps/2];
    }
    printf("%-6zu %-5zu", nb*BLK, nb);
    for(int v=0;v<NV;v++) printf(" | %8.3f", best[v]);
    printf(" ||");
    for(int v=1;v<NV;v++) printf(" %+7.2f", 100.0*(best[v]-best[0])/best[0]);
    printf("\n");
    printf("       med  ");
    for(int v=0;v<NV;v++) printf(" | %8.3f", med[v]);
    printf("\n");
    fflush(stdout);
  }
  return 0;
}
