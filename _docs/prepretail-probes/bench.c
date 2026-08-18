/* Multi-variant interleaved benchmark for aesv8_gcm_8x_dec_256_wb variants.
 * Round-robin, order rotated per rep, best-of-N, correctness self-check first.
 * Slots: 0=base 1=base(AA floor) 2=expA 3=prep 4=both
 */
#define _POSIX_C_SOURCE 199309L
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <stdlib.h>

typedef size_t (*fn)(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*,
                     const void*, const void*);

extern size_t dec_s0(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s1(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s2(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s3(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);
extern size_t dec_s4(const uint8_t*, size_t, uint8_t*, uint8_t*, uint8_t*, const void*, const void*);

#define NV 5
static fn F[NV] = { dec_s0, dec_s1, dec_s2, dec_s3, dec_s4 };
static const char *NAME[NV] = { "base", "AA", "expA", "prep", "both" };

#define BLK 16u
#define MAXB 300u
static uint8_t in_ct[MAXB*BLK] __attribute__((aligned(64)));
static uint8_t out[NV][MAXB*BLK] __attribute__((aligned(64)));
static uint8_t Htable[256] __attribute__((aligned(16)));
static uint8_t key[256] __attribute__((aligned(16)));
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
  for(int i=0;i<200;i++) f(in_ct,bl,wout,wxi,wiv,key,Htable);
  uint64_t t0=ns();
  for(int i=0;i<iters;i++) f(in_ct,bl,wout,wxi,wiv,key,Htable);
  uint64_t t1=ns();
  return (double)(t1-t0)/iters;
}

/* returns 0 if all variants agree with slot 0 */
static int selfcheck(void){
  size_t sizes[] = {8,9,10,11,12,13,14,15,16,17,23,24,31,32,33,64,255,256};
  int bad=0;
  for(size_t si=0; si<sizeof(sizes)/sizeof(sizes[0]); si++){
    size_t nb=sizes[si]; size_t bl=nb*BLK*8u;
    for(int v=0;v<NV;v++){
      memcpy(xi[v],xi0,BLK); memcpy(iv[v],iv0,BLK);
      memset(out[v],0xA5,sizeof out[v]);
      F[v](in_ct,bl,out[v],xi[v],iv[v],key,Htable);
    }
    for(int v=1;v<NV;v++){
      if(memcmp(out[v],out[0],nb*BLK) || memcmp(xi[v],xi[0],BLK) || memcmp(iv[v],iv[0],BLK)){
        printf("SELFCHECK FAIL nblk=%zu variant %s: out=%d xi=%d ivec=%d\n", nb, NAME[v],
               memcmp(out[v],out[0],nb*BLK)!=0, memcmp(xi[v],xi[0],BLK)!=0,
               memcmp(iv[v],iv[0],BLK)!=0);
        bad=1;
      }
    }
  }
  if(!bad) printf("SELFCHECK OK (18 sizes x %d variants, out/Xi/ivec byte-identical)\n", NV);
  return bad;
}

int main(int argc,char**argv){
  fill(in_ct,sizeof in_ct); fill(Htable,sizeof Htable); fill(key,sizeof key);
  fill(xi0,sizeof xi0); fill(iv0,sizeof iv0);
  memcpy(wxi,xi0,BLK); memcpy(wiv,iv0,BLK);
  if(selfcheck() && !getenv("ALLOW_MISMATCH")) return 2;

  int reps = (argc>1)? atoi(argv[1]) : 120;
  size_t sizes[] = {8,16,32,64,256};
  double best[NV], med[NV], all[NV][512];

  printf("%-6s %-5s", "bytes","blks");
  for(int v=0;v<NV;v++) printf(" | %8s", NAME[v]);
  printf(" ||");
  for(int v=1;v<NV;v++) printf(" %7s%%", NAME[v]);
  printf("\n");

  for(size_t si=0; si<5; si++){
    size_t nb=sizes[si];
    long long budget = 200000;              /* ns per pass target */
    int iters = (int)(budget/(nb*2.5));
    if(iters<2000) iters=2000; if(iters>40000) iters=40000;
    for(int r=0;r<reps;r++){
      for(int k=0;k<NV;k++){
        int v = (k + r) % NV;               /* rotate order per rep */
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
    fflush(stdout);
    printf("       med  ");
    for(int v=0;v<NV;v++) printf(" | %8.3f", med[v]);
    printf("\n");
    fflush(stdout);
  }
  return 0;
}
