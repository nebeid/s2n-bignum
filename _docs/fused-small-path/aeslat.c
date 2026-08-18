/* AES round-chain latency: serial aese+aesmc pairs, 1 stream vs 8 streams. */
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdint.h>
#include <time.h>
static inline uint64_t ns(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);
 return (uint64_t)t.tv_sec*1000000000ull+t.tv_nsec;}
#define R14 "aese v0.16b,v20.16b\naesmc v0.16b,v0.16b\n"
#define X8(s) s s s s s s s s
#define X16(s) X8(s) X8(s)
int main(void){
  double gh=0; /* clock filled by caller */
  /* 1 stream: 128 dependent fused pairs */
  uint64_t t0=ns();
  for(int i=0;i<200000;i++) __asm__ volatile(X16(X8(R14))::: "v0");
  uint64_t t1=ns();
  double per1=(double)(t1-t0)/200000.0/128.0;
  /* 8 streams interleaved: 128 pairs total (16 per stream) */
  t0=ns();
  for(int i=0;i<200000;i++) __asm__ volatile(X16(
    "aese v0.16b,v20.16b\naesmc v0.16b,v0.16b\n"
    "aese v1.16b,v20.16b\naesmc v1.16b,v1.16b\n"
    "aese v2.16b,v20.16b\naesmc v2.16b,v2.16b\n"
    "aese v3.16b,v20.16b\naesmc v3.16b,v3.16b\n"
    "aese v4.16b,v20.16b\naesmc v4.16b,v4.16b\n"
    "aese v5.16b,v20.16b\naesmc v5.16b,v5.16b\n"
    "aese v6.16b,v20.16b\naesmc v6.16b,v6.16b\n"
    "aese v7.16b,v20.16b\naesmc v7.16b,v7.16b\n")
    ::: "v0","v1","v2","v3","v4","v5","v6","v7");
  t1=ns();
  double per8=(double)(t1-t0)/200000.0/128.0;
  printf("ns_per_pair_1stream %.4f  ns_per_pair_8streams %.4f\n", per1, per8);
  (void)gh; return 0;
}
