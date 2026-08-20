/* Clock estimate via a long dependent-add chain (1 add/cycle). */
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdint.h>
#include <time.h>
static inline uint64_t ns(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
  return (uint64_t)t.tv_sec*1000000000ull+t.tv_nsec; }
int main(void){
  double bestg=0;
  for(int r=0;r<5;r++){
    uint64_t n = 400000000ull;
    uint64_t t0=ns();
    __asm__ volatile(
      "mov x9, %0\n"
      "mov x10, #0\n"
      "1:\n"
      "add x10, x10, #1\n add x10, x10, #1\n add x10, x10, #1\n add x10, x10, #1\n"
      "subs x9, x9, #4\n"
      "b.ne 1b\n"
      :: "r"(n) : "x9","x10","cc");
    uint64_t t1=ns();
    double g = (double)n/(double)(t1-t0);   /* GHz, 1 add/cyc */
    if(g>bestg) bestg=g;
  }
  printf("clock_GHz %.4f\n", bestg);
  return 0;
}
