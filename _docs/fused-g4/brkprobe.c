/* brkprobe.c -- two probes for the g4 single-entry region.
 *
 *  1. LIVENESS.  Linked against a variant carrying `brk #0` at the region's one
 *     entry label, this program must DIE for nblk = 1,2,3,4 (the group is
 *     entered) and must SURVIVE for nblk = 5,6,7,8 and nblk > 8 (they fall back
 *     to the baseline path).  The caller reads the exit status.
 *
 *  2. MEMORY SAFETY of the clamped lane addresses.  With `guard` / `guardlo`
 *     the ciphertext and plaintext buffers are placed flush against a PROT_NONE
 *     page, above (guard) or below (guardlo) the buffer, so ANY access outside
 *     [buf, buf+16*nblk) faults.  A g4 lane that failed to clamp -- the
 *     characteristic bug: lane j reading block j-(4-nblk) < 0, or four blocks
 *     of stores when one was asked for -- is a hard SIGSEGV here.
 *
 * Build: gcc -O2 -o brkprobe brkprobe.c obj/b<slot>.o obj/awslchelp.o
 */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>

extern size_t dec_s0(const uint8_t *, size_t, uint8_t *, uint8_t *, uint8_t *,
                     const void *, const void *);
typedef struct { uint64_t hi, lo; } u128;
typedef struct { uint32_t rd_key[60]; unsigned rounds; } AES_KEY;
extern int aes_hw_set_encrypt_key(const uint8_t *, int, AES_KEY *);
extern void aes_hw_encrypt(const uint8_t *, uint8_t *, const AES_KEY *);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

static u128 Htable[16] __attribute__((aligned(16)));
static AES_KEY key __attribute__((aligned(16)));
static uint8_t xi[16] __attribute__((aligned(16)));
static uint8_t iv[16] __attribute__((aligned(16)));
static uint8_t sin[300 * 16] __attribute__((aligned(64)));
static uint8_t sout[300 * 16] __attribute__((aligned(64)));

/* n bytes in a RW page flanked by two PROT_NONE pages; flush against the upper
 * guard (lo == 0) or against the lower guard (lo == 1). */
static uint8_t *guardbuf(size_t n, int lo)
{
  long ps = sysconf(_SC_PAGESIZE);
  uint8_t *p = mmap(NULL, 3 * (size_t)ps, PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (p == MAP_FAILED) { perror("mmap"); exit(9); }
  if (mprotect(p, ps, PROT_NONE) || mprotect(p + 2 * ps, ps, PROT_NONE)) {
    perror("mprotect"); exit(9);
  }
  return lo ? p + ps : p + 2 * (size_t)ps - n;
}

int main(int argc, char **argv)
{
  size_t nb = (argc > 1) ? strtoul(argv[1], 0, 0) : 1;
  const char *mode = (argc > 2) ? argv[2] : "plain";
  uint8_t uk[32];
  for (int i = 0; i < 32; i++) uk[i] = (uint8_t)(i * 7 + 1);
  if (aes_hw_set_encrypt_key(uk, 256, &key) != 0 || key.rounds != 14) return 8;
  uint8_t z[16] = { 0 }, H[16];
  aes_hw_encrypt(z, H, &key);
  uint64_t Hbe[2];
  for (int i = 0; i < 2; i++) {
    uint64_t w = 0;
    for (int j = 0; j < 8; j++) w = (w << 8) | H[i * 8 + j];
    Hbe[i] = w;
  }
  gcm_init_v8(Htable, Hbe);
  for (int i = 0; i < 16; i++) { xi[i] = (uint8_t)i; iv[i] = (uint8_t)(0xff - i); }

  size_t n = nb * 16;
  uint8_t *in = sin, *out = sout;
  if (!strcmp(mode, "guard"))   { in = guardbuf(n, 0); out = guardbuf(n, 0); }
  if (!strcmp(mode, "guardlo")) { in = guardbuf(n, 1); out = guardbuf(n, 1); }
  for (size_t i = 0; i < n; i++) in[i] = (uint8_t)(i * 13 + 5);
  size_t r = dec_s0(in, n * 8, out, xi, iv, &key, Htable);
  printf("SURVIVED nblk=%zu ret=%zu mode=%s\n", nb, r, mode);
  return (r == n) ? 0 : 7;
}
