/* Interleaved raw-kernel benchmark for AES-256-GCM assembly variants. */
#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef NV
#define NV 8
#endif

typedef size_t (*kernel_fn)(const uint8_t *, size_t, uint8_t *, uint8_t *,
                            uint8_t *, const void *, const void *);
#define DECL(n) extern size_t kernel##n(const uint8_t *, size_t, uint8_t *, \
    uint8_t *, uint8_t *, const void *, const void *)
DECL(0);
#if NV > 1
DECL(1);
#endif
#if NV > 2
DECL(2);
#endif
#if NV > 3
DECL(3);
#endif
#if NV > 4
DECL(4);
#endif
#if NV > 5
DECL(5);
#endif
#if NV > 6
DECL(6);
#endif
#if NV > 7
DECL(7);
#endif

static kernel_fn kernels[NV] = {
    kernel0,
#if NV > 1
    kernel1,
#endif
#if NV > 2
    kernel2,
#endif
#if NV > 3
    kernel3,
#endif
#if NV > 4
    kernel4,
#endif
#if NV > 5
    kernel5,
#endif
#if NV > 6
    kernel6,
#endif
#if NV > 7
    kernel7,
#endif
};

typedef struct { uint64_t hi, lo; } u128;
typedef struct { uint32_t rd_key[60]; unsigned rounds; } AES_KEY;
extern int aes_hw_set_encrypt_key(const uint8_t *, int, AES_KEY *);
extern void aes_hw_encrypt(const uint8_t *, uint8_t *, const AES_KEY *);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

#define BLOCK 16u
#define MAX_CHECK_BLOCKS 256u
#define MAX_BENCH_BLOCKS 2048u
#define MAX_REPS 512
static uint8_t input[MAX_BENCH_BLOCKS * BLOCK + 64]
    __attribute__((aligned(64)));
static uint8_t output[NV][MAX_BENCH_BLOCKS * BLOCK + 64]
    __attribute__((aligned(64)));
static uint8_t work_output[NV][MAX_BENCH_BLOCKS * BLOCK + 64]
    __attribute__((aligned(64)));
static uint8_t xi0[BLOCK], iv0[BLOCK];
static uint8_t xi[NV][BLOCK], iv[NV][BLOCK];
static uint8_t work_xi[NV][BLOCK], work_iv[NV][BLOCK];
static u128 htable[16] __attribute__((aligned(16)));
static AES_KEY key __attribute__((aligned(16)));
static const char *names[NV];
static uint64_t rng_state = UINT64_C(0x1234567890abcdef);

static uint8_t random_byte(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return (uint8_t)rng_state;
}

static void fill(uint8_t *p, size_t n) {
    for (size_t i = 0; i < n; i++) p[i] = random_byte();
}

static uint64_t now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}

static double measure(int variant, size_t blocks, int iterations) {
    kernel_fn f = kernels[variant];
    const size_t bits = blocks * BLOCK * 8u;
    for (int i = 0; i < 20; i++)
        f(input, bits, work_output[variant], work_xi[variant],
          work_iv[variant], &key, htable);
    const uint64_t start = now_ns();
    for (int i = 0; i < iterations; i++)
        f(input, bits, work_output[variant], work_xi[variant],
          work_iv[variant], &key, htable);
    return (double)(now_ns() - start) / iterations;
}

static int selfcheck(void) {
    int failed = 0;
    for (size_t blocks = 1; blocks <= MAX_CHECK_BLOCKS; blocks++) {
        size_t result[NV];
        for (int v = 0; v < NV; v++) {
            memcpy(xi[v], xi0, BLOCK);
            memcpy(iv[v], iv0, BLOCK);
            memset(output[v], 0xa5, sizeof(output[v]));
            result[v] = kernels[v](input, blocks * BLOCK * 8u, output[v],
                                    xi[v], iv[v], &key, htable);
        }
        for (int v = 1; v < NV; v++) {
            if (memcmp(output[v], output[0], blocks * BLOCK) ||
                memcmp(xi[v], xi[0], BLOCK) ||
                memcmp(iv[v], iv[0], BLOCK) ||
                result[v] != result[0] ||
                result[v] != blocks * BLOCK) {
                fprintf(stderr, "SELFCHECK FAIL blocks=%zu variant=%s\n",
                        blocks, names[v]);
                failed = 1;
            }
        }
    }
    if (!failed)
        printf("# SELFCHECK OK: 1..256 blocks, %d variants\n", NV);
    return failed;
}

static int compare_double(const void *a, const void *b) {
    const double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc != NV + 3) {
        fprintf(stderr, "usage: %s REPS PROCESS LABEL...\n", argv[0]);
        return 64;
    }
    const int reps = atoi(argv[1]);
    const int process = atoi(argv[2]);
    if (reps < 3 || reps > MAX_REPS) return 64;
    for (int v = 0; v < NV; v++) names[v] = argv[v + 3];

    fill(input, sizeof(input));
    uint8_t user_key[32], zero[16] = {0}, h[16];
    fill(user_key, sizeof(user_key));
    if (aes_hw_set_encrypt_key(user_key, 256, &key) || key.rounds != 14)
        return 4;
    aes_hw_encrypt(zero, h, &key);
    uint64_t h_be[2];
    for (int i = 0; i < 2; i++) {
        h_be[i] = 0;
        for (int j = 0; j < 8; j++) h_be[i] = (h_be[i] << 8) | h[i * 8 + j];
    }
    gcm_init_v8(htable, h_be);
    fill(xi0, sizeof(xi0));
    fill(iv0, sizeof(iv0));
    for (int v = 0; v < NV; v++) {
        memcpy(work_xi[v], xi0, BLOCK);
        memcpy(work_iv[v], iv0, BLOCK);
    }
    if (selfcheck()) return 2;
    if (getenv("SELFCHECK_ONLY")) return 0;

    static const size_t blocks[] = {
        1, 2, 3, 4, 5, 6, 7, 8,
    };
    static double samples[NV][MAX_REPS];
    for (size_t s = 0; s < sizeof(blocks) / sizeof(blocks[0]); s++) {
        const size_t n = blocks[s];
        int iterations = (int)(2000000.0 / n);
        if (iterations < 100) iterations = 100;
        if (iterations > 20000) iterations = 20000;
        for (int r = 0; r < reps; r++) {
            for (int k = 0; k < NV; k++) {
                const int v = (k + r + process) % NV;
                samples[v][r] = measure(v, n, iterations);
            }
        }
        for (int v = 0; v < NV; v++) {
            qsort(samples[v], reps, sizeof(double), compare_double);
            printf("RES,%d,%zu,%s,%.3f,%.3f\n", process, n * BLOCK,
                   names[v], samples[v][0], samples[v][reps / 2]);
        }
        fflush(stdout);
    }
    return 0;
}
