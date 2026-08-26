/* Co-linked AES-256-GCM encrypt kernel benchmark.
 * All variants use the same process, data, real key schedule, and H table.
 */
#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef NV
#define NV 7
#endif

typedef size_t (*kernel_fn)(const uint8_t *, size_t, uint8_t *, uint8_t *,
                            uint8_t *, const void *, const void *);
#define DECL(n) extern size_t enc_s##n(const uint8_t *, size_t, uint8_t *, \
    uint8_t *, uint8_t *, const void *, const void *)
DECL(0); DECL(1); DECL(2); DECL(3); DECL(4); DECL(5); DECL(6);

static kernel_fn kernels[] = {
    enc_s0, enc_s1, enc_s2, enc_s3, enc_s4, enc_s5, enc_s6
};
static const char *names[] = {
    "base", "baseAA", "compact", "compactAA", "full", "awslc8x", "awslc4x"
};
static int void_return[NV];

typedef struct { uint64_t hi, lo; } u128;
typedef struct { uint32_t rd_key[60]; unsigned rounds; } AES_KEY;
extern int aes_hw_set_encrypt_key(const uint8_t *, int, AES_KEY *);
extern void aes_hw_encrypt(const uint8_t *, uint8_t *, const AES_KEY *);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

#define BLOCK 16u
#define MAX_BLOCKS 256u
#define MAX_REPS 512
static uint8_t input[MAX_BLOCKS * BLOCK] __attribute__((aligned(64)));
static uint8_t output[NV][MAX_BLOCKS * BLOCK] __attribute__((aligned(64)));
static uint8_t scratch[MAX_BLOCKS * BLOCK] __attribute__((aligned(64)));
static uint8_t xi0[BLOCK], iv0[BLOCK];
static uint8_t xi[NV][BLOCK], iv[NV][BLOCK], scratch_xi[BLOCK], scratch_iv[BLOCK];
static u128 htable[16] __attribute__((aligned(16)));
static AES_KEY key __attribute__((aligned(16)));
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

static double measure(kernel_fn f, size_t blocks, int iterations) {
    const size_t bits = blocks * BLOCK * 8u;
    for (int i = 0; i < 200; i++)
        f(input, bits, scratch, scratch_xi, scratch_iv, &key, htable);
    const uint64_t start = now_ns();
    for (int i = 0; i < iterations; i++)
        f(input, bits, scratch, scratch_xi, scratch_iv, &key, htable);
    return (double)(now_ns() - start) / iterations;
}

static int selfcheck(void) {
    int failed = 0;
    for (size_t blocks = 1; blocks <= MAX_BLOCKS; blocks++) {
        size_t result[NV];
        for (int v = 0; v < NV; v++) {
            memcpy(xi[v], xi0, BLOCK);
            memcpy(iv[v], iv0, BLOCK);
            memset(output[v], 0xa5, blocks * BLOCK);
            result[v] = kernels[v](input, blocks * BLOCK * 8u, output[v],
                                    xi[v], iv[v], &key, htable);
        }
        for (int v = 1; v < NV; v++) {
            const int mismatch =
                memcmp(output[v], output[0], blocks * BLOCK) ||
                memcmp(xi[v], xi[0], BLOCK) ||
                memcmp(iv[v], iv[0], BLOCK) ||
                (!void_return[v] &&
                 (result[v] != result[0] || result[v] != blocks * BLOCK));
            if (mismatch) {
                fprintf(stderr, "SELFCHECK FAIL blocks=%zu variant=%s\n",
                        blocks, names[v]);
                failed = 1;
            }
        }
    }
    if (!failed)
        printf("SELFCHECK OK: 1..256 blocks, out/Xi/ivec/return agree\n");
    return failed;
}

static int compare_double(const void *a, const void *b) {
    const double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
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
    memcpy(scratch_xi, xi0, BLOCK);
    memcpy(scratch_iv, iv0, BLOCK);
    void_return[6] = 1;
    if (selfcheck()) return 2;
    if (getenv("SELFCHECK_ONLY")) return 0;

    int reps = argc > 1 ? atoi(argv[1]) : 120;
    if (reps < 3) reps = 3;
    if (reps > MAX_REPS) reps = MAX_REPS;
    static const size_t blocks[] = {1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 32, 64, 256};
    double samples[NV][MAX_REPS];

    printf("bytes");
    for (int v = 0; v < NV; v++) printf(",%s_best,%s_median", names[v], names[v]);
    putchar('\n');
    for (size_t s = 0; s < sizeof(blocks) / sizeof(blocks[0]); s++) {
        const size_t n = blocks[s];
        int iterations = (int)(200000.0 / (n * 2.5 + 12));
        if (iterations < 2000) iterations = 2000;
        if (iterations > 40000) iterations = 40000;
        for (int r = 0; r < reps; r++)
            for (int k = 0; k < NV; k++) {
                const int v = (k + r) % NV;
                samples[v][r] = measure(kernels[v], n, iterations);
            }
        printf("%zu", n * BLOCK);
        for (int v = 0; v < NV; v++) {
            qsort(samples[v], reps, sizeof(double), compare_double);
            printf(",%.3f,%.3f", samples[v][0], samples[v][reps / 2]);
        }
        putchar('\n');
        fflush(stdout);
    }
    return 0;
}
