#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct {
    uint64_t hi, lo;
} u128;

typedef struct {
    uint32_t rd_key[60];
    unsigned rounds;
} AES_KEY;

extern size_t aes_gcm_enc_kernel_hybrid_256(
    const uint8_t *, size_t, uint8_t *, uint8_t *, uint8_t *,
    const void *, const void *);
extern int aes_hw_set_encrypt_key(const uint8_t *, int, AES_KEY *);
extern void aes_hw_encrypt(const uint8_t *, uint8_t *, const AES_KEY *);
extern void gcm_init_v8(u128 Htable[16], const uint64_t H[2]);

int main(void) {
    static const uint8_t expected_ciphertext[16] = {
        0xce, 0xa7, 0x40, 0x3d, 0x4d, 0x60, 0x6b, 0x6e,
        0x07, 0x4e, 0xc5, 0xd3, 0xba, 0xf3, 0x9d, 0x18,
    };
    static const uint8_t expected_counter[16] = {
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3,
    };
    static const uint8_t expected_auth_state[16] = {
        0xfd, 0x6a, 0xb7, 0x58, 0x6e, 0x55, 0x6d, 0xba,
        0x06, 0xd6, 0x9c, 0xfe, 0x62, 0x23, 0xb2, 0x62,
    };
    uint8_t key_bytes[32] = {0};
    uint8_t zero[16] = {0};
    uint8_t h[16], input[16] = {0}, output[16] = {0}, xi[16] = {0};
    uint8_t ivec[16] = {
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2,
    };
    uint64_t h_be[2] = {0};
    u128 htable[16] __attribute__((aligned(16)));
    AES_KEY key __attribute__((aligned(16)));

    if (aes_hw_set_encrypt_key(key_bytes, 256, &key) || key.rounds != 14)
        return 2;
    aes_hw_encrypt(zero, h, &key);
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 8; j++)
            h_be[i] = (h_be[i] << 8) | h[i * 8 + j];
    gcm_init_v8(htable, h_be);

    size_t result = aes_gcm_enc_kernel_hybrid_256(
        input, 128, output, xi, ivec, &key, htable);
    if (result != 16 ||
        memcmp(output, expected_ciphertext, sizeof(output)) != 0 ||
        memcmp(xi, expected_auth_state, sizeof(xi)) != 0 ||
        memcmp(ivec, expected_counter, sizeof(ivec)) != 0) {
        fprintf(stderr, "AES-256-GCM one-block KAT failed\n");
        return 1;
    }

    puts("AES-256-GCM one-block KAT PASS");
    return 0;
}
