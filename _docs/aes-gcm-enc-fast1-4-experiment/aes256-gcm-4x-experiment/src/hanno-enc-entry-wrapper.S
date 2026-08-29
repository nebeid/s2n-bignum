// Shared entry frame for the AES-256-GCM 1--3-block vector short path and
// Hanno Becker's unchanged scalar-counter late-tag large path.

#include <openssl/asm_base.h>
#include <openssl/arm_arch.h>

#if !defined(OPENSSL_NO_ASM) && defined(__AARCH64EL__) && defined(__ELF__)
.arch armv8-a+crypto
.text
.globl aes_gcm_enc_kernel_entry_256
.hidden aes_gcm_enc_kernel_entry_256
.type aes_gcm_enc_kernel_entry_256,%function
.globl aes_gcm_enc_shared_restore_256
.hidden aes_gcm_enc_shared_restore_256

#define SHARED_STACK_SIZE (6*16 + 4*16 + 4*16)

.align 4
aes_gcm_enc_kernel_entry_256:
        AARCH64_VALID_CALL_TARGET
        sub sp, sp, #SHARED_STACK_SIZE
        stp x19, x20, [sp, #(16*0)]
        stp x21, x22, [sp, #(16*1)]
        stp x23, x24, [sp, #(16*2)]
        stp x25, x26, [sp, #(16*3)]
        stp x27, x28, [sp, #(16*4)]
        stp x29, x30, [sp, #(16*5)]
        stp  d8,  d9, [sp, #(6*16 + 16*0)]
        stp d10, d11, [sp, #(6*16 + 16*1)]
        stp d12, d13, [sp, #(6*16 + 16*2)]
        stp d14, d15, [sp, #(6*16 + 16*3)]
        lsr x15, x1, #3
        ldr q18, [x5, #(0*16)]
        ldr q19, [x5, #(1*16)]
        ldr q20, [x5, #(2*16)]
        ldr q21, [x5, #(3*16)]
        ldr q22, [x5, #(4*16)]
        ldr q23, [x5, #(5*16)]
        ldr q24, [x5, #(6*16)]
        ldr q25, [x5, #(7*16)]
        ldr q26, [x5, #(8*16)]
        ldr q27, [x5, #(9*16)]
        ldr q28, [x5, #(10*16)]
        ldr q15, [x5, #(11*16)]
        ldr q16, [x5, #(12*16)]
        ldr q17, [x5, #(13*16)]
        movi v7.8b, #0xc2
        shl d7, d7, #56
        cmp x1, #384
        b.ls aes_gcm_enc_short_body_256
        b aes_gcm_enc_large_body_256

aes_gcm_enc_shared_restore_256:
        ldp  d8,  d9, [sp, #(6*16 + 16*0)]
        ldp d10, d11, [sp, #(6*16 + 16*1)]
        ldp d12, d13, [sp, #(6*16 + 16*2)]
        ldp d14, d15, [sp, #(6*16 + 16*3)]
        ldp x19, x20, [sp, #(16*0)]
        ldp x21, x22, [sp, #(16*1)]
        ldp x23, x24, [sp, #(16*2)]
        ldp x25, x26, [sp, #(16*3)]
        ldp x27, x28, [sp, #(16*4)]
        ldp x29, x30, [sp, #(16*5)]
        add sp, sp, #SHARED_STACK_SIZE
        ret
.size aes_gcm_enc_kernel_entry_256,.-aes_gcm_enc_kernel_entry_256

.section .note.GNU-stack,"",%progbits
#endif
