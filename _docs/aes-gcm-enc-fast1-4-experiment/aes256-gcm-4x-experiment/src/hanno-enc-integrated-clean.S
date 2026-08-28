// Copyright (c) 2022, ARM Inc.
// Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

// Author: Hanno Becker <hannobecker@posteo.de>
//
// This file was derived from the assembly generated from aesv8-gcm-armv8.pl,
// written by Fangming Fang <fangming.fang@arm.com> for the OpenSSL project,
// and derived from https://github.com/ARM-software/AArch64cryptolib, original
// author Samuel Lee <Samuel.Lee@arm.com>.
//
// The code below is a 'clean' AArch64 implementation of AES-GCM emphasizing
// the logic of the computation. It is meant as the input to manual audits /
// formal verification, as well as automated micro-optimization such as done
// by the SLOTHY superoptimizer (https://github.com/slothy-optimizer/slothy).

#if !defined(__has_feature)
#define __has_feature(x) 0
#endif
#if __has_feature(memory_sanitizer) && !defined(OPENSSL_NO_ASM)
#define OPENSSL_NO_ASM
#endif

#include <openssl/asm_base.h>

#if !defined(OPENSSL_NO_ASM) && defined(__AARCH64EL__)
#if defined(__ELF__)
#include <openssl/boringssl_prefix_symbols_asm.h>
#include <openssl/arm_arch.h>
.arch   armv8-a+crypto
.text
.globl  aes_gcm_enc_kernel_slothy_base_256
.hidden aes_gcm_enc_kernel_slothy_base_256
.type   aes_gcm_enc_kernel_slothy_base_256,%function
#elif defined(__APPLE__)
#if defined(BORINGSSL_PREFIX)
#include <boringssl_prefix_symbols_asm.h>
#endif
#include <openssl/arm_arch.h>
.text
.globl	_aes_gcm_enc_kernel_slothy_base_256
.private_extern	_aes_gcm_enc_kernel_slothy_base_256
#else
#error Unknown configuration
#endif

#if __ARM_MAX_ARCH__ >= 8

// Arguments
input    .req x0
len_bits .req x1
output   .req x2
tag_ptr  .req x3
ivec     .req x4
key      .req x5
Htable   .req x6

byte_len .req x15

constant_temp .req x25

count           .req x1
full_blocks     .req x7
remainder       .req x16
unroll          .req x10

ctr_tmp   .req x14
ctr_tmp_w .req w14

ivec_0_63    .req x11
ivec_64_96   .req x12
ivec_64_96_w .req w12

ctr      .req w13
ctr_x    .req x13

aes_st    .req v0
aes_st_q  .req q0
aes_st_d  .req d0

res       .req v0
res_q     .req q0

ghash_hi    .req v9
ghash_lo    .req v8
ghash_mid   .req v10
ghash_mid_d .req d10

ghash_tmp   .req v11
ghash_tmp_d .req d11

ghash_mod   .req v7
ghash_mod_d .req d7

modulo_tmp0 .req v0
modulo_tmp1 .req v1

Ht1q   .req q12
Ht2q   .req q13
Ht12q  .req q14

Ht1    .req v12
Ht2    .req v13
Ht12   .req v14

Ht3q   .req q12
Ht4q   .req q13
Ht34q  .req q14

Ht3    .req v12
Ht4    .req v13
Ht34   .req v14

rk0q   .req q18
rk1q   .req q19
rk2q   .req q20
rk3q   .req q21
rk4q   .req q22
rk5q   .req q23
rk6q   .req q24
rk7q   .req q25
rk8q   .req q26
rk9q   .req q27
rk10q  .req q28

rk11q  .req q15
rk12q  .req q16
rk13q  .req q17

rk14_lo .req x20
rk14_hi .req x21

rk0    .req v18
rk1    .req v19
rk2    .req v20
rk3    .req v21
rk4    .req v22
rk5    .req v23
rk6    .req v24
rk7    .req v25
rk8    .req v26
rk9    .req v27
rk10   .req v28

rk11   .req v15
rk12   .req v16
rk13   .req v17

plain   .req v29
plain_q .req q29

plain_lo .req x22
plain_hi .req x23

tag    .req v30
tag_q  .req q30

#define UNROLL 4

#define STACK_SIZE_GPRS  (6*16)
#define STACK_SIZE_VREGS (4*16)
#define STACK_SIZE  (STACK_SIZE_GPRS + STACK_SIZE_VREGS + UNROLL*16)

#define STACK_BASE_GPRS  (0)
#define STACK_BASE_VREGS (STACK_SIZE_GPRS)
#define STACK_BASE_AES_ST (STACK_SIZE_GPRS + STACK_SIZE_VREGS)

/********************************************************************/
/*                 Generic preamble/postamble macros                */
/********************************************************************/

.macro save_vregs
        stp  d8,  d9, [sp, #(STACK_BASE_VREGS + 16*0)]
        stp d10, d11, [sp, #(STACK_BASE_VREGS + 16*1)]
        stp d12, d13, [sp, #(STACK_BASE_VREGS + 16*2)]
        stp d14, d15, [sp, #(STACK_BASE_VREGS + 16*3)]
.endm

.macro restore_vregs
        ldp  d8,  d9, [sp, #(STACK_BASE_VREGS + 16*0)]
        ldp d10, d11, [sp, #(STACK_BASE_VREGS + 16*1)]
        ldp d12, d13, [sp, #(STACK_BASE_VREGS + 16*2)]
        ldp d14, d15, [sp, #(STACK_BASE_VREGS + 16*3)]
.endm

.macro save_gprs
        stp x19, x20, [sp, #(STACK_BASE_GPRS + 16*0)]
        stp x21, x22, [sp, #(STACK_BASE_GPRS + 16*1)]
        stp x23, x24, [sp, #(STACK_BASE_GPRS + 16*2)]
        stp x25, x26, [sp, #(STACK_BASE_GPRS + 16*3)]
        stp x27, x28, [sp, #(STACK_BASE_GPRS + 16*4)]
        stp x29, x30, [sp, #(STACK_BASE_GPRS + 16*5)]
.endm

.macro restore_gprs
        ldp x19, x20, [sp, #(STACK_BASE_GPRS + 16*0)]
        ldp x21, x22, [sp, #(STACK_BASE_GPRS + 16*1)]
        ldp x23, x24, [sp, #(STACK_BASE_GPRS + 16*2)]
        ldp x25, x26, [sp, #(STACK_BASE_GPRS + 16*3)]
        ldp x27, x28, [sp, #(STACK_BASE_GPRS + 16*4)]
        ldp x29, x30, [sp, #(STACK_BASE_GPRS + 16*5)]
.endm

// Derive number of iterations of unrolled loop and single-block loop
.macro prepare_loop_counts
        mov  unroll, #UNROLL
        // Number of AES Blocks (16b each)
        lsr  full_blocks, byte_len, #4
        // Number of iterations of the unrolled loop
        udiv count, full_blocks, unroll
        // Number of iterations for the tail loop handling 1 block each
        msub remainder, count, unroll, full_blocks
.endm

/********************************************************************/
/*                       AES related macros                         */
/********************************************************************/

.macro load_iv
        ldp        ivec_0_63, ivec_64_96, [ivec]
        lsr        ctr_x, ivec_64_96, #32
        rev        ctr, ctr
        orr        ivec_64_96_w, ivec_64_96_w, ivec_64_96_w // clear top 32 bit
.endm

.macro next_ctr_init_aes aes_st, loc
        add        ctr_tmp_w, ctr, #\loc
        rev        ctr_tmp_w, ctr_tmp_w
        orr        ctr_tmp, ivec_64_96, ctr_tmp, lsl #32
        stp        ivec_0_63, ctr_tmp, [sp, #(STACK_BASE_AES_ST + \loc*16)] // @slothy:writes=stack_\loc
        ldr        \aes_st\()_q, [sp, #(STACK_BASE_AES_ST + \loc*16)]       // @slothy:reads=stack_\loc
.endm

// A single AES round
// Prevent SLOTHY from unfolding because uArchs tend to fuse AESMC+AESE
.macro aesr data, key // @slothy:no-unfold=true
        aese  \data, \key
        aesmc \data, \data
.endm

.macro aesr_0_8 data, key
        aesr \data\().16b, \key\()0.16b
        aesr \data\().16b, \key\()1.16b
        aesr \data\().16b, \key\()2.16b
        aesr \data\().16b, \key\()3.16b
        aesr \data\().16b, \key\()4.16b
        aesr \data\().16b, \key\()5.16b
        aesr \data\().16b, \key\()6.16b
        aesr \data\().16b, \key\()7.16b
        aesr \data\().16b, \key\()8.16b
.endm

.macro aesr_9_10 data, key
        aesr \data\().16b, \key\()9.16b
        aesr \data\().16b, \key\()10.16b
.endm

.macro aesr_11_12 data, key
        aesr \data\().16b, \key\()11.16b
        aesr \data\().16b, \key\()12.16b
.endm

// Destructs inA
.macro eor3 out, inA, inB, inC
        eor \inA, \inA, \inB
        eor \out, \inA, \inC
.endm

.macro aesr_final aes_st, plain, out, loc
        aese \aes_st\().16b, rk13.16b
        eor \plain\()_lo, \plain\()_lo, rk14_lo
        eor \plain\()_hi, \plain\()_hi, rk14_hi
        stp \plain\()_lo, \plain\()_hi, [sp, #(STACK_BASE_AES_ST + \loc*16)] // @slothy:writes=stack_\loc
        ldr \plain\()_q, [sp, #(STACK_BASE_AES_ST + \loc*16)]       // @slothy:reads=stack_\loc
        eor \out\().16b, \plain\().16b, \aes_st\().16b
.endm

.macro aes_full_block aes_st, input, output, loc
        next_ctr_init_aes \aes_st, \loc
        aesr_0_8 \aes_st\(), rk
        aesr_9_10 \aes_st\(), rk
        aesr_11_12 \aes_st\(), rk
        aesr_final \aes_st, \input, \output, \loc
.endm

.macro load_round_key i
        ldr rk\i\()q, [key, #((\i)*16)]
.endm

.macro load_round_key_scalar i
        ldp rk\i\()_lo, rk\i\()_hi, [key, #((\i)*16)]
.endm

.macro load_round_keys
        load_round_key 0
        load_round_key 1
        load_round_key 2
        load_round_key 3
        load_round_key 4
        load_round_key 5
        load_round_key 6
        load_round_key 7
        load_round_key 8
        load_round_key 9
        load_round_key 10
        load_round_key 11
        load_round_key 12
        load_round_key 13
        load_round_key_scalar 14
.endm

/********************************************************************/
/*       Loading of H-table (precomputed H-powers for GHASH)        */
/********************************************************************/

// This has to be synchronized with the H-table generation

.macro load_h1 dst, dst_q
        ldr \dst_q, [Htable]
.endm

.macro load_h2 dst, dst_q
        ldr \dst_q, [Htable, #32]
.endm

.macro load_h3 dst, dst_q
        ldr \dst_q, [Htable, #48]
.endm

.macro load_h4 dst, dst_q
        ldr \dst_q, [Htable, #80]
.endm

.macro load_h5 dst, dst_q
        ldr \dst_q, [Htable, #96]
.endm

.macro load_h6 dst, dst_q
        ldr \dst_q, [Htable, #128]
.endm

.macro load_h7 dst, dst_q
        ldr \dst_q, [Htable, #144]
.endm

.macro load_h8 dst, dst_q
        ldr \dst_q, [Htable, #176]
.endm

.macro load_h12 dst, dst_q
        ldr \dst_q, [Htable, #16]
.endm

.macro load_h34 dst, dst_q
        ldr \dst_q, [Htable, #64]
.endm

.macro load_h56 dst, dst_q
        ldr \dst_q, [Htable, #112]
.endm

.macro load_h78 dst, dst_q
        ldr \dst_q, [Htable, #160]
.endm

.macro load_full_htable
        load_h1  Ht1,  Ht1q
        load_h2  Ht2,  Ht2q
        load_h3  Ht3,  Ht3q
        load_h4  Ht4,  Ht4q
        load_h5  Ht5,  Ht5q
        load_h6  Ht6,  Ht6q
        load_h12 Ht12, Ht12q
        load_h34 Ht34, Ht34q
        load_h56 Ht56, Ht56q
.endm

.macro load_htable_12
        load_h1  Ht1,  Ht1q
        load_h2  Ht2,  Ht2q
        load_h12 Ht12, Ht12q
.endm

.macro load_htable_1
        load_h1  Ht1,  Ht1q
        load_h12 Ht12, Ht12q
.endm

.macro load_htable_34
        load_h3  Ht3,  Ht3q
        load_h4  Ht4,  Ht4q
        load_h34 Ht34, Ht34q
.endm

.macro load_htable_3
        load_h3  Ht3,  Ht3q
        load_h34 Ht34, Ht34q
.endm

.macro load_htable_56
        load_h5  Ht5,  Ht5q
        load_h6  Ht6,  Ht6q
        load_h56 Ht56, Ht56q
.endm

.macro load_htable_78
        load_h7  Ht7,  Ht7q
        load_h8  Ht8,  Ht8q
        load_h78 Ht78, Ht78q
.endm

/********************************************************************/
/*                    Macros for GHASH udpate                       */
/********************************************************************/

.macro ghash_init_0 input, Hk, Hk_mid
        rev64 \input\().16b, \input\().16b
        // Low product
        pmull   ghash_lo.1q, \input\().1d, \Hk\().1d
        // High product
        pmull2  ghash_hi.1q, \input\().2d, \Hk\().2d
        // Middle product
        mov     ghash_tmp_d, \input\().d[1]
        eor     ghash_tmp.8b, ghash_tmp.8b, \input\().8b
        pmull   ghash_mid.1q, ghash_tmp.1d, \Hk_mid\().1d
.endm

.macro ghash_init_1 input, Hk, Hk_mid
        rev64 \input\().16b, \input\().16b
        // Low product
        pmull   ghash_lo.1q, \input\().1d, \Hk\().1d
        // High product
        pmull2  ghash_hi.1q, \input\().2d, \Hk\().2d
        // Middle product
        ext     ghash_tmp.16b, \input\().16b, \input\().16b, #8
        eor     ghash_tmp.16b, ghash_tmp.16b, \input\().16b
        pmull2  ghash_mid.1q, ghash_tmp.2d, \Hk_mid\().2d
.endm

.macro ghash_acc_0 input, Hk, Hk_mid
        rev64   \input\().16b, \input\().16b
        // Low product
        pmull   ghash_tmp.1q, \input\().1d, \Hk\().1d
        eor     ghash_lo.16b, ghash_lo.16b, ghash_tmp.16b
        // High product
        pmull2  ghash_tmp.1q, \input\().2d, \Hk\().2d
        eor     ghash_hi.16b, ghash_hi.16b, ghash_tmp.16b
        // Middle product
        mov     ghash_tmp_d, \input\().d[1]
        eor     ghash_tmp.8b, ghash_tmp.8b, \input\().8b
        pmull   ghash_tmp.1q, ghash_tmp.1d, \Hk_mid\().1d
        eor     ghash_mid.16b, ghash_mid.16b, ghash_tmp.16b
.endm

.macro ghash_acc_1 input, Hk, Hk_mid
        rev64   \input\().16b, \input\().16b
        // Low product
        pmull   ghash_tmp.1q, \input\().1d, \Hk\().1d
        eor     ghash_lo.16b, ghash_lo.16b, ghash_tmp.16b
        // High product
        pmull2  ghash_tmp.1q, \input\().2d, \Hk\().2d
        eor     ghash_hi.16b, ghash_hi.16b, ghash_tmp.16b
        // Middle product
        ext     ghash_tmp.16b, \input\().16b, \input\().16b, #8
        eor     ghash_tmp.16b, ghash_tmp.16b, \input\().16b
        pmull2  ghash_tmp.1q, ghash_tmp.2d, \Hk_mid\().2d
        eor     ghash_mid.16b, ghash_mid.16b, ghash_tmp.16b
.endm

.macro ghash_init_with_tag_0 input, Hk, Hk_mid, tag
        rev64 \input\().16b, \input\().16b
        eor   \input\().16b, \input\().16b, \tag\().16b
        // Low product
        pmull   ghash_lo.1q, \input\().1d, \Hk\().1d
        // High product
        pmull2  ghash_hi.1q, \input\().2d, \Hk\().2d
        // Middle product
        mov     ghash_tmp_d, \input\().d[1]
        eor     ghash_tmp.8b, ghash_tmp.8b, \input\().8b
        pmull   ghash_mid.1q, ghash_tmp.1d, \Hk_mid\().1d
.endm

.macro ghash_init_with_tag_1 input, Hk, Hk_mid, tag
        rev64 \input\().16b, \input\().16b
        eor   \input\().16b, \input\().16b, \tag\().16b
        // Low product
        pmull   ghash_lo.1q, \input\().1d, \Hk\().1d
        // High product
        pmull2  ghash_hi.1q, \input\().2d, \Hk\().2d
        // Middle product
        ext     ghash_tmp.16b, \input\().16b, \input\().16b, #8
        eor     ghash_tmp.16b, ghash_tmp.16b, \input\().16b
        pmull2  ghash_mid.1q, ghash_tmp.2d, \Hk_mid\().2d
.endm

.macro ghash_acc_with_tag_0 input, Hk, Hk_mid, tag
        rev64   \input\().16b, \input\().16b
        eor   \input\().16b, \input\().16b, \tag\().16b
        // Low product
        pmull   ghash_tmp.1q, \input\().1d, \Hk\().1d
        eor     ghash_lo.16b, ghash_lo.16b, ghash_tmp.16b
        // High product
        pmull2  ghash_tmp.1q, \input\().2d, \Hk\().2d
        eor     ghash_hi.16b, ghash_hi.16b, ghash_tmp.16b
        // Middle product
        mov     ghash_tmp_d, \input\().d[1]
        eor     ghash_tmp.8b, ghash_tmp.8b, \input\().8b
        pmull   ghash_tmp.1q, ghash_tmp.1d, \Hk_mid\().1d
        eor     ghash_mid.16b, ghash_mid.16b, ghash_tmp.16b
.endm

.macro ghash_acc_with_tag_1 input, Hk, Hk_mid, tag
        rev64   \input\().16b, \input\().16b
        eor   \input\().16b, \input\().16b, \tag\().16b
        // Low product
        pmull   ghash_tmp.1q, \input\().1d, \Hk\().1d
        eor     ghash_lo.16b, ghash_lo.16b, ghash_tmp.16b
        // High product
        pmull2  ghash_tmp.1q, \input\().2d, \Hk\().2d
        eor     ghash_hi.16b, ghash_hi.16b, ghash_tmp.16b
        // Middle product
        ext     ghash_tmp.16b, \input\().16b, \input\().16b, #8
        eor     ghash_tmp.16b, ghash_tmp.16b, \input\().16b
        pmull2  ghash_tmp.1q, ghash_tmp.2d, \Hk_mid\().2d
        eor     ghash_mid.16b, ghash_mid.16b, ghash_tmp.16b
.endm

.macro ghash_finalize tag
        eor        modulo_tmp0.16b, ghash_lo.16b,  ghash_hi.16b
        pmull      modulo_tmp1.1q,  ghash_hi.1d,   ghash_mod.1d
        ext        ghash_hi.16b,    ghash_hi.16b,  ghash_hi.16b, #8
        eor        ghash_mid.16b,   ghash_mid.16b, modulo_tmp0.16b
        eor        modulo_tmp1.16b, ghash_hi.16b,  modulo_tmp1.16b
        eor        ghash_mid.16b,   ghash_mid.16b, modulo_tmp1.16b
        pmull      ghash_hi.1q,     ghash_mid.1d,  ghash_mod.1d
        eor        ghash_lo.16b,    ghash_lo.16b,  ghash_hi.16b
        ext        ghash_mid.16b,   ghash_mid.16b, ghash_mid.16b, #8
        eor        \tag\().16b,     ghash_lo.16b,  ghash_mid.16b
        ext        \tag\().16b, \tag\().16b, \tag\().16b, #8
.endm

.macro load_tag
        ldr      tag_q, [tag_ptr]
        rev64    tag.16b, tag.16b
.endm

.macro prepare_ghash
        // Prepare constant for modular reduction
        movi ghash_mod.8b, #0xc2
        shl  ghash_mod_d, ghash_mod_d, #56
.endm

/********************************************************************/
/*                            Core routine                          */
/********************************************************************/

.align        4
_aes_gcm_enc_kernel_slothy_base_256:
aes_gcm_enc_kernel_slothy_base_256:
#ifdef BORINGSSL_DISPATCH_TEST
        adrp  x9,_BORINGSSL_function_hit@PAGE
        add   x9, x9, _BORINGSSL_function_hit@PAGEOFF
        mov   w10, #1
        strb  w10, [x9,#15] // kFlag_aes_gcm_slothy
#endif

        AARCH64_VALID_CALL_TARGET
        sub sp, sp, #STACK_SIZE

Lenc_preamble_start:
        save_gprs
        save_vregs

        lsr byte_len, len_bits, #3

        load_round_keys
        load_tag
        load_iv

        prepare_loop_counts
        prepare_ghash

Lenc_preamble_end:

        cbz count, Lremainder_dispatch
        load_htable_12
        load_htable_34
Lloop_unrolled_start:

        load_htable_12

        ldp plain_lo, plain_hi, [input, #(3*16)]
        aes_full_block aes_st, plain, res, 3
        str res_q, [output, #(3*16)]

        ghash_init_0 res, Ht1, Ht12

        ldp plain_lo, plain_hi, [input, #(2*16)]
        aes_full_block aes_st, plain, res, 2
        str res_q, [output, #(2*16)]

        ghash_acc_1 res, Ht2, Ht12

        load_htable_34

        ldp plain_lo, plain_hi, [input, #(1*16)]
        aes_full_block aes_st, plain, res, 1
        str res_q, [output, #(1*16)]

        ghash_acc_0 res, Ht3, Ht34

        ldp plain_lo, plain_hi, [input], #(4*16)
        aes_full_block aes_st, plain, res, 0
        str res_q, [output], #(4*16)

        ghash_acc_with_tag_1 res, Ht4, Ht34, tag
        ghash_finalize tag

        add ctr, ctr, #UNROLL
        sub count, count, #1
        cbnz count, Lloop_unrolled_start
Lloop_unrolled_end:

Lremainder_dispatch:
        cmp remainder, #3
        b.eq Lremainder_3_start
        cmp remainder, #2
        b.eq Lremainder_2_start
        cmp remainder, #1
        b.eq Lremainder_1_start
        b Lend

Lremainder_3_start:
        load_htable_12

        ldp plain_lo, plain_hi, [input, #(2*16)]
        aes_full_block aes_st, plain, res, 2
        str res_q, [output, #(2*16)]

        ghash_init_0 res, Ht1, Ht12

        ldp plain_lo, plain_hi, [input, #(1*16)]
        aes_full_block aes_st, plain, res, 1
        str res_q, [output, #(1*16)]

        ghash_acc_1 res, Ht2, Ht12
        load_htable_3

        ldp plain_lo, plain_hi, [input, #(0*16)]
        aes_full_block aes_st, plain, res, 0
        str res_q, [output, #(0*16)]

        ghash_acc_with_tag_0 res, Ht3, Ht34, tag
        ghash_finalize tag
        add ctr, ctr, #3
Lremainder_3_end:
        b Lend

Lremainder_2_start:
        load_htable_12

        ldp plain_lo, plain_hi, [input, #(1*16)]
        aes_full_block aes_st, plain, res, 1
        str res_q, [output, #(1*16)]

        ghash_init_0 res, Ht1, Ht12

        ldp plain_lo, plain_hi, [input, #(0*16)]
        aes_full_block aes_st, plain, res, 0
        str res_q, [output, #(0*16)]

        ghash_acc_with_tag_1 res, Ht2, Ht12, tag
        ghash_finalize tag
        add ctr, ctr, #2
Lremainder_2_end:
        b Lend

Lremainder_1_start:
        load_htable_1

        ldp plain_lo, plain_hi, [input, #(0*16)]
        aes_full_block aes_st, plain, res, 0
        str res_q, [output, #(0*16)]

        ghash_init_with_tag_0 res, Ht1, Ht12, tag
        ghash_finalize tag
        add ctr, ctr, #1
Lremainder_1_end:
Lend:

        // Return number of bytes processed
        mov x0, byte_len
        // Store new authentication tag
        rev64 tag.16b, tag.16b
        str tag_q, [tag_ptr]

        // Store updated counter
        // rev32 rtmp_ctr.16b, rtmp_ctr.16b
        // str rtmp_ctr_q, [ivec]
        rev ctr_tmp_w, ctr
        str ctr_tmp_w, [ivec, #12]

        restore_vregs
        restore_gprs

Lenc_postamble_end:
        add sp, sp, #STACK_SIZE

        ret

#endif
#endif  // !OPENSSL_NO_ASM && defined(__AARCH64EL__) && defined(__APPLE__)
#if defined(__ELF__)
// See https://www.airs.com/blog/archives/518.
.section .note.GNU-stack,"",%progbits
#endif
