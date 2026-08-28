// Dispatch 1--3 blocks to the short-only fast-tail kernel and larger inputs
// to Hanno's unchanged scalar_iv_mem_late_tag_scalar_rk kernel.

	.arch	armv8-a+crypto
	.text
	.globl	aes_gcm_enc_kernel_hybrid_256
	.hidden	aes_gcm_enc_kernel_hybrid_256
	.type	aes_gcm_enc_kernel_hybrid_256,%function
	.align	4
aes_gcm_enc_kernel_hybrid_256:
	cmp	x1, #(3 * 16 * 8)
	b.ls	aes_gcm_enc_kernel_short_256
	b	aes_gcm_enc_kernel_late_tag_256
	.size	aes_gcm_enc_kernel_hybrid_256,.-aes_gcm_enc_kernel_hybrid_256

	.section .note.GNU-stack,"",%progbits
