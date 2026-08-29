# Convert a complete encrypt kernel into a body entered after the shared
# frame setup. Usage:
#   awk -v name=... -v short=0|1 -f make-enc-entry-body.awk source.S

{
    gsub(/aes_gcm_enc_kernel_slothy_base_256/, name)
}

/^#ifdef BORINGSSL_DISPATCH_TEST$/ {
    skipping_dispatch_test = 1
    next
}

skipping_dispatch_test {
    if (/^#endif$/) {
        skipping_dispatch_test = 0
    }
    next
}

/^[[:space:]]+AARCH64_VALID_CALL_TARGET$/ ||
/^[[:space:]]+sub sp, sp, #STACK_SIZE$/ ||
/^Lenc_preamble_start:$/ ||
/^[[:space:]]+save_gprs$/ ||
/^[[:space:]]+save_vregs$/ ||
/^[[:space:]]+lsr byte_len, len_bits, #3$/ {
    next
}

short && /^[[:space:]]+prepare_loop_counts$/ {
    print "        lsr remainder, byte_len, #4"
    next
}

short && /^[[:space:]]+b Lloop_unrolled_end$/ {
    next
}

/^[[:space:]]+load_round_keys$/ {
    if (short) {
        print "        load_round_key 14"
    } else {
        print "        load_round_key_scalar 14"
    }
    next
}

/^[[:space:]]+prepare_ghash$/ {
    next
}

/^[[:space:]]+restore_vregs$/ {
    print "        b aes_gcm_enc_shared_restore_256"
    skipping_restore = 1
    next
}

skipping_restore {
    if (/^[[:space:]]+ret$/) {
        skipping_restore = 0
    }
    next
}

{
    print
}
