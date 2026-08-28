# Generate a 1--3-block-only kernel from Hanno's optimized encrypt fast_tail.
# The exported wrapper guarantees this object is never called for >= 4 blocks.

/^Lenc_preamble_end:/ {
    print
    print "        b Lloop_unrolled_end"
    skipping_loop = 1
    next
}

skipping_loop && /^Lloop_unrolled_end:/ {
    skipping_loop = 0
}

!skipping_loop {
    print
}
