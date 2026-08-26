#!/usr/bin/awk -f

# Remove only the fast5/fast6/fast7 dispatches and their contiguous appended
# bodies. The following fast4em label marks the first retained final refinement.
/\[s127 fast[567]\]/ {
    getline
    next
}

/^L256_enc_fast5:/ {
    dropping = 1
}

dropping && /^L256_enc_fast4em:/ {
    dropping = 0
}

!dropping {
    print
}
