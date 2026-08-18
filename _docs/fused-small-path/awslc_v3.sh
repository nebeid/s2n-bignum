#!/bin/bash
# awslc_v3.sh <A|B|C> : same as awslc.sh but ALSO relaxes
# CRYPTO_is_ARMv8_GCM_8x_capable() so the 8x path is reachable on Neoverse-V3
# (aws-lc v1.68.0 allowlists only Neoverse-V1/V2/Apple-M, so on Graviton5 the
# 8x kernel is dead regardless of the length threshold).
set -e
V="$1"
/tmp/fsp/awslc.sh "$V" > /tmp/awslc_stage_$V.log 2>&1 || { tail -20 /tmp/awslc_stage_$V.log; exit 1; }
D=/tmp/awslc_$V
H=$D/crypto/fipsmodule/cpucap/internal.h
python3 - "$H" <<'PY'
import sys,re
p=sys.argv[1]; s=open(p).read()
old="""  return (CRYPTO_is_ARMv8_SHA3_capable() &&
          ((OPENSSL_armcap_P & ARMV8_NEOVERSE_V1) != 0 ||
           (OPENSSL_armcap_P & ARMV8_NEOVERSE_V2) != 0 ||
           (OPENSSL_armcap_P & ARMV8_APPLE_M) != 0));"""
new="""  return CRYPTO_is_ARMv8_SHA3_capable();   /* [V3] allowlist relaxed */"""
assert old in s, "predicate not found"
open(p,'w').write(s.replace(old,new))
print("relaxed 8x capability predicate")
PY
mv $D /tmp/awslc_${V}v3
cd /tmp/awslc_${V}v3/build
ninja bssl > /tmp/ninja_${V}v3.log 2>&1 || { tail -20 /tmp/ninja_${V}v3.log; exit 1; }
echo "built /tmp/awslc_${V}v3/build/tool/bssl"
