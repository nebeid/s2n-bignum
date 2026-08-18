#!/bin/bash
# probe.sh : per-entry-point and per-section liveness probes for the cascade.
#
#   zapN    -- entry stub N's  acc <- Xi'*H^N  products replaced by zero.
#              Stub N is reached ONLY for nblk == N, so this MUST break
#              exactly nblk == N and nothing else.
#   zsecJ   -- cascade section J's own GHASH products replaced by zero.
#              Section J is executed for every nblk >= J (fall-through), so
#              this MUST break exactly nblk >= J and nothing else.
#
# Together the sixteen probes prove (a) each of the eight entry labels is
# entered for exactly its own length and its seed is load-bearing, and (b) the
# fall-through really does run sections n..1 and only those.
set -e
cd /tmp/fsp
echo "==== entry-stub probes (must fail EXACTLY nblk == N) ===="
for N in 1 2 3 4 5 6 7 8; do
  python3 gen_casck.py src/base.S src/kzap$N.S 1.0 0.35 $N 0 >/dev/null
  ./mk.sh kzap$N
  ./build_bench.sh base kzap$N
  got=$(ALLOW_MISMATCH=1 SELFCHECK_ONLY=1 taskset -c 3 ./bench 2 base kzap$N \
        | sed -n 's/^SELFCHECK FAIL nblk=\([0-9]*\).*/\1/p' | tr '\n' ',' )
  echo "zap$N: fails at nblk={${got%,}}   expected {$N}"
done
echo "==== section probes (must fail EXACTLY nblk >= J) ===="
for J in 1 2 3 4 5 6 7 8; do
  python3 gen_casck.py src/base.S src/ksec$J.S 1.0 0.35 0 $J >/dev/null
  ./mk.sh ksec$J
  ./build_bench.sh base ksec$J
  got=$(ALLOW_MISMATCH=1 SELFCHECK_ONLY=1 taskset -c 3 ./bench 2 base ksec$J \
        | sed -n 's/^SELFCHECK FAIL nblk=\([0-9]*\).*/\1/p' | tr '\n' ',' )
  lo=$(echo "${got%,}" | cut -d, -f1); hi=$(echo "${got%,}" | rev | cut -d, -f1 | rev)
  n=$(echo "${got%,}" | tr ',' '\n' | wc -l | tr -d ' ')
  echo "zsec$J: fails at nblk=$lo..$hi ($n lengths)   expected $J..8 ($((9-J)) lengths, since nblk>8 uses the untouched path)"
done
