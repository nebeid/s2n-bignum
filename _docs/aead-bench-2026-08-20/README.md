# Artifacts: AES-256-GCM decrypt, four-variant benchmark, 2026-08-20

**The report lives in
[`../percommit-crosscore-benchmark-2026-08-14.md`](../percommit-crosscore-benchmark-2026-08-14.md),
section "2026-08-20 extension".** This directory holds only the harness and raw
data, so the run can be re-derived or re-analysed with a different estimator.

Banking these in-repo is a deliberate correction: the 2026-08-14 cross-core
harness was left in `/tmp` and is now gone, which makes that report's tables
unauditable.

## Contents

| path | what |
|---|---|
| `harness/harness.c` | interleaved timing harness + mandatory correctness gate |
| `harness/build.sh` | assemble each `.S` separately, `objcopy --redefine-sym`, link one binary with four A/A duplicates |
| `harness/mk.sh` | object staging |
| `harness/clk.c` | in-process core-clock measurement (dependent scalar-add chain) |
| `harness/analyze.py` | aggregation: min-over-processes, A/A floors, delta tables |
| `harness/src/A.S` | current aws-lc `aesv8_gcm_8x_dec_256`, md5 `eb1412c648f8ae2bc613378897c06c78` |
| `harness/src/B.S` | ours before the adopted optimisations (v0 `5500b7e6`), md5 `1ebeecdbc02cddc69069f85c80697e17` |
| `harness/src/C.S` | ours after (v5 `91b1ce25`), md5 `6de404aca78da9799a911b126727c73f` |
| `harness/src/D.S` | fused short-message variant (`d5r`), md5 `94b4f2c9efc7b85341def2858074c1b1` |
| `raw/out_r8g.txt` | every `RES` line from all 22 processes |

Expected assembled object md5 for D: `968b7a2f0e89093da5d1961d978e4f44` — the
value recorded in STATE for the object baked into the fused HOL checkpoint. If a
rebuild does not reproduce it, the fused variant is not the one that was proved.

## Reproducing

```bash
ssh ec2r8g 'mkdir -p /tmp/pcb4 && cd /tmp/pcb4 && ./build.sh'
ssh ec2r8g 'md5sum /tmp/pcb4/obj/D.o'   # expect 968b7a2f0e89093da5d1961d978e4f44

ssh ec2r8g 'cd /tmp/pcb4
  for p in $(seq 1 10);  do taskset -c 3 ./pcb4 200 $p >> out_r8g.txt; done
  for p in $(seq 11 22); do taskset -c 3 ./pcb4 300 $p >> out_r8g.txt; done'

python3 harness/analyze.py raw/out_r8g.txt
```

Host: `ec2r8g`, Graviton4 / Neoverse-V2, 4 cores, 2.7929 GHz measured
in-process. Sizes 16/32/64/128/256/512/1024/4096 B.

## One-line summary

Versus shipping aws-lc, the optimisation arc in PR #445 is **−22.2 % at 128 B**,
−17.6 % at 256 B, −11.7 % at 512 B, −1.6 % at 4 KB. The fused variant adds
−46/−44/−27 % at 16/32/64 B and nothing at ≥ 128 B. **The +1.5 % at 512 B this
run originally reported was retracted** — it was a `min`-over-processes artifact;
a four-host follow-up (`../512b-placement-2026-08-20/`) measured the median of
per-process paired deltas at −0.29 % (V1), +0.14 % (V2), +0.02 % (V3), i.e. no
regression on any core. The remaining argument against the fused variant is
reach, not cost: aws-lc's dispatch never routes sub-256 B (soon sub-128 B)
traffic to this kernel.
