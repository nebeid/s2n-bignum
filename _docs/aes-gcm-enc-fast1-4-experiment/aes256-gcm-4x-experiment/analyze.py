#!/usr/bin/env python3
import csv
import glob
import os
import statistics

HOSTS = {
    "ip-172-31-4-159": ("G3", "Neoverse-V1"),
    "ip-172-31-44-56": ("G4", "Neoverse-V2"),
    "ip-172-31-42-229": ("G5", "Neoverse-V3"),
}

data = {}
for path in glob.glob(os.path.join(os.path.dirname(__file__), "results", "raw-*.log")):
    host = os.path.basename(path)[4:-4]
    if host not in HOSTS:
        continue
    with open(path) as f:
        for row in csv.reader(line for line in f if line.startswith("RES,")):
            _, process, size, variant, best, median = row
            data.setdefault((host, int(size), variant), []).append(float(median))

for host, (label, core) in HOSTS.items():
    print(f"\n## {label} / {core}\n")
    print("| bytes | direction | 8x ns | fastest John 4x | 4x ns | 8x faster |")
    print("|---:|:---|---:|:---|---:|---:|")
    for direction, variants in (
        ("encrypt", ["enc-basic", "enc-dual", "enc-fasttail", "enc-reload",
                     "enc-mem2", "enc-mem2tail", "enc-scalarrk"]),
        ("decrypt", ["dec-basic", "dec-mem2"]),
    ):
        for size in range(16, 129, 16):
            x8 = statistics.median(data[(host, size, direction[:3] + "-x8")])
            candidates = {
                v: statistics.median(data[(host, size, v)])
                for v in variants
            }
            winner = min(candidates, key=candidates.get)
            four = candidates[winner]
            delta = 100.0 * (four - x8) / four
            print(f"| {size} | {direction} | {x8:.3f} | `{winner}` | "
                  f"{four:.3f} | {delta:+.1f}% |")
