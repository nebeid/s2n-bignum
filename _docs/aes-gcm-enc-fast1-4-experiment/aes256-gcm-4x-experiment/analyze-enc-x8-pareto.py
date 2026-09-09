#!/usr/bin/env python3
import math
import statistics
from pathlib import Path

ROOT = Path(__file__).resolve().parent / "results"
PLATFORMS = [
    ("G3 / V1", "172-31-4-159"),
    ("G4 / V2", "172-31-44-56"),
    ("G5 / V3", "172-31-42-229"),
]
COMPACT = "enc-8x-compact-fast1-4"
SHARED = "enc-8x-w4-shared"
INLINE = "enc-8x-w4-inline"


def medians(path):
    samples = {}
    for line in path.read_text().splitlines():
        if not line.startswith("RES,"):
            continue
        _, _, size, label, _, median = line.split(",")
        samples.setdefault((int(size), label), []).append(float(median))
    return {key: statistics.median(values) for key, values in samples.items()}


def advantage(control, candidate):
    return 100.0 * (control - candidate) / control


def geometric_advantage(ratios):
    return 100.0 * (math.exp(statistics.mean(map(math.log, ratios))) - 1.0)


short = {
    name: medians(ROOT / f"x8-pareto-small-ip-{ip}.log")
    for name, ip in PLATFORMS
}
large = {
    name: medians(ROOT / f"x8-pareto-large-ip-{ip}.log")
    for name, ip in PLATFORMS
}

print("full shared-setup 8x advantage over compact fast1-fast4 8x")
print("| bytes | " + " | ".join(name for name, _ in PLATFORMS) + " |")
print("|---:|" + "---:|" * len(PLATFORMS))
for size in range(16, 129, 16):
    cells = []
    for name, _ in PLATFORMS:
        data = short[name]
        cells.append(f"{advantage(data[size, COMPACT], data[size, SHARED]):+.1f}%")
    print(f"| {size} | " + " | ".join(cells) + " |")

print("\n16-64 B geometric mean")
for name, _ in PLATFORMS:
    data = short[name]
    ratios = [data[size, COMPACT] / data[size, SHARED]
              for size in range(16, 65, 16)]
    print(name, f"{geometric_advantage(ratios):+.2f}%")

print("\nfull shared-reduction advantage over full inline reduction, 16-64 B")
for name, _ in PLATFORMS:
    data = short[name]
    ratios = [data[size, INLINE] / data[size, SHARED]
              for size in range(16, 65, 16)]
    print(name, f"{geometric_advantage(ratios):+.3f}%")

print("\nomitted-width fallback advantage over compact (negative is slower)")
print("| omitted width | build | "
      + " | ".join(name for name, _ in PLATFORMS) + " |")
print("|---:|---|" + "---:|" * len(PLATFORMS))
for size, build in (
        (32, "enc-8x-w1-inline"),
        (48, "enc-8x-w2-shared"),
        (64, "enc-8x-w3-shared")):
    cells = []
    for name, _ in PLATFORMS:
        data = short[name]
        cells.append(f"{advantage(data[size, COMPACT], data[size, build]):+.1f}%")
    print(f"| {size} B | {build.removeprefix('enc-8x-')} | "
          + " | ".join(cells) + " |")

print("\nfull shared-setup 8x advantage over compact fast1-fast4 8x, large sizes")
print("| bytes | " + " | ".join(name for name, _ in PLATFORMS) + " |")
print("|---:|" + "---:|" * len(PLATFORMS))
for size in (1344, 2048, 4096, 8192, 16384, 32768):
    cells = []
    for name, _ in PLATFORMS:
        data = large[name]
        cells.append(f"{advantage(data[size, COMPACT], data[size, SHARED]):+.3f}%")
    print(f"| {size} | " + " | ".join(cells) + " |")

print("\nlarge geometric mean")
for name, _ in PLATFORMS:
    data = large[name]
    ratios = [data[size, COMPACT] / data[size, SHARED]
              for size in (1344, 2048, 4096, 8192, 16384, 32768)]
    print(name, f"{geometric_advantage(ratios):+.3f}%")
