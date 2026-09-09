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
LAYOUTS = ("4x-first", "8x-first")
FINAL_4X = "enc-4x-shared"
FINAL_8X = "enc-8x-final"
COMPACT = "enc-8x-compact"


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


def load(mode, ip, layout):
    return medians(ROOT / f"finalists-{mode}-{layout}-ip-{ip}.log")


def print_table(mode, sizes):
    print(f"\n{mode}: 4x shared advantage over final 8x")
    print("| bytes | layout | "
          + " | ".join(name for name, _ in PLATFORMS) + " |")
    print("|---:|---|" + "---:|" * len(PLATFORMS))
    for size in sizes:
        for layout in LAYOUTS:
            cells = []
            for _, ip in PLATFORMS:
                data = load(mode, ip, layout)
                cells.append(
                    f"{advantage(data[size, FINAL_8X], data[size, FINAL_4X]):+.1f}%"
                )
            print(f"| {size:,} | {layout} | " + " | ".join(cells) + " |")


print_table("small", range(16, 129, 16))
print_table("large", (1344, 2048, 4096, 8192, 16384, 32768))

for label, sizes, mode in (
        ("16--48 B", (16, 32, 48), "small"),
        ("16--64 B", (16, 32, 48, 64), "small"),
        ("1,344 B--32 KiB", (1344, 2048, 4096, 8192, 16384, 32768), "large")):
    print(f"\n{label} geometric-mean final 8x speed advantage over 4x shared")
    for name, ip in PLATFORMS:
        cells = []
        for layout in LAYOUTS:
            data = load(mode, ip, layout)
            ratios = [
                data[size, FINAL_4X] / data[size, FINAL_8X]
                for size in sizes
            ]
            cells.append(f"{layout}: {geometric_advantage(ratios):+.2f}%")
        print(name, "; ".join(cells))

print("\ncompact control spread between layouts")
for name, ip in PLATFORMS:
    first = load("small", ip, "4x-first")
    second = load("small", ip, "8x-first")
    changes = [
        max(first[size, COMPACT], second[size, COMPACT])
        / min(first[size, COMPACT], second[size, COMPACT])
        for size in range(16, 129, 16)
    ]
    print(name, f"max {max(changes) - 1.0:+.3%}")
