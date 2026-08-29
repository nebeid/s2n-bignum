#!/usr/bin/env python3
import csv
import glob
import math
import os
import statistics

ROOT = os.path.dirname(__file__)
HOSTS = {
    "ip-172-31-11-58": ("G2", "N1"),
    "ip-172-31-4-159": ("G3", "V1"),
    "ip-172-31-44-56": ("G4", "V2"),
    "ip-172-31-42-229": ("G5", "V3"),
}

data = {}
comparison = {}
for path in glob.glob(os.path.join(ROOT, "results", "entry-*.log")):
    basename = os.path.basename(path)
    host = basename.split("-ip-", 1)[1][:-4]
    host = "ip-" + host
    layout = None
    if "entry-compare-" in basename:
        layout = ("hybrid-first" if "hybrid-first" in basename
                  else "entry-first")
    with open(path, encoding="ascii") as source:
        rows = csv.reader(line for line in source if line.startswith("RES,"))
        for _, _, size, variant, _, median in rows:
            data.setdefault((host, int(size), variant), []).append(float(median))
            if layout:
                comparison.setdefault(
                    (host, layout, int(size), variant), []
                ).append(float(median))


def median(host, size, variant):
    return statistics.median(data[(host, size, variant)])


def faster_percent(first, second):
    return 100.0 * (second - first) / second


def geometric_mean(values):
    return math.exp(sum(math.log(value) for value in values) / len(values))


for host, (generation, core) in HOSTS.items():
    print(f"\n## {generation} / {core}")
    controls = ["enc-4x-fast-tail"]
    if generation != "G2":
        controls.append("enc-8x")
    print("| bytes | entry ns | fast-tail change |"
          + (" compact 8x change |" if generation != "G2" else ""))
    print("|---:|---:|---:|" + ("---:|" if generation != "G2" else ""))
    for size in range(16, 129, 16):
        entry = median(host, size, "enc-4x-entry")
        fast_tail = median(host, size, "enc-4x-fast-tail")
        row = (f"| {size} | {entry:.3f} | "
               f"{faster_percent(entry, fast_tail):+.1f}% |")
        if generation != "G2":
            compact = median(host, size, "enc-8x")
            row += f" {faster_percent(entry, compact):+.1f}% |"
        print(row)

    short_sizes = [16, 32, 48]
    for control in controls:
        changes = [
            median(host, size, "enc-4x-entry") / median(host, size, control)
            for size in short_sizes
        ]
        print(f"16--48 B geometric-mean entry change vs {control}: "
              f"{(geometric_mean(changes) - 1.0) * -100.0:+.3f}%")

    large_sizes = [1344, 2048, 4096, 8192, 16384, 32768]
    changes = [
        median(host, size, "enc-4x-entry")
        / median(host, size, "enc-4x-late-tag")
        for size in large_sizes
    ]
    print("1344 B--32 KiB geometric-mean entry change vs late-tag: "
          f"{(geometric_mean(changes) - 1.0) * -100.0:+.3f}%")

    for layout in ("entry-first", "hybrid-first"):
        changes = []
        points = []
        for size in (16, 32, 48):
            entry = statistics.median(
                comparison[(host, layout, size, "entry")]
            )
            helper = statistics.median(
                comparison[(host, layout, size, "shared-helper")]
            )
            change = faster_percent(entry, helper)
            changes.append(entry / helper)
            points.append(f"{size}: {change:+.1f}%")
        geometric = (geometric_mean(changes) - 1.0) * -100.0
        print(f"{layout} entry change vs helper: {', '.join(points)}; "
              f"GM {geometric:+.3f}%")
