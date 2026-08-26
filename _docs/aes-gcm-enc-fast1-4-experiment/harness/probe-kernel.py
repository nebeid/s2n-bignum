#!/usr/bin/env python3
"""Print every file offset where an object's .text bytes occur in a binary."""
import sys

needle = open(sys.argv[1], "rb").read()
haystack = open(sys.argv[2], "rb").read()
offsets = []
start = 0
while True:
    offset = haystack.find(needle, start)
    if offset < 0:
        break
    offsets.append(offset)
    start = offset + 1
if not offsets:
    raise SystemExit("NOTFOUND")
print(",".join(hex(offset) for offset in offsets))
