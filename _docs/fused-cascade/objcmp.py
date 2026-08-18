#!/usr/bin/env python3
"""Normalised objdump instruction-stream comparison: is the nblk>8 path of a
variant byte-identical IN CONTENT to the baseline (addresses may shift)?

Usage: objcmp.py base.o variant.o

Branch/label targets and instruction addresses are masked; everything else must
match instruction-for-instruction.  Reports the insertion point, how many
baseline instructions are matched after skipping the inserted ones, and what is
left over (the relocated .L256_dec_ret stub in the fused designs).
"""
import re, subprocess, sys

BR = re.compile(r"^(b|bl|b\.[a-z]+|cbz|cbnz|tbz|tbnz)$")


def dump(path):
    out = subprocess.run(["objdump", "-d", "--no-show-raw-insn", path],
                         capture_output=True, text=True).stdout
    ins = []
    for ln in out.split("\n"):
        m = re.match(r"^\s*[0-9a-f]+:\s+(\S+)(?:\s+(.*))?$", ln)
        if not m:
            continue
        mn = m.group(1)
        op = (m.group(2) or "").strip()
        op = re.sub(r"\s*//.*$", "", op)
        if BR.match(mn):
            # mask the target: last comma-separated operand
            parts = [p.strip() for p in op.split(",")]
            parts[-1] = "TGT"
            op = ", ".join(parts)
        ins.append("%s %s" % (mn, op))
    return ins


def main(a, b):
    A, B = dump(a), dump(b)
    print("%s %d instructions, %s %d instructions" % (a, len(A), b, len(B)))
    i = j = 0
    while i < len(A) and j < len(B) and A[i] == B[j]:
        i += 1
        j += 1
    print("first divergence at baseline instruction %d (base: %s | variant: %s)"
          % (i, A[i] if i < len(A) else "<end>", B[j] if j < len(B) else "<end>"))
    # how many variant instructions were inserted before the streams resync?
    ins = None
    for k in range(1, 64):
        if j + k < len(B) and B[j + k] == A[i]:
            # tentative resync; require a long run
            n = 0
            while i + n < len(A) and j + k + n < len(B) and A[i + n] == B[j + k + n]:
                n += 1
            if n > 50:
                ins = k
                break
    if ins is None:
        print("NO RESYNC FOUND")
        return 1
    n = 0
    while i + n < len(A) and j + ins + n < len(B) and A[i + n] == B[j + ins + n]:
        n += 1
    print("%d instructions inserted; then %d more baseline instructions identical"
          % (ins, n))
    left = A[i + n:]
    print("baseline tail left unmatched at this point: %d instruction(s): %s"
          % (len(left), left[:6]))
    # look for that tail verbatim later in the variant (relocated)
    tail_ok = False
    if left:
        for s in range(j + ins + n, len(B) - len(left) + 1):
            if B[s:s + len(left)] == left:
                tail_ok = True
                print("  -> found verbatim at variant instruction %d (relocated, identical)" % s)
                break
        if not tail_ok:
            print("  -> NOT FOUND: baseline tail is NOT preserved")
    print("appended after the baseline stream: %d instruction(s)"
          % (len(B) - (j + ins + n) - (len(left) if tail_ok else 0)))
    ok = (len(A) - i - n == 0) or tail_ok
    print("VERDICT: nblk>8 content %s" % ("UNCHANGED" if ok else "CHANGED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
