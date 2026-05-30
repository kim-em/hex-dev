#!/usr/bin/env python3
"""For each basis emitted by /tmp/lll-lean-times.jsonl, run fpylll LLL on the
same basis and write merged JSONL with timings."""
import json
import time
from pathlib import Path

from fpylll import IntegerMatrix, LLL

LEAN = Path("/tmp/lll-lean-times.jsonl")
OUT = Path("/tmp/lll-merged.jsonl")


def time_fpylll(basis, target_seconds: float = 0.4):
    reps = 1
    while True:
        t0 = time.perf_counter()
        last = None
        for _ in range(reps):
            # IntegerMatrix from Python list-of-lists. LLL.reduction mutates,
            # so make a fresh copy each rep.
            M = IntegerMatrix.from_matrix(basis)
            last = LLL.reduction(M, delta=0.75)
        elapsed = time.perf_counter() - t0
        if elapsed >= target_seconds or reps >= 256:
            return elapsed / reps, last, reps
        reps *= 2


rows = []
for line in LEAN.read_text().splitlines():
    line = line.strip()
    if not line or not line.startswith("{"):
        continue
    rec = json.loads(line)
    basis = rec["basis"]
    per_call, _, reps = time_fpylll(basis)
    merged = {
        "n": rec["n"],
        "lean_seconds": rec["lean_nanos"] / 1e9,
        "fpylll_seconds": per_call,
        "fpylll_reps": reps,
    }
    rows.append(merged)
    print(
        f"n {rec['n']:>4} | lean {rec['lean_nanos']/1e9:>10.6f}s | "
        f"fpylll {per_call*1e6:>10.2f} µs  (ratio {rec['lean_nanos']/1e9 / per_call:>10.0f}x)",
    )

OUT.write_text("\n".join(json.dumps(r) for r in rows) + "\n")
print(f"\nWrote {OUT}")
