#!/usr/bin/env python3
"""Read /tmp/bz-lean-times.jsonl, factor each poly with FLINT, write merged JSONL."""
import json
import sys
import time
from pathlib import Path

import flint

LEAN = Path("/tmp/bz-lean-times.jsonl")
OUT = Path("/tmp/bz-merged.jsonl")


def time_flint(coeffs, target_seconds: float = 0.3):
    """Adaptive repeat: keep doubling until total wall >= target_seconds, return per-call seconds."""
    p = flint.fmpz_poly(coeffs)
    reps = 1
    while True:
        t0 = time.perf_counter()
        last = None
        for _ in range(reps):
            last = p.factor()
        elapsed = time.perf_counter() - t0
        if elapsed >= target_seconds or reps >= 4096:
            return elapsed / reps, last, reps
        reps *= 4


rows = []
for line in LEAN.read_text().splitlines():
    line = line.strip()
    if not line or not line.startswith("{"):
        continue
    rec = json.loads(line)
    coeffs = rec["coeffs"]
    per_call, fac, reps = time_flint(coeffs)
    n_irr = sum(1 for _, _ in fac[1])  # fac is (content, [(poly, mult)...])
    merged = {
        "degree": rec["degree"],
        "lean_seconds": rec["lean_nanos"] / 1e9,
        "lean_factors": rec["factors"],
        "flint_seconds": per_call,
        "flint_factors": n_irr,
        "flint_reps": reps,
    }
    rows.append(merged)
    print(
        f"deg {rec['degree']:>3} | "
        f"lean {rec['lean_nanos']/1e9:>10.6f}s ({rec['factors']} factors) | "
        f"flint {per_call*1e6:>10.2f} µs ({n_irr} factors)",
    )

OUT.write_text("\n".join(json.dumps(r) for r in rows) + "\n")
print(f"\nWrote {OUT}")
