#!/usr/bin/env python3
"""For each LLL basis in /tmp/lll-lean-times.jsonl, time the verified
extracted-Haskell `svp_verified` binary. Each measurement launches the
binary ONCE and pipes R copies of the same basis through stdin to
amortize the ~20ms process startup cost."""
import json
import subprocess
import time
from pathlib import Path

LEAN = Path("/tmp/lll-lean-times.jsonl")
OUT = Path("/tmp/lll-isabelle-times.jsonl")
BIN = Path("/Users/kim/projects/lean/hex/.cache/oracles/lll-isabelle/src/experiments/svp_verified")


def measure_overhead(reps=20):
    """How long does it take to launch the binary and pipe `reps`
    one-row trivial inputs through it. Subtract this from per-input cost."""
    trivial = "[[1,0,0],[0,1,0],[0,0,1]]\n" * reps
    t0 = time.perf_counter()
    subprocess.run([str(BIN)], input=trivial, capture_output=True, text=True, check=True, timeout=60)
    return (time.perf_counter() - t0) / reps  # per-input on a trivial basis


def time_one(basis, target_seconds: float = 0.6, min_reps: int = 4, max_reps: int = 64):
    basis_line = repr(basis)
    reps = min_reps
    while True:
        input_data = (basis_line + "\n") * reps
        t0 = time.perf_counter()
        r = subprocess.run(
            [str(BIN)], input=input_data, capture_output=True, text=True, check=True, timeout=300,
        )
        elapsed = time.perf_counter() - t0
        per_call = elapsed / reps
        if elapsed >= target_seconds or reps >= max_reps:
            sq = r.stdout.strip().splitlines()[-1].strip()
            return per_call, sq, reps
        reps *= 2


# Establish a "trivial input" baseline that includes process start +
# the parser + JIT warmup.  We subtract it from each measurement,
# clamping to zero.
overhead = measure_overhead()
print(f"[svp_verified startup baseline: {overhead*1e3:.2f} ms / input on trivial 3x3]")

rows = []
for line in LEAN.read_text().splitlines():
    line = line.strip()
    if not line.startswith("{"):
        continue
    rec = json.loads(line)
    basis = rec["basis"]
    per_call, sq, reps = time_one(basis)
    adjusted = max(per_call - overhead, 0.0)
    rows.append({
        "n": rec["n"],
        "lean_seconds": rec["lean_nanos"] / 1e9,
        "isa_seconds_raw": per_call,
        "isa_seconds": adjusted,
        "isa_overhead_seconds": overhead,
        "isa_sq_norm": sq,
        "isa_reps": reps,
    })
    print(
        f"n {rec['n']:>4} | lean {rec['lean_nanos']/1e9:>10.6f}s | "
        f"isabelle raw {per_call*1e3:>8.2f}ms  → minus startup = {adjusted*1e3:>8.2f}ms  (sq={sq})",
        flush=True,
    )

OUT.write_text("\n".join(json.dumps(r) for r in rows) + "\n")
print(f"\nWrote {OUT}")
