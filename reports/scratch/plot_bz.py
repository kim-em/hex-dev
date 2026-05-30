#!/usr/bin/env python3
"""Plot Lean vs FLINT factorization times on the split linear ladder."""
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

rows = [json.loads(l) for l in Path("/tmp/bz-merged.jsonl").read_text().splitlines() if l.strip()]
rows.sort(key=lambda r: r["degree"])

deg = [r["degree"] for r in rows]
lean_full = [(r["degree"], r["lean_seconds"]) for r in rows if r["lean_factors"] == r["degree"]]
lean_part = [(r["degree"], r["lean_seconds"]) for r in rows if r["lean_factors"] != r["degree"]]
flint = [(r["degree"], r["flint_seconds"]) for r in rows]

fig, ax = plt.subplots(figsize=(9, 6))

if lean_full:
    xs, ys = zip(*lean_full)
    ax.plot(xs, ys, "o-", color="C0", label="hex (fully refined)", markersize=7)
if lean_part:
    xs, ys = zip(*lean_part)
    ax.plot(xs, ys, "x", color="C0", label="hex (under-refined, fewer factors)", markersize=9, mew=2)

xs, ys = zip(*flint)
ax.plot(xs, ys, "s-", color="C1", label="FLINT (fmpz_poly.factor)", markersize=6)

ax.set_yscale("log")
ax.set_xlabel("input degree  (input is $(x-1)(x-2)\\cdots(x-n)$)")
ax.set_ylabel("wall time per factorization (seconds, log scale)")
ax.set_title("Integer poly factorization: hex (Lean) vs FLINT")
ax.grid(True, which="both", linestyle="--", linewidth=0.4, alpha=0.5)
ax.legend(loc="upper left")

out = Path("/tmp/bz-lean-vs-flint.png")
fig.tight_layout()
fig.savefig(out, dpi=140)
print(f"wrote {out}")
