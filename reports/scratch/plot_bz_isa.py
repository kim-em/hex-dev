#!/usr/bin/env python3
"""Plot hex (Lean) vs Isabelle (verified Haskell extraction) on the
split-linear BZ ladder.  Optionally also overlay FLINT for context."""
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

lean = {
    json.loads(l)["degree"]: json.loads(l)
    for l in Path("/tmp/bz-merged.jsonl").read_text().splitlines()
    if l.strip()
}
isa = {
    json.loads(l)["degree"]: json.loads(l)
    for l in Path("/tmp/bz-isabelle-times.jsonl").read_text().splitlines()
    if l.strip()
}

degrees = sorted(set(lean) & set(isa))

fig, ax = plt.subplots(figsize=(9, 6))

lean_full = [(d, lean[d]["lean_seconds"]) for d in degrees if lean[d]["lean_factors"] == d]
lean_part = [(d, lean[d]["lean_seconds"]) for d in degrees if lean[d]["lean_factors"] != d]
isa_pts   = [(d, isa[d]["isa_nanos"] / 1e9) for d in degrees]

if lean_full:
    xs, ys = zip(*lean_full)
    ax.plot(xs, ys, "o-", color="C0", label="hex (Lean), fully refined", markersize=7)
if lean_part:
    xs, ys = zip(*lean_part)
    ax.plot(xs, ys, "x", color="C0", label="hex (Lean), under-refined (fewer factors)", markersize=9, mew=2)

xs, ys = zip(*isa_pts)
ax.plot(xs, ys, "D-", color="C2", label="Isabelle/AFP (extracted Haskell, GHC -O2)", markersize=6)

ax.set_yscale("log")
ax.set_xlabel("input degree  (input is $(x-1)(x-2)\\cdots(x-n)$)")
ax.set_ylabel("wall time per factorization (seconds, log scale)")
ax.set_title("Integer poly factorization: hex (Lean) vs Isabelle/AFP")
ax.grid(True, which="both", linestyle="--", linewidth=0.4, alpha=0.5)
ax.legend(loc="upper left")

out = Path("/tmp/bz-lean-vs-isabelle.png")
fig.tight_layout()
fig.savefig(out, dpi=140)
print(f"wrote {out}")
