#!/usr/bin/env python3
"""Plot Lean LLL vs fpylll on the random-bounded ladder."""
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

rows = [
    json.loads(l)
    for l in Path("/tmp/lll-merged.jsonl").read_text().splitlines()
    if l.strip()
]
rows.sort(key=lambda r: r["n"])

dim = [r["n"] for r in rows]
lean = [r["lean_seconds"] for r in rows]
fpyl = [r["fpylll_seconds"] for r in rows]
ratio = [a / b for a, b in zip(lean, fpyl)]

fig, ax = plt.subplots(figsize=(9, 6))

ax.plot(dim, lean, "o-", color="C0", label="hex (Lean, lllUnchecked)", markersize=7)
ax.plot(dim, fpyl, "s-", color="C1", label="fpylll (LLL.reduction, δ=0.75)", markersize=6)

ax.set_yscale("log")
ax.set_xlabel("lattice dimension n  (n×n random-bounded triangular basis, entries in [-30,30])")
ax.set_ylabel("wall time per LLL reduction (seconds, log scale)")
ax.set_title("LLL: hex (Lean) vs fpylll")
ax.grid(True, which="both", linestyle="--", linewidth=0.4, alpha=0.5)
ax.legend(loc="upper left")

out = Path("/tmp/lll-lean-vs-fpylll.png")
fig.tight_layout()
fig.savefig(out, dpi=140)
print(f"wrote {out}")
print(f"ratio range: {min(ratio):.0f}× to {max(ratio):.0f}×")
