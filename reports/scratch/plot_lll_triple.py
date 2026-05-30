#!/usr/bin/env python3
"""LLL triple comparison: hex (Lean) vs Isabelle (AFP svp_verified) vs fpylll."""
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

lean = {
    json.loads(l)["n"]: json.loads(l)
    for l in Path("/tmp/lll-merged.jsonl").read_text().splitlines()
    if l.strip()
}
isa = {
    json.loads(l)["n"]: json.loads(l)
    for l in Path("/tmp/lll-isabelle-times.jsonl").read_text().splitlines()
    if l.strip() and json.loads(l).get("isa_seconds") is not None
}

dims = sorted(set(lean) & set(isa))

xs       = dims
lean_y   = [lean[n]["lean_seconds"] for n in xs]
fpyl_y   = [lean[n]["fpylll_seconds"] for n in xs]
isa_y    = [isa[n]["isa_seconds_raw"] for n in xs]

fig, ax = plt.subplots(figsize=(9, 6))

ax.plot(xs, lean_y, "o-", color="C0", label="hex (Lean, lllUnchecked)", markersize=7)
ax.plot(xs, isa_y,  "D-", color="C2", label="Isabelle/AFP (svp_verified, extracted Haskell)", markersize=6)
ax.plot(xs, fpyl_y, "s-", color="C1", label="fpylll (LLL.reduction)", markersize=6)

ax.set_yscale("log")
ax.set_xlabel("lattice dimension n  (n×n random-bounded triangular basis, entries in [-30,30])")
ax.set_ylabel("wall time per LLL reduction (seconds, log scale)")
ax.set_title("LLL: hex (Lean) vs Isabelle/AFP vs fpylll")
ax.grid(True, which="both", linestyle="--", linewidth=0.4, alpha=0.5)
ax.legend(loc="upper left")

out = Path("/tmp/lll-triple.png")
fig.tight_layout()
fig.savefig(out, dpi=140)
print(f"wrote {out}")

# Print pairwise ratios so we can sanity-check.
print("\nratios (isa / lean, fpylll / lean):")
for n, L, I, F in zip(xs, lean_y, isa_y, fpyl_y):
    print(f"  n={n:>4}: isa/lean={I/L:.2f}x, lean/fpylll={L/F:.1f}x")
