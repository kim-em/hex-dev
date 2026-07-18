#!/usr/bin/env python3
"""Generate the HexRoots comparator-runtime plot from committed exports.

Draws the historical Lean `runIsolateParam` diagnostic wall-time curve
alongside the python-flint `fmpz_poly.complex_roots` curve (from the flint
comparator export) for one `phase4.input_families` entry, log-y wall time per
call across the shared fixed-separation degree ladder (degrees 4–10; the
distinct fixed `runIsolateAll` point is report-only). Reads the same JSON the
Comparator-ratios numbers in
reports/hex-roots-performance.md cite.

python-flint is scoped to the whole-polynomial isolation surface; the internal
kernel families are declared `no-comparable-surface-in-named-comparator`.

Usage:
    python3 scripts/plots/hex-roots-comparator.py --family fixed-separation-product
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hex-roots-comparator"
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
LEAN_EXPORT = ROOT / "reports/bench-results/hex-roots-isolate-diagnostic-round5.json"
FLINT_EXPORT = ROOT / "reports/bench-results/hex-roots-flint-round5.json"


def lean_isolate_by_degree() -> dict[int, float]:
    d = json.loads(LEAN_EXPORT.read_text())
    return {row["degree"]: row["median_s"] for row in d["rows"]}


def flint_by_degree() -> tuple[dict[int, float], float]:
    f = json.loads(FLINT_EXPORT.read_text())
    return {row["degree"]: row["median_s"] for row in f["rows"]}, f["overhead_s"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", default="fixed-separation-product",
                    choices=["fixed-separation-product"])
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    hexd = lean_isolate_by_degree()
    flintd, overhead = flint_by_degree()
    degrees = sorted(set(hexd) & set(flintd))

    fig, ax = plt.subplots(figsize=(7, 4.5))
    ax.plot(degrees, [hexd[d] for d in degrees], "o-",
            label="hex isolate diagnostic (Lean, certified)")
    ax.plot(degrees, [max(flintd[d] - overhead, 1e-9) for d in degrees], "s-",
            label="python-flint complex_roots (overhead-adjusted)")
    ax.set_yscale("log")
    ax.set_xlabel("degree n (fixed-separation product)")
    ax.set_ylabel("wall time per call (s)")
    ax.set_title("HexRoots vs python-flint — fixed-separation family (chungus2)")
    ax.legend()
    ax.grid(True, which="both", alpha=0.3)
    out = Path(args.out) if args.out else ROOT / f"reports/figures/hex-roots-comparator-{args.family}.svg"
    out.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out)
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
