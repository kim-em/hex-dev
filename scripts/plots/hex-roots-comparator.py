#!/usr/bin/env python3
"""Generate the HexRoots comparator-runtime plot from committed exports.

Draws the Lean `isolateAll?@32` wall-time curve (from the lean-bench export)
alongside the python-flint `fmpz_poly.complex_roots` curve (from the flint
comparator export) for one `phase4.input_families` entry, log-y wall time per
call across the shared seeded degree ladder. Reads the same JSONL/JSON the
Comparator-ratios numbers in reports/hexroots-performance.md cite.

Only the `seeded-dense` family has python-flint data (the process-call
comparator was run on the whole-polynomial driver ladder); MPSolve is
scheduled-only (no data points), and the `wilkinson-linprod` / `refine-fixed`
families carry no external-comparator series, so `--family` accepts only
`seeded-dense`.

Usage:
    python3 scripts/plots/hex-roots-comparator.py --family seeded-dense
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
LEAN_EXPORT = ROOT / "reports/bench-results/hex-roots-b08a66cce522.json"
FLINT_EXPORT = ROOT / "reports/bench-results/hex-roots-flint-b08a66cce522.json"


def lean_isolateall_by_degree() -> dict[int, float]:
    d = json.loads(LEAN_EXPORT.read_text())
    out: dict[int, float] = {}
    for r in d["results"]:
        if r["function"].endswith("runIsolateAll"):
            for t in r["trial_summaries"]:
                out[t["param"]] = t["median_per_call_nanos"] / 1e9
    return out


def flint_by_degree() -> tuple[dict[int, float], float]:
    f = json.loads(FLINT_EXPORT.read_text())
    return {row["degree"]: row["median_s"] for row in f["rows"]}, f["overhead_s"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", default="seeded-dense", choices=["seeded-dense"])
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    hexd = lean_isolateall_by_degree()
    flintd, overhead = flint_by_degree()
    degrees = sorted(set(hexd) & set(flintd))

    fig, ax = plt.subplots(figsize=(7, 4.5))
    ax.plot(degrees, [hexd[d] for d in degrees], "o-", label="hex isolateAll?@32 (Lean, certified)")
    ax.plot(degrees, [max(flintd[d] - overhead, 1e-9) for d in degrees], "s-",
            label="python-flint complex_roots (overhead-adjusted)")
    ax.set_yscale("log")
    ax.set_xlabel("degree n (seed-0xC0FFEE dense integer polynomial)")
    ax.set_ylabel("wall time per call (s)")
    ax.set_title("HexRoots vs python-flint — seeded-dense family (chungus2)")
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
