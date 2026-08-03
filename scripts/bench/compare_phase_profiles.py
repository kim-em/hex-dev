#!/usr/bin/env python3
"""Compare two `factor_phase_profile.py` records row by row (issue #9142).

Prints the Hensel-lift time, total profiled time, end-to-end median, and
allocation counts of a baseline record against an after record, with the
per-row ratios. Both records must cover the same corpus.

Run::

    python3 scripts/bench/compare_phase_profiles.py before.json after.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def rows(record: dict) -> dict[str, dict]:
    out = {}
    for result in record["results"]:
        phases = result.get("phase_profile", {}).get("profile", {}).get("phases")
        if not phases:
            continue
        out[result["name"]] = {
            "degree": result["degree"],
            "lift_nanos": phases.get("henselLift", {}).get("nanos"),
            "lift_allocs": phases.get("henselLift", {}).get("smallAllocs"),
            "total_nanos": phases["total"]["nanos"],
            "total_allocs": phases["total"]["smallAllocs"],
            "e2e_nanos": result["end_to_end"].get("median_nanos"),
        }
    return out


def ratio(before, after) -> str:
    if not before or not after:
        return "    n/a"
    return f"{before / after:7.2f}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    args = parser.parse_args()

    before = rows(json.loads(args.before.read_text()))
    after = rows(json.loads(args.after.read_text()))

    header = (f"{'name':24s} {'deg':>4s} {'lift before':>12s} {'lift after':>12s} "
              f"{'x':>7s} {'e2e before':>12s} {'e2e after':>12s} {'x':>7s} "
              f"{'allocs x':>9s}")
    print(header)
    print("-" * len(header))
    for name in sorted(before.keys() & after.keys(),
                       key=lambda n: -(before[n]["lift_nanos"] or 0)):
        b, a = before[name], after[name]
        print(f"{name:24s} {b['degree']:4d} "
              f"{b['lift_nanos'] or 0:12d} {a['lift_nanos'] or 0:12d} "
              f"{ratio(b['lift_nanos'], a['lift_nanos'])} "
              f"{b['e2e_nanos'] or 0:12d} {a['e2e_nanos'] or 0:12d} "
              f"{ratio(b['e2e_nanos'], a['e2e_nanos'])} "
              f"{ratio(b['total_allocs'], a['total_allocs'])}")
    missing = (before.keys() ^ after.keys())
    if missing:
        print(f"\nrows in only one record: {sorted(missing)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
