#!/usr/bin/env python3
"""Paired-difference tables over the packed Berlekamp ladder (issue #9166).

`factor_phase_profile.py` keeps every ladder rung's reduction per repeat in
`reduceNanosSamples`, and runs the rungs in alternating directions within one
process, so a difference between two rungs can be taken *within* each repeat and
merged by median. This script prints those paired differences, and -- given two
records -- the unpaired before/after comparison of a single rung across runs.

Run::

    python3 scripts/bench/packed_ladder_diff.py RECORD.json
    python3 scripts/bench/packed_ladder_diff.py --diff mirrored,hoistedPivotRow RECORD.json
    python3 scripts/bench/packed_ladder_diff.py --rung integrated BEFORE.json AFTER.json

A paired range that crosses zero means the protocol does not resolve that effect
on that row; the range is printed rather than rounded away.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import statistics


def ladders(record: dict) -> dict[str, dict]:
    """Instance name -> its `packedLadder` block, for rows that have one."""
    out: dict[str, dict] = {}
    for row in record.get("kernels", []):
        ladder = (row.get("kernel") or {}).get("kernel", {}).get("packedLadder")
        if ladder:
            out[row["name"]] = ladder
    return out


def label(record: dict, name: str) -> str:
    """Mark the control instances the phase-profile driver distinguishes."""
    for row in record.get("results", []):
        if row["name"] == name and not row.get("representative", True):
            return f"`{name}` (control)"
    return f"`{name}`"


def duration(nanos: float) -> str:
    if abs(nanos) >= 1e6:
        return f"{nanos / 1e6:.3f} ms"
    if abs(nanos) >= 1e3:
        return f"{nanos / 1e3:.3f} us"
    return f"{nanos:.0f} ns"


def samples(ladder: dict, rung: str) -> list[int]:
    block = ladder.get(rung)
    if block is None:
        raise SystemExit(f"no rung {rung!r}; have {sorted(ladder)}")
    return block["reduceNanosSamples"]


def paired(record: dict, left: str, right: str) -> None:
    print(f"| instance | `{left}` | `{right}` | "
          f"`{left} - {right}` (paired median) | paired range | share of `{left}` |")
    print("|---|---:|---:|---:|---:|---:|")
    for name, ladder in ladders(record).items():
        a, b = samples(ladder, left), samples(ladder, right)
        diffs = [x - y for x, y in zip(a, b)]
        med = statistics.median(diffs)
        base = statistics.median(a)
        share = f"{100 * med / base:.1f}%" if base else "n/a"
        print(f"| {label(record, name)} | {duration(base)} | "
              f"{duration(statistics.median(b))} | {duration(med)} | "
              f"{duration(min(diffs))} to {duration(max(diffs))} | {share} |")


def across(before: dict, after: dict, rung: str) -> None:
    print(f"| instance | `{rung}` before | `{rung}` after | after/before | "
          f"before range | after range |")
    print("|---|---:|---:|---:|---:|---:|")
    lb, la = ladders(before), ladders(after)
    for name in lb:
        if name not in la:
            continue
        b, a = samples(lb[name], rung), samples(la[name], rung)
        mb, ma = statistics.median(b), statistics.median(a)
        ratio = f"{ma / mb:.2f}x" if mb else "n/a"
        print(f"| {label(after, name)} | {duration(mb)} | {duration(ma)} | "
              f"{ratio} | {duration(min(b))} to {duration(max(b))} | "
              f"{duration(min(a))} to {duration(max(a))} |")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("records", type=Path, nargs="+",
                   help="one record for --diff, two (before, after) for --rung")
    p.add_argument("--diff", default="mirrored,hoistedPivotRow",
                   help="comma-separated rung pair to difference within one "
                        "record (default mirrored,hoistedPivotRow)")
    p.add_argument("--rung", default=None,
                   help="rung to compare across two records instead")
    args = p.parse_args()

    loaded = [json.loads(path.read_text()) for path in args.records]
    if args.rung:
        if len(loaded) != 2:
            raise SystemExit("--rung needs exactly two records: before after")
        across(loaded[0], loaded[1], args.rung)
    else:
        if len(loaded) != 1:
            raise SystemExit("--diff needs exactly one record")
        left, right = args.diff.split(",")
        paired(loaded[0], left, right)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
