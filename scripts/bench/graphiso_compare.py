#!/usr/bin/env python3
"""Compare an explicit baseline and candidate on the same named cactus corpus.

Reports candidate/baseline time ratios separately from changed traversal counts.
This reads measurements; it does not repeat runs or choose a favorable sample.
Source, host and trial provenance remain in the supplied measurements' metadata.
"""
# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison

from __future__ import annotations

import argparse
from collections import defaultdict
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.graphiso_archive import normalize  # noqa: E402


def load(path: Path, column: str) -> dict:
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        row = normalize(json.loads(line))
        key = row["family"], row["name"], row["n"]
        if not isinstance(key[0], str) or not isinstance(key[1], str):
            raise ValueError(f"{path}: invalid case name")
        if key in rows:
            raise ValueError(f"{path}: duplicate instance {key}")
        for field in ["n", "nodes", column]:
            if type(row.get(field)) is not int or row[field] <= 0:
                raise ValueError(f"{path}: {key}: invalid {field}")
        rows[key] = row
    if not rows:
        raise ValueError(f"{path}: no measurements")
    return rows


def compare(baseline: dict, candidate: dict, column: str) -> tuple[list, list]:
    if baseline.keys() != candidate.keys():
        raise ValueError("incompatible corpora: family, case name and vertex count must match exactly")
    ratios = defaultdict(list)
    changed = []
    for key, before in baseline.items():
        after = candidate[key]
        ratios[key[0]].append(after[column] / before[column])
        if before["nodes"] != after["nodes"]:
            changed.append((key[1], before["nodes"], after["nodes"]))
    return [(family, len(rs), math.exp(sum(map(math.log, rs)) / len(rs)), max(rs))
            for family, rs in sorted(ratios.items())], sorted(changed)


def provenance(path: Path, rows: dict, column: str) -> str:
    fields = sorted({row["search_column"] for row in rows.values()}) if column == "search_ns" else [column]
    meta = path.with_suffix(".meta.json")
    detail = json.dumps(json.loads(meta.read_text()), sort_keys=True) if meta.exists() else "no sibling metadata; verify source and host separately"
    return f"{path}\n  Recorded columns: {', '.join(fields)}\n  Provenance: {detail}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--column", choices=("search_ns", "fast_ns"), default="search_ns")
    parser.add_argument("--require-same-nodes", action="store_true")
    args = parser.parse_args()
    try:
        before, after = load(args.baseline, args.column), load(args.candidate, args.column)
        table, changed = compare(before, after, args.column)
        print(f"Baseline: {provenance(args.baseline, before, args.column)}\nCandidate: {provenance(args.candidate, after, args.column)}\nOperation: {args.column}\n")
        print("| Family | Cases | Mean time ratio | Worst time ratio |\n|---|---:|---:|---:|")
        for family, count, mean, worst in table:
            print(f"| {family} | {count} | {mean:.4f} | {worst:.4f} |")
        print(f"\nChanged node counts: {len(changed)} / {len(before)}")
        for name, a, b in changed:
            print(f"  {name}: {a} -> {b}")
        if args.require_same_nodes and changed:
            return 1
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"search comparison failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
