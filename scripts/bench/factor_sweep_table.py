#!/usr/bin/env python3
"""Reproduce the current cross-system factorization tables.

The reader and newest-per-system selection rule are shared with the cactus
plots. Summary medians use the ordinary statistical median. The p10 and p90
entries use the observations at zero-based indices ``n // 10`` and
``(9 * n) // 10`` after sorting.
A paired row is eligible only when each system's measurement is strictly above
ten times that system's own protocol overhead.

Run::

    python3 scripts/bench/factor_sweep_table.py
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from statistics import median
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "plots"))

from hexbz_sweep_data import (  # noqa: E402
    CURRENT_SYSTEMS,
    default_sweep_paths,
    load_corpus,
    merge_reports,
)


SYSTEM_ORDER = (
    "hex-factor",
    "flint",
    "pari",
    "ntl",
    "isabelle-bz",
    "isabelle-lll",
)

SYSTEM_LABEL = {
    "hex-factor": "Hex public factorization",
    "flint": "FLINT 0.9.0",
    "pari": "PARI/GP 2.17.2",
    "ntl": "NTL 11.6.0",
    "isabelle-bz": "Verified Isabelle BZ",
    "isabelle-lll": "Verified Isabelle LLL",
}

FAMILY_LABEL = {
    "chebyshev": "Chebyshev",
    "conway": "Conway",
    "cyclotomic": "Cyclotomic",
    "cyclotomic-products": "Cyclotomic products",
    "laguerre": "Laguerre",
    "legendre": "Legendre",
    "random-products": "Random products",
    "sd-products": "Swinnerton-Dyer products",
    "swinnerton-dyer": "Swinnerton-Dyer",
    "wilkinson": "Wilkinson",
    "hoeij-zimmermann": "Hoeij-Zimmermann",
    "certificate-boundary": "Certificate boundary",
}


def quantile(values: list[float], numerator: int, denominator: int) -> float:
    """The observation at index floor(numerator * n / denominator)."""
    if not values:
        raise ValueError("quantile of an empty sequence")
    ordered = sorted(values)
    index = numerator * len(ordered) // denominator
    return ordered[min(index, len(ordered) - 1)]


def fmt_nanos(value: float) -> str:
    if value >= 1e9:
        return f"{value / 1e9:.3f} s"
    if value >= 1e6:
        return f"{value / 1e6:.3f} ms"
    return f"{value / 1e3:.3f} us"


def rows_by_system(results):
    return {
        system: {row["name"]: row for row in results if row["system"] == system}
        for system in CURRENT_SYSTEMS
    }


def selected_overheads(paths, provenance, systems):
    """Read each selected record's per-system protocol overhead."""
    by_name: dict[str, list[Path]] = {}
    for path in paths:
        by_name.setdefault(path.name, []).append(path)

    overheads = {}
    for system in systems:
        filename, _timestamp, _cutoff = provenance[system]
        matches = by_name.get(filename, [])
        if len(matches) != 1:
            raise SystemExit(
                f"cannot identify selected record {filename!r} for {system}")
        report = json.loads(matches[0].read_text())
        try:
            overheads[system] = report["config"]["per_system_overhead_nanos"][system]
        except (KeyError, TypeError) as error:
            raise SystemExit(
                f"{filename}: missing protocol overhead for {system}") from error
    return overheads


def paired_ratios(reference, other, overheads):
    ratios = []
    for name, left in reference.items():
        right = other.get(name)
        if right is None:
            continue
        left_time = left.get("median_nanos")
        right_time = right.get("median_nanos")
        if (left.get("status") != "ok" or right.get("status") != "ok"
                or left_time is None or right_time is None):
            continue
        if (left_time <= 10 * overheads["hex-factor"]
                or right_time <= 10 * overheads[right["system"]]):
            continue
        ratios.append((name, left_time / right_time))
    return ratios


def print_summary(rows, systems):
    print("## Current summary")
    print()
    print("| System | Answered | Timed out | Median | p90 | Slowest answer |")
    print("|---|---:|---:|---:|---:|---:|")
    for system in SYSTEM_ORDER:
        if system not in systems:
            continue
        solved = [row["median_nanos"] for row in rows[system].values()
                  if row["status"] == "ok" and row["median_nanos"] is not None]
        timed_out = sum(row["status"] == "timeout" for row in rows[system].values())
        unexpected = sorted(
            f"{row['name']}={row['status']}" for row in rows[system].values()
            if row["status"] not in {"ok", "timeout"})
        if unexpected:
            raise SystemExit(
                f"{system}: non-answer statuses are not timeouts: "
                + ", ".join(unexpected))
        print(f"| {SYSTEM_LABEL[system]} | {len(solved)} | {timed_out} | "
              f"{fmt_nanos(median(solved))} | "
              f"{fmt_nanos(quantile(solved, 9, 10))} | "
              f"{fmt_nanos(max(solved))} |")
    print()


def print_pairs(rows, systems, overheads):
    print("## Hex / comparator pairs")
    print()
    print("| Comparator | Eligible pairs | Median | p10 | p90 | Hex wins-losses |")
    print("|---|---:|---:|---:|---:|---:|")
    for system in ("flint", "pari", "ntl", "isabelle-bz", "isabelle-lll"):
        if system not in systems:
            continue
        pairs = paired_ratios(rows["hex-factor"], rows[system], overheads)
        ratios = [ratio for _, ratio in pairs]
        wins = sum(ratio < 1 for ratio in ratios)
        losses = sum(ratio > 1 for ratio in ratios)
        ties = len(ratios) - wins - losses
        split = f"{wins}-{losses}" if ties == 0 else f"{wins}-{losses}-{ties}"
        print(f"| {SYSTEM_LABEL[system]} | {len(ratios)} | "
              f"{median(ratios):.3f}x | {quantile(ratios, 1, 10):.3f}x | "
              f"{quantile(ratios, 9, 10):.3f}x | {split} |")
    print()


def print_families(rows, systems, overheads, corpus):
    if "isabelle-bz" not in systems:
        return
    print("## Hex / verified Isabelle BZ by family")
    print()
    print("| Family | Eligible pairs | Median Hex / Isabelle | Hex wins |")
    print("|---|---:|---:|---:|")
    pairs = paired_ratios(rows["hex-factor"], rows["isabelle-bz"], overheads)
    by_family: dict[str, list[float]] = {}
    for name, ratio in pairs:
        by_family.setdefault(corpus[name]["family"], []).append(ratio)
    unlabelled = {row["family"] for row in corpus.values()} - FAMILY_LABEL.keys()
    if unlabelled:
        raise SystemExit("unlabelled corpus families: " + ", ".join(sorted(unlabelled)))
    for family, label in FAMILY_LABEL.items():
        ratios = by_family.get(family, [])
        if ratios:
            print(f"| {label} | {len(ratios)} | {median(ratios):.3f}x | "
                  f"{sum(ratio < 1 for ratio in ratios)} |")
    print()


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--sweep", type=Path, nargs="+", default=None,
        help="explicit sweep records (default: committed current-corpus records, "
             "newest measurement per system)")
    args = parser.parse_args()

    paths = args.sweep or default_sweep_paths()[0]
    if not paths:
        raise SystemExit("no sweep records found for the current corpus")
    results, systems, provenance, _cutoffs = merge_reports(paths)
    systems = [system for system in systems if system in CURRENT_SYSTEMS]
    results = [row for row in results if row["system"] in systems]
    if "hex-factor" not in systems:
        raise SystemExit("no current Hex factorization measurement")

    print("record provenance (newest measurement per system):")
    for system in systems:
        filename, timestamp, cutoff = provenance[system]
        print(f"  - {system}: {filename} ({timestamp}, cutoff {cutoff}s)")
    print()

    rows = rows_by_system(results)
    overheads = selected_overheads(paths, provenance, systems)
    print_summary(rows, systems)
    print_pairs(rows, systems, overheads)
    print_families(rows, systems, overheads, load_corpus())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
