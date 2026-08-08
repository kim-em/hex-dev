#!/usr/bin/env python3
"""Exact cactus ranks around the Hex / Isabelle BZ crossover (issue #9127).

A cactus curve sorts each system's *own* solved instances by time, so rank `k`
names a different instance for each system. Comparing two systems therefore has
two distinct readings, and a report that blurs them is wrong:

* the **cumulative-rank** reading — "how much total time did each system need to
  solve its own easiest `k` instances" — which is what the cactus plots show;
* the **paired-testcase** reading — "on the instance Hex ranks `k`-th, what did
  the other system cost" — which is what an attribution argument needs.

This tool prints both, over the same records and the same record-selection rule
the cactus figures use (`scripts/plots/hexbz_sweep_data.py`), so the tables in
the performance report and the committed SVGs cannot drift apart.

Run::

    python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "plots"))

from hexbz_sweep_data import (  # noqa: E402
    CURRENT_SYSTEMS,
    ROOT,
    corpus_sha256,
    default_sweep_paths,
    load_corpus,
    merge_reports,
)


def fmt_seconds(value: "float | None") -> str:
    if value is None:
        return "--"
    if value >= 1:
        return f"{value:.3f} s"
    if value >= 1e-3:
        return f"{value * 1e3:.3f} ms"
    return f"{value * 1e6:.3f} us"


def solved_ranking(results, system, names):
    """`[(name, seconds)]` for one system's solved instances, fastest first.

    Ties break on the instance name so the ranking is reproducible from the
    record rather than depending on Python's input order.
    """
    rows = [(r["name"], r["median_nanos"] / 1e9) for r in results
            if r["system"] == system and r["name"] in names
            and r["status"] == "ok" and r["median_nanos"] is not None]
    return sorted(rows, key=lambda row: (row[1], row[0]))


def by_name(results, system):
    return {r["name"]: r for r in results if r["system"] == system}


def cumulative(ranking):
    out, acc = [], 0.0
    for name, seconds in ranking:
        acc += seconds
        out.append((name, seconds, acc))
    return out


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--sweep", type=Path, nargs="+", default=None,
                   help="explicit sweep records (default: the committed records "
                        "for the current corpus, newest measurement per system)")
    p.add_argument("--lo", type=int, default=118, help="first rank (inclusive)")
    p.add_argument("--hi", type=int, default=144, help="last rank (inclusive)")
    p.add_argument("--reference", default="hex-factor",
                   help="system whose ranks index the paired table")
    p.add_argument("--against", default="isabelle-bz",
                   help="system paired against the reference")
    p.add_argument("--set", dest="instance_set", choices=("combined", "all"),
                   default="combined",
                   help="corpus subset: the combined mix-doctrine mixture "
                        "(default, what the combined cactus plots) or all rows")
    p.add_argument("--json", type=Path, default=None,
                   help="also write the tables as JSON")
    args = p.parse_args()

    paths = args.sweep or default_sweep_paths()[0]
    if not paths:
        raise SystemExit("no sweep records found for the current corpus")
    results, systems, provenance, cutoffs = merge_reports(paths)
    if args.sweep is None:
        results = [r for r in results if r["system"] in CURRENT_SYSTEMS]
        systems = [s for s in systems if s in CURRENT_SYSTEMS]

    corpus = load_corpus()
    if args.instance_set == "combined":
        names = {n for n, i in corpus.items() if i["combined"]}
    else:
        names = set(corpus)

    for system in (args.reference, args.against):
        if system not in systems:
            raise SystemExit(f"no current measurement for {system}")

    ref_rank = cumulative(solved_ranking(results, args.reference, names))
    against_rank = cumulative(solved_ranking(results, args.against, names))
    against_rows = by_name(results, args.against)

    lo, hi = args.lo, args.hi
    print(f"# Cactus ranks {lo}--{hi} ({args.instance_set} mixture, "
          f"{len(names)} instances)")
    print()
    print(f"corpus sha256 `{corpus_sha256()}`")
    print(f"cutoff {'/'.join(f'{c}s' for c in sorted(cutoffs))}")
    print("record provenance (newest measurement per system):")
    for system in systems:
        fname, iso, cutoff = provenance[system]
        print(f"  - `{system}`: {fname} ({iso}, cutoff {cutoff}s)")
    print()
    print(f"{args.reference} solved {len(ref_rank)} of {len(names)}; "
          f"{args.against} solved {len(against_rank)}.")
    print()

    print("## Cumulative-rank view (independently sorted, as plotted)")
    print()
    print(f"| rank | {args.reference} instance | time | cumulative | "
          f"{args.against} instance | time | cumulative |")
    print("|---:|---|---:|---:|---|---:|---:|")
    rank_rows = []
    for rank in range(lo, hi + 1):
        left = ref_rank[rank - 1] if rank <= len(ref_rank) else None
        right = against_rank[rank - 1] if rank <= len(against_rank) else None
        rank_rows.append({
            "rank": rank,
            args.reference: None if left is None else
                {"name": left[0], "seconds": left[1], "cumulative_seconds": left[2]},
            args.against: None if right is None else
                {"name": right[0], "seconds": right[1], "cumulative_seconds": right[2]},
        })
        cells = []
        for entry in (left, right):
            if entry is None:
                cells += ["--", "--", "--"]
            else:
                cells += [f"`{entry[0]}`", fmt_seconds(entry[1]),
                          fmt_seconds(entry[2])]
        print(f"| {rank} | " + " | ".join(cells) + " |")
    print()

    print("## Paired-testcase view (same instance, both systems)")
    print()
    print(f"| {args.reference} rank | instance | degree | {args.reference} | "
          f"{args.against} | {args.against} / {args.reference} |")
    print("|---:|---|---:|---:|---:|---:|")
    paired_rows = []
    for rank in range(lo, hi + 1):
        if rank > len(ref_rank):
            continue
        name, seconds, _ = ref_rank[rank - 1]
        other = against_rows.get(name)
        other_ok = other is not None and other["status"] == "ok" \
            and other["median_nanos"] is not None
        other_seconds = other["median_nanos"] / 1e9 if other_ok else None
        status = other["status"] if other is not None else "absent"
        ratio = (other_seconds / seconds) if (other_ok and seconds) else None
        paired_rows.append({
            "rank": rank, "name": name, "degree": corpus[name]["degree"],
            "reference_seconds": seconds,
            "against_seconds": other_seconds,
            "against_status": status,
            "ratio": ratio,
        })
        rendered = fmt_seconds(other_seconds) if other_ok else status
        print(f"| {rank} | `{name}` | {corpus[name]['degree']} | "
              f"{fmt_seconds(seconds)} | {rendered} | "
              f"{'--' if ratio is None else f'{ratio:.2f}x'} |")

    if args.json is not None:
        payload = {
            "corpus_sha256": corpus_sha256(),
            "instance_set": args.instance_set,
            "instances": len(names),
            "reference": args.reference,
            "against": args.against,
            "lo": lo,
            "hi": hi,
            "provenance": {s: {"record": provenance[s][0],
                               "timestamp_iso": provenance[s][1],
                               "cutoff_seconds": provenance[s][2]}
                           for s in systems},
            "solved": {s: len(solved_ranking(results, s, names)) for s in systems},
            "cumulative_rank_view": rank_rows,
            "paired_testcase_view": paired_rows,
        }
        args.json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"\nwrote {args.json.relative_to(ROOT)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
