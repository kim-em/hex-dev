#!/usr/bin/env python3
"""Counterfactual: would the retained good primes reject any candidate degree?

`hexbz_factor_service --entry retainedPrimeProbe` mirrors the production
proposal traversal leaf for leaf and, at every leaf that passes the production
selected-support degree check, asks each *other* good prime the planner
retained whether that degree is a subset sum of its own modular factor degrees.
The answers are counted and discarded, so the mirrored traversal visits exactly
the leaves production visits.

This is the measurement gate of issue #9153. Production changes only if the
intersection removes a material fraction of the post-degree-check leaves on
some row; a documented no-go is the other admissible outcome.

This is a diagnostic driver, not a benchmark harness: the merge-gating suites
do not run it.

Run::

    lake build hexbz_factor_service
    python3 scripts/bench/retained_prime_probe.py \\
        --output reports/bench-results/hexbz-retained-prime-probe.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"

# The groups the issue asks to report separately. A row belongs to the first
# group that claims it, so the three named `x^n - 1` rows are reported apart
# from the rest of the cyclotomic products they live among in the corpus.
GROUPS = (
    ("sd5 and shifts", {"family": "swinnerton-dyer"}),
    ("SD products", {"family": "sd-products"}),
    ("xpow48/105/120",
     {"names": ("xpow48_minus1", "xpow105_minus1", "xpow120_minus1")}),
    ("cyclotomic products", {"family": "cyclotomic-products"}),
    ("Hoeij-Zimmermann", {"family": "hoeij-zimmermann"}),
    ("Wilkinson", {"family": "wilkinson"}),
    ("easy controls", {"family": None}),
)

# Groups small enough to list row by row rather than only in aggregate.
PER_ROW_GROUPS = (
    "sd5 and shifts", "SD products", "xpow48/105/120",
    "Hoeij-Zimmermann", "Wilkinson",
)


def group_of(row: dict) -> str:
    for name, rule in GROUPS:
        if rule.get("names") and row["name"] in rule["names"]:
            return name
        if rule.get("family") and row["family"] == rule["family"]:
            return name
    return "easy controls"


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, text=True,
                          capture_output=True, check=True).stdout.strip()


def load_corpus() -> dict:
    corpus = {}
    for line in CORPUS.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            corpus[row["name"]] = row
    return corpus


def summarize(result: dict) -> dict:
    """Whole-row totals plus the level that loses the most leaves."""
    totals = result.get("totals") or {}
    degree_survivors = totals.get("degreeSurvivors", 0)
    intersection = totals.get("intersectionSurvivors", 0)
    probes = totals.get("probeSurvivors") or []
    removed = degree_survivors - intersection if probes else 0
    worst = None
    for level in result.get("levels") or []:
        stats = level["stats"]
        d = stats["degreeSurvivors"]
        i = stats["intersectionSurvivors"]
        if not stats["probeSurvivors"]:
            continue
        if d and (worst is None or d - i > worst["removed"]):
            worst = {
                "residual": level["residual"],
                "cardinality": level["cardinality"],
                "degreeSurvivors": d,
                "intersectionSurvivors": i,
                "removed": d - i,
            }
    return {
        "retainedProbeCount": result.get("retainedProbeCount", 0),
        "degreeSurvivors": degree_survivors,
        "intersectionSurvivors": intersection,
        "removed": removed,
        "removedFraction": (removed / degree_survivors) if degree_survivors else 0.0,
        "perProbeSurvivors": probes,
        "worstLevel": worst,
    }


def median(values: list[int]) -> float:
    ordered = sorted(values)
    mid = len(ordered) // 2
    if not ordered:
        return 0.0
    if len(ordered) % 2:
        return float(ordered[mid])
    return (ordered[mid - 1] + ordered[mid]) / 2


def emit_tables(rows: list[dict]) -> None:
    """Print the grouped markdown tables the report quotes."""
    searched = [r for r in rows if r.get("summary")]
    print("| group | rows | retaining a prime | with a rejectable degree |"
          " leaves | passing the degree check | passing every retained prime |"
          " median predicate/plain | worst predicate/plain |")
    print("|---|---|---|---|---|---|---|---|---|")
    for name, _ in GROUPS:
        members = [r for r in searched if r["group"] == name]
        if not members:
            continue
        ratios = [median(r["predicateNanos"]) / median(r["plainNanos"])
                  for r in members if median(r["plainNanos"])]
        print(f"| {name} | {len(members)} |"
              f" {sum(1 for r in members if r['summary']['retainedProbeCount'])} |"
              f" {sum(1 for r in members if r['rejectableDegrees'])} |"
              f" {sum(r['totals']['leaves'] for r in members)} |"
              f" {sum(r['totals']['degreeSurvivors'] for r in members)} |"
              f" {sum(r['totals']['intersectionSurvivors'] for r in members)} |"
              f" {median(ratios):.3f} | {max(ratios):.3f} |")
    for name in PER_ROW_GROUPS:
        members = [r for r in searched if r["group"] == name]
        if not members:
            continue
        print()
        print(f"#### {name}")
        print()
        print("| row | degree | retained primes | leaves |"
              " passing the degree check | passing every retained prime |"
              " rejectable degrees | plain | predicate |")
        print("|---|---|---|---|---|---|---|---|---|")
        for r in sorted(members, key=lambda r: r["name"]):
            t = r["totals"]
            print(f"| `{r['name']}` | {r['degree']} |"
                  f" {r['summary']['retainedProbeCount']} | {t['leaves']} |"
                  f" {t['degreeSurvivors']} | {t['intersectionSurvivors']} |"
                  f" {len(r['rejectableDegrees'])} |"
                  f" {median(r['plainNanos']) / 1000:.1f} µs |"
                  f" {median(r['predicateNanos']) / 1000:.1f} µs |")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--names", help="comma-separated corpus instances")
    parser.add_argument("--output", required=True)
    parser.add_argument("--service", default=str(SERVICE))
    parser.add_argument("--tables", action="store_true",
                        help="print the report's grouped markdown tables")
    parser.add_argument("--from-record",
                        help="tabulate an existing record instead of measuring")
    args = parser.parse_args(argv[1:])

    if args.from_record:
        emit_tables(json.loads(Path(args.from_record).read_text())["rows"])
        return 0

    corpus = load_corpus()
    names = tuple(args.names.split(",")) if args.names else tuple(corpus)
    missing = [name for name in names if name not in corpus]
    if missing:
        raise SystemExit(f"not in the corpus: {', '.join(missing)}")

    request = "".join(
        json.dumps({"coeffs": corpus[name]["coeffs"]}) + "\n" for name in names)
    completed = subprocess.run(
        [args.service, "--entry", "retainedPrimeProbe"], input=request,
        text=True, capture_output=True, check=True)
    replies = [json.loads(line) for line in completed.stdout.splitlines()
               if line.strip()]
    if len(replies) != len(names):
        raise SystemExit(f"expected {len(names)} replies, got {len(replies)}")

    rows = []
    for name, reply in zip(names, replies):
        result = reply.get("result") or {}
        row = {
            "name": name,
            "family": corpus[name]["family"],
            "degree": corpus[name]["degree"],
            "group": group_of({"name": name, "family": corpus[name]["family"]}),
            "goodPrimeFound": result.get("goodPrimeFound", False),
        }
        if result.get("goodPrimeFound"):
            row.update({
                "selectedPrime": result["selectedPrime"],
                "probes": result["probes"],
                "liftedFactorCount": result["liftedFactorCount"],
                "decline": result["decline"],
                "summary": summarize(result),
                "totals": result["totals"],
                "levels": result["levels"],
                "actedTotals": result["actedTotals"],
                "rejectableDegrees": result["rejectableDegrees"],
                "peeledFactorDegrees": result["peeledFactorDegrees"],
                "residualDegree": result["residualDegree"],
                "remainingSupport": result["remainingSupport"],
                "remainingBudget": result["remainingBudget"],
                "sameOutcome": result["sameOutcome"],
                "plainNanos": [s["nanos"] for s in result["plainSpans"]],
                "countNanos": [s["nanos"] for s in result["countSpans"]],
                "predicateNanos": [s["nanos"] for s in result["predicateSpans"]],
                "actNanos": [s["nanos"] for s in result["actSpans"]],
            })
        rows.append(row)

    record = {
        "schema": "hexbz-retained-prime-probe/1",
        "env": {
            "git_commit": git("rev-parse", "HEAD"),
            "git_dirty": bool(git("status", "--porcelain")),
            "corpus_sha256": hashlib.sha256(CORPUS.read_bytes()).hexdigest(),
        },
        "rows": rows,
    }
    Path(args.output).write_text(json.dumps(record, indent=1, sort_keys=True) + "\n")

    if args.tables:
        emit_tables(rows)
    searched = [r for r in rows if r.get("summary")]
    with_probe = [r for r in searched if r["summary"]["retainedProbeCount"]]
    removing = [r for r in with_probe if r["summary"]["removed"]]
    plain = median([n for r in searched for n in r["plainNanos"]])
    count = median([n for r in searched for n in r["countNanos"]])
    act = median([n for r in searched for n in r["predicateNanos"]])
    disagree = [r["name"] for r in searched if not r["sameOutcome"]]
    rejectable = [r for r in with_probe if r["rejectableDegrees"]]
    print(f"wrote {args.output}")
    print(f"rows measured {len(rows)}, rows reaching a plan {len(searched)}, "
          f"rows with a retained other prime {len(with_probe)}")
    print(f"rows whose retained prime can reject some selected-prime degree: "
          f"{len(rejectable)}")
    print(f"rows where the intersection removes a visited leaf: {len(removing)}")
    for row in sorted(removing, key=lambda r: -r["summary"]["removedFraction"]):
        summary = row["summary"]
        acted = row["actedTotals"]
        print(f"  {row['name']}: {summary['removed']}/{summary['degreeSurvivors']}"
              f" = {summary['removedFraction']:.1%};"
              f" trailing survivors {row['totals']['trailingSurvivors']}"
              f" -> {acted['trailingSurvivors']},"
              f" constructed {row['totals']['constructed']}"
              f" -> {acted['constructed']},"
              f" exact divisions {row['totals']['exactDivisions']}"
              f" -> {acted['exactDivisions']};"
              f" peel {median(row['plainNanos']):.0f} ns"
              f" -> {median(row['predicateNanos']):.0f} ns")
    print(f"median peel span: plain {plain:.0f} ns, counting {count:.0f} ns, "
          f"predicate {act:.0f} ns")
    print(f"arms disagree on: {disagree if disagree else 'no row'}")
    return 0 if not disagree else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
