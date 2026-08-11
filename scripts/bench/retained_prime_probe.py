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

# Rows the report tabulates separately, per the issue's reporting request.
REPORTED = {
    "sd5": "sd5 and shifts",
    "sd5_shift1": "sd5 and shifts",
    "sd5_shift2": "sd5 and shifts",
    "sd4": "sd5 and shifts",
    "sd6": "sd5 and shifts",
    "sd5_x_phi11": "SD products",
    "sd5_x_phi45": "SD products",
    "sd4_x_sd4shift1": "SD products",
    "xpow48_minus1": "xpow48/105/120",
    "xpow105_minus1": "xpow48/105/120",
    "xpow120_minus1": "xpow48/105/120",
    "cyclo_phi64_x_phi105": "cyclotomic products",
    "cyclo_phi105_x_phi128": "cyclotomic products",
    "cyclo_phi128_x_phi165": "cyclotomic products",
    "wilkinson_40": "Wilkinson",
    "wilkinson_48": "Wilkinson",
    "wilkinson_56": "Wilkinson",
    "cyclo_phi17": "easy controls",
    "cyclo_phi41": "easy controls",
    "legendre_P30": "easy controls",
    "chebyshev_T24": "easy controls",
}


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


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--names", help="comma-separated corpus instances")
    parser.add_argument("--output", required=True)
    parser.add_argument("--service", default=str(SERVICE))
    args = parser.parse_args(argv[1:])

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
            "reported": REPORTED.get(name),
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
                "actedPeeledFactorDegrees": result["actedPeeledFactorDegrees"],
                "residualDegree": result["residualDegree"],
                "actedResidualDegree": result["actedResidualDegree"],
                "actedDecline": result["actedDecline"],
                "sameOutcome": (
                    result["peeledFactorDegrees"]
                    == result["actedPeeledFactorDegrees"]
                    and result["residualDegree"] == result["actedResidualDegree"]
                    and result["decline"] == result["actedDecline"]),
                "plainNanos": [s["nanos"] for s in result["plainSpans"]],
                "countNanos": [s["nanos"] for s in result["countSpans"]],
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

    searched = [r for r in rows if r.get("summary")]
    with_probe = [r for r in searched if r["summary"]["retainedProbeCount"]]
    removing = [r for r in with_probe if r["summary"]["removed"]]
    plain = median([n for r in searched for n in r["plainNanos"]])
    count = median([n for r in searched for n in r["countNanos"]])
    act = median([n for r in searched for n in r["actNanos"]])
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
              f" -> {median(row['actNanos']):.0f} ns")
    print(f"median peel span: plain {plain:.0f} ns, counting {count:.0f} ns, "
          f"acting {act:.0f} ns")
    print(f"arms disagree on: {disagree if disagree else 'no row'}")
    return 0 if not disagree else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
