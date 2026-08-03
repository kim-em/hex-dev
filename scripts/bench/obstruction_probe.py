#!/usr/bin/env python3
"""Counted before/after probe of the word-prime divisibility obstruction.

`hexbz_factor_service --entry obstructionProbe` runs the counted recombination
mirror four times on one input -- filtered (the production leaf), unfiltered,
filtered, unfiltered -- and reports every stage-counter set and every span. This
driver feeds it a named subset of the committed corpus and writes one durable
JSON record, so the rejection counts quoted in
`reports/hexbz-modular-obstruction.md` are reproducible rather than asserted.

Rows that answer through the proposal or lattice tier never enter the
head-forced traversal and carry no obstruction block; they are recorded with
their method so the omission is visible rather than silent.

This is a diagnostic driver, not a benchmark harness: it emits counters and raw
spans for the report, and the merge-gating suites do not run it.

Run::

    lake build hexbz_factor_service
    taskset -c 70 python3 scripts/bench/obstruction_probe.py \\
        --output reports/bench-results/hexbz-obstruction-probe.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"

# The instances the report tabulates: the `x^n - 1` family the issue names, the
# Swinnerton-Dyer family and its products, Wilkinson, representative cyclotomic
# products, and the easy controls where every candidate is a real divisor.
DEFAULT_NAMES = (
    "xpow24_minus1", "xpow36_minus1", "xpow48_minus1", "xpow60_minus1",
    "xpow105_minus1", "xpow120_minus1",
    "sd4", "sd5", "sd5_shift1", "sd5_shift2", "sd5_x_phi11", "sd5_x_phi45",
    "sd4_x_sd4shift1", "sd6",
    "wilkinson_40", "wilkinson_48", "wilkinson_56",
    "cyclo_phi17", "cyclo_phi41", "cyclo_phi179", "cyclo_phi275",
    "cyclo_phi385", "cyclo_phi64_x_phi105", "cyclo_phi105_x_phi128",
    "cyclo_phi128_x_phi165",
    "chebyshev_T24", "chebyshev_U24", "legendre_P30", "legendre_P38",
    "randprod_10", "randprod_21", "hoeij_M12_f132",
)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, text=True,
                          capture_output=True, check=True).stdout.strip()


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--names", help="comma-separated corpus instances")
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv[1:])

    names = tuple(args.names.split(",")) if args.names else DEFAULT_NAMES
    corpus = {}
    for line in CORPUS.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            corpus[row["name"]] = row
    missing = [name for name in names if name not in corpus]
    if missing:
        raise SystemExit(f"not in the corpus: {', '.join(missing)}")

    request = "".join(
        json.dumps({"coeffs": corpus[name]["coeffs"]}) + "\n" for name in names)
    completed = subprocess.run(
        [str(SERVICE), "--entry", "obstructionProbe"], input=request,
        text=True, capture_output=True, check=True)
    replies = [json.loads(line) for line in completed.stdout.splitlines() if line.strip()]
    if len(replies) != len(names):
        raise SystemExit(f"expected {len(names)} replies, got {len(replies)}")

    rows = []
    for name, reply in zip(names, replies):
        result = reply.get("result") or {}
        rows.append({
            "name": name,
            "family": corpus[name]["family"],
            "degree": corpus[name]["degree"],
            "method": result.get("method"),
            "obstruction": result.get("obstruction"),
        })

    record = {
        "schema": "hexbz-obstruction-probe/1",
        "env": {
            "git_commit": git("rev-parse", "HEAD"),
            "git_dirty": bool(git("status", "--porcelain")),
            "corpus_sha256": __import__("hashlib").sha256(
                CORPUS.read_bytes()).hexdigest(),
        },
        "rows": rows,
    }
    Path(args.output).write_text(json.dumps(record, indent=1, sort_keys=True) + "\n")

    reached = sum(r["obstruction"]["reachedFilter"] for r in rows if r["obstruction"])
    rejected = sum(r["obstruction"]["modularRejections"] for r in rows if r["obstruction"])
    fell = sum(r["obstruction"]["exactFallThroughs"] for r in rows if r["obstruction"])
    avoided = sum(r["obstruction"]["exactDivisionsAvoided"] for r in rows if r["obstruction"])
    agree = all(r["obstruction"]["sameFactors"] and r["obstruction"]["sameSearchShape"]
                and r["obstruction"]["sameDecline"]
                and r["obstruction"]["sameRepeatCounters"]
                for r in rows if r["obstruction"])
    print(f"wrote {args.output}")
    print(f"reached {reached}, rejected {rejected}, fell through {fell}, "
          f"exact divisions avoided {avoided}")
    print(f"filtered and unfiltered agree on every row: {agree}")
    return 0 if agree else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
