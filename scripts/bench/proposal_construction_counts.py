#!/usr/bin/env python3
"""Count the prepared objects one proposal peel run builds, per corpus row.

The proposal traversal prepares two things before it walks a subset level: the
lift-wide data (the lift modulus and the lifted-factor degree and trailing
arrays) and the residual's image in `F_q[X]`.  Issue #9152 gives them their
mathematical lifetimes -- one per lift, one per residual -- where the old
`SupportMeta` built both once per attempted cardinality level.

The counts are exact rather than sampled.  `--entry proposalTrace` reports the
peel run's own record: `peeledFactorDegrees` gives one entry per exact split,
`unforcedCompletedLevels` concatenates the fully exhausted cardinalities of each
residual in order, and `unforcedDecline` says how the run ended.  From those:

    peel runs            = 1 when `henselLifts` is set, else 0 (the proposal
                           declined before lifting and never peeled)
    peels P              = len(peeledFactorDegrees)
    residuals searched R = P + 1 when the run stopped inside `findDirectSubset`
                             (`subsetBudget` or `cardinalityCap`),
                           P otherwise (`target = 1`, or no search at all)
    levels attempted A   = len(unforcedCompletedLevels) + P

A is `len(completed) + P` because the residual that stops attempts exactly the
levels it completes: `subsetBudget` declines before evaluating any member of the
level that does not fit, and `cardinalityCap` means the schedule ran out.  Each
of the other P residuals completes some levels and then finds in one more.

So the two arms build, per peel run:

    before   A lift-modulus preparations and A target reductions
    after    1 lift-modulus preparation  and R target reductions

Run against either arm; the derived columns report both, so one run of one
binary states what the other arm would have built on the same trace.  Usage::

    python3 scripts/bench/proposal_construction_counts.py \\
        .lake/build/bin/hexbz_factor_service --rows sd5_x_phi11,xpow105_minus1

Each record also carries `factorizationSha256`, a digest of the factorization
the proposal returned. Running the script against two binaries and diffing the
records therefore compares both what the traversal decided and what it answered.

With no `--rows`, every corpus row is measured and rows whose peel run attempts
more levels than it searches residuals are reported first.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"

# Declines raised by `findDirectSubset`, i.e. by a residual that entered
# proposal search and therefore had its image built.
SEARCHED_DECLINES = {"subsetBudget", "cardinalityCap", "invalidCandidate"}


class Service:
    """A warm `hexbz_factor_service --entry proposalTrace`."""

    def __init__(self, binary: str, cpu: str | None) -> None:
        argv = ([] if cpu is None else ["taskset", "-c", cpu]) + [
            binary, "--entry", "proposalTrace"]
        self.process = subprocess.Popen(
            argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            text=True, bufsize=1)

    def ask(self, coeffs: list[int]) -> tuple[dict | None, str]:
        """Return the proposal trace and a digest of the proposed factors.

        The digest covers the returned factorization coefficient by
        coefficient, so comparing two arms compares what they answered and not
        only how they got there: two runs can agree on every counter, support
        size and factor degree and still have chosen different factors of the
        same degree.
        """
        line = json.dumps({"coeffs": coeffs}, separators=(",", ":")) + "\n"
        self.process.stdin.write(line)
        self.process.stdin.flush()
        reply = json.loads(self.process.stdout.readline())
        result = reply.get("result")
        if result is None:
            return None, hashlib.sha256(b"declined").hexdigest()
        canonical = json.dumps(
            result.get("factorization"), sort_keys=True, separators=(",", ":"))
        return result["trace"], hashlib.sha256(canonical.encode()).hexdigest()

    def kill(self) -> None:
        self.process.kill()
        self.process.wait()


def counts(trace: dict) -> dict:
    """Derive the construction counts of one peel run from its trace."""
    peels = len(trace["peeledFactorDegrees"])
    completed = trace["unforcedCompletedLevels"]
    decline = trace["unforcedDecline"]
    # `proposeFactorization` sets `henselLifts` before it peels, so this is
    # exactly the rows whose proposal ran at all: the rest declined on the
    # eligibility test or on prime selection and never called `peelDirect`.
    peeled = 1 if trace["henselLifts"] >= 1 else 0
    residuals = peels + (1 if decline in SEARCHED_DECLINES else 0)
    attempted = len(completed) + peels
    return {
        "peelRuns": peeled,
        "peels": peels,
        "residuals": residuals,
        "completedLevels": completed,
        "levelsAttempted": attempted,
        "decline": decline,
        "liftedFactorCount": trace["liftedFactorCount"],
        "leaves": trace["unforcedLeaves"],
        "recordable": trace["unforcedRecordable"],
        "exactDivisions": trace["unforcedExactDivisions"],
        "obstructionRejections":
            trace["unforcedRecordable"] - trace["unforcedExactDivisions"],
        # What each arm builds for this run.
        "beforeLiftPreparations": attempted,
        "beforeTargetReductions": attempted,
        "afterLiftPreparations": peeled,
        "afterTargetReductions": residuals,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", help="hexbz_factor_service binary")
    parser.add_argument("--rows", help="comma-separated corpus row names")
    parser.add_argument("--cpu", help="pin the service to this CPU")
    parser.add_argument("--json", help="write the full record here")
    args = parser.parse_args()

    corpus = {
        row["name"]: row
        for row in map(json.loads, CORPUS.read_text().splitlines())
    }
    if args.rows:
        names = args.rows.split(",")
        missing = [name for name in names if name not in corpus]
        if missing:
            print(f"unknown corpus rows: {', '.join(missing)}", file=sys.stderr)
            return 2
    else:
        names = list(corpus)

    service = Service(args.binary, args.cpu)
    records = {}
    try:
        for name in names:
            trace, digest = service.ask(corpus[name]["coeffs"])
            record = None if trace is None else counts(trace)
            if record is not None:
                record["factorizationSha256"] = digest
            records[name] = record
    finally:
        service.kill()

    if not args.rows:
        names.sort(
            key=lambda name: -(0 if records[name] is None else
                               records[name]["levelsAttempted"] -
                               records[name]["residuals"]))

    print("| row | lifted | peels | residuals searched | levels attempted "
          "| completed | lift preps before/after | target reductions "
          "before/after |")
    print("|---|---:|---:|---:|---:|---|---|---|")
    for name in names:
        record = records[name]
        if record is None:
            print(f"| `{name}` | | | | | declined | | |")
            continue
        print(
            f"| `{name}` | {record['liftedFactorCount']} | {record['peels']} "
            f"| {record['residuals']} | {record['levelsAttempted']} "
            f"| {record['completedLevels']} "
            f"| {record['beforeLiftPreparations']} / "
            f"{record['afterLiftPreparations']} "
            f"| {record['beforeTargetReductions']} / "
            f"{record['afterTargetReductions']} |")

    if args.json:
        Path(args.json).write_text(json.dumps(records, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
