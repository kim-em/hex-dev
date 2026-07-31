#!/usr/bin/env python3
"""Performance gate for HexBerlekampZassenhaus.

Asserts the per-case typed direct trace emitted by the Lean fixtures (chosen
tier, decline reason, prime probes, Hensel lifts, and candidate count) stays
within a committed baseline. A recombination blow-up or route/resource change
fails the merge even when the factors remain correct.

Deterministic: it reads the committed trace records and a committed baseline, with
no wall-clock measurement, so it is robust to CI-runner noise. A legitimate change
(e.g. a genuinely better/worse algorithm) updates the baseline deliberately, which
is a reviewable diff. The complementary wall-clock backstop lives in the CI step.

Usage: bz_trace_gate.py [fixtures.jsonl] [baseline.json]
       bz_trace_gate.py --write [fixtures.jsonl] [baseline.json]   # regenerate baseline
"""
from __future__ import annotations
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_FIXTURES = REPO_ROOT / "conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl"
DEFAULT_BASELINE = REPO_ROOT / "conformance-fixtures/HexBerlekampZassenhaus/bz-trace-baseline.json"


def load_traces(path: Path) -> dict[str, dict]:
    traces: dict[str, dict] = {}
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            if rec.get("kind") == "result" and rec.get("op") == "trace":
                traces[rec["case"]] = rec["value"]
    return traces


def main(argv: list[str]) -> int:
    args = [a for a in argv[1:] if not a.startswith("--")]
    write = "--write" in argv
    fixtures = Path(args[0]) if len(args) > 0 else DEFAULT_FIXTURES
    baseline_path = Path(args[1]) if len(args) > 1 else DEFAULT_BASELINE

    traces = load_traces(fixtures)

    if write:
        baseline = {
            case: {
                "tier": tr["tier"],
                "decline": tr["decline"],
                "primeProbes": tr["primeProbes"],
                "henselLifts": tr["henselLifts"],
                "candidatesTried": tr["candidatesTried"],
            }
            for case, tr in sorted(traces.items())
        }
        baseline_path.write_text(json.dumps(baseline, indent=2, sort_keys=True) + "\n")
        print(f"bz_trace_gate.py: wrote baseline with {len(baseline)} case(s)", file=sys.stderr)
        return 0

    baseline = json.loads(baseline_path.read_text())
    failures = 0
    for case, tr in sorted(traces.items()):
        b = baseline.get(case)
        if b is None:
            print(f"FAIL {case}: no baseline entry (add it deliberately with --write)", file=sys.stderr)
            failures += 1
            continue
        if tr["tier"] != b["tier"]:
            print(f"FAIL {case}: tier {tr['tier']!r} != baseline {b['tier']!r}", file=sys.stderr)
            failures += 1
        if tr["decline"] != b["decline"]:
            print(
                f"FAIL {case}: decline {tr['decline']!r} != baseline "
                f"{b['decline']!r}",
                file=sys.stderr,
            )
            failures += 1
        if tr["primeProbes"] != b["primeProbes"]:
            print(
                f"FAIL {case}: primeProbes {tr['primeProbes']} != baseline "
                f"{b['primeProbes']}",
                file=sys.stderr,
            )
            failures += 1
        if tr["henselLifts"] != b["henselLifts"]:
            print(
                f"FAIL {case}: henselLifts {tr['henselLifts']} != baseline "
                f"{b['henselLifts']}",
                file=sys.stderr,
            )
            failures += 1
        if tr["candidatesTried"] > b["candidatesTried"]:
            print(
                f"FAIL {case}: candidatesTried {tr['candidatesTried']} > baseline "
                f"{b['candidatesTried']} (recombination regression)",
                file=sys.stderr,
            )
            failures += 1
    for case in baseline:
        if case not in traces:
            print(f"FAIL {case}: baseline entry has no trace record", file=sys.stderr)
            failures += 1
    print(f"bz_trace_gate.py: checked {len(traces)} trace(s), {failures} failure(s)", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
