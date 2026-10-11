#!/usr/bin/env python3
"""Direct exact root/sign oracle for the rational Sturm frontend.

Reuse the existing pinned FLINT qqbar root evaluator on original rational
polynomials and endpoints. No Lean query, recurrence or certificate supplies
expected answers. Noncanonical wire coefficients are independently interpreted
from their two rational coordinates before the same root/sign contract applies.
Produced-certificate replay is a Lean control, not independent certificate
soundness evidence.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.real_algebraic_qqbar import QQBar, Unavailable, VERSION
from scripts.oracle.sign_det_common import require
from scripts.oracle.sign_det_flint import rational, polynomial, root_words, endpoint

DEFAULT_FIXTURE = ROOT / "conformance-fixtures/HexSturm/sturm.jsonl"
CORE = ("two-roots", "negative-head", "non-monic", "cubic", "zero-head",
        "constant", "negative-constant", "repeated-head", "root-free", "rational-root")
REQUIRED_CASES = {f"{name}/{i}" for name in CORE for i in range(12)} | {
    f"seed-10575/{i}" for i in range(24)} | {f"noncanonical/{i}" for i in range(12)}


def interpreted(raw: Any) -> list:
    require(isinstance(raw, list), "raw polynomial must be a list")
    result = []
    for pair in raw:
        require(isinstance(pair, list) and len(pair) == 2, "expected two stored coordinates")
        result.append(rational(pair[0]) + rational(pair[1]))
    return result


def check_record(record: dict) -> None:
    require(record.get("lib") == "HexSturm" and record.get("op") == "queries",
            "wrong library or operation")
    data = record["value"]
    require(data["schema"] == 1 and data["seed"] == 10575, "wrong schema or seed")
    require(data["storage"] in ("rational", "noncanonical"), "unknown storage")
    if data["storage"] == "noncanonical":
        require(interpreted(data["raw_head"]) == polynomial(data["head"]),
                "stored head disagrees with interpreted input")
        require([interpreted(q) for q in data["raw_queries"]] ==
                [polynomial(q) for q in data["queries"]],
                "stored queries disagree with interpreted inputs")
    words = root_words(data)
    valid = words is not None
    count = len(words) if valid else None
    signs = ([sum(word[i] for word in words) for i in range(len(data["queries"]))]
             if valid else [None] * len(data["queries"]))
    finite_integer_bounds = all(tag == 1 and bound.denominator == 1
                                for tag, bound in (endpoint(data["lower"]), endpoint(data["upper"])))
    require(data["integer_count"] == (count if valid and finite_integer_bounds else None),
            "positive-cleared half-open integer count disagrees on its guarded domain")
    result = data["result"]
    require(result["query"] == signs, f"query signs: expected {signs}, got {result['query']}")
    require(result["root_count"] == count, "wrong natural root count or domain refusal")
    require(result["prepared"] is valid, "wrong preparation acceptance")
    require(result["prepared_query"] == (signs if valid else None), "wrong prepared query")
    require(result["prepared_count"] == count, "wrong prepared root count")
    require(result["producer_replay"] == [valid] * len(data["queries"]),
            "produced certificate does not replay on its original input")
    require(result["prepared_replay"] == ([True] * len(data["queries"]) if valid else None),
            "prepared certificate does not replay on its original input")
    for key in ("query", "prepared_query"):
        require(result[key] is None or all(x is None or type(x) is int for x in result[key]),
                "query values must be exact integers or null")
    for key in ("producer_replay", "prepared_replay"):
        require(result[key] is None or all(type(x) is bool for x in result[key]),
                "replay controls must be Boolean")
    for key in ("root_count", "prepared_count"):
        require(result[key] is None or type(result[key]) is int, "count must be an exact integer")


def check(source: str | Path | None, failure_dir: Path) -> int:
    seen: set[str] = set()
    failures = 0
    for record in read_fixtures(source):
        case = record.get("case", "malformed")
        try:
            require(case not in seen, "duplicate case")
            seen.add(case)
            check_record(record)
        except (OracleMismatch, KeyError, TypeError, ValueError, ArithmeticError) as exc:
            failures += 1
            write_failure(failure_dir, library="HexSturm", profile="ci", seed=10575,
                          case_id=case, kind="query", input_record=record,
                          lean_output=record.get("value"), oracle_output=None,
                          oracle_name="FLINT qqbar", oracle_version=VERSION, diff=str(exc))
            print(f"FAIL {case}: {exc}", file=sys.stderr)
    require(REQUIRED_CASES <= seen, f"missing required cases: {sorted(REQUIRED_CASES - seen)}")
    print(f"HexSturm: {len(seen)} exact frontend cases, {failures} failures ({VERSION})")
    return int(failures != 0)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    try:
        with QQBar():
            pass
        return check(args.source or (DEFAULT_FIXTURE if args.check else None), args.failure_dir)
    except (Unavailable, OracleMismatch, OSError, ImportError) as exc:
        print(f"FAIL HexSturm oracle: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
