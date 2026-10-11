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
from fractions import Fraction

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.real_algebraic_qqbar import QQBar, Unavailable, VERSION
from scripts.oracle.exact_roots import require, rational, polynomial, root_words, endpoint

DEFAULT_FIXTURE = ROOT / "conformance-fixtures/HexSturm/sturm.jsonl"
def wire(poly: list[Fraction]) -> list[list[int]]:
    while poly and poly[-1] == 0:
        poly.pop()
    return [[c.numerator, c.denominator] for c in poly]


def input_cases() -> dict[str, tuple[list, list, Any, Any, str]]:
    """Regenerate the fixed input contract, without any Lean answers."""
    core = {
        "two-roots": [-1, 0, 1], "negative-head": [1, 0, -1],
        "non-monic": [Fraction(-4, 3), 0, Fraction(2, 3)],
        "cubic": [0, -1, 0, 1], "zero-head": [], "constant": [5],
        "negative-constant": [-5], "four-x": [0, 4],
        "repeated-head": [1, -2, 1], "root-free": [1, 0, 1],
        "rational-root": [Fraction(-1, 3), 1],
    }
    intervals = [("-inf", "+inf"), ([-2, 1], [2, 1]), ("-inf", [0, 1]),
                 ([0, 1], "+inf"), ([-1, 1], [2, 1]), ([2, 1], [-2, 1]),
                 ([0, 1], [0, 1]), ("+inf", "-inf"), ("-inf", "-inf"),
                 ("+inf", "+inf"), ([-2, 1], [1, 1]), ("+inf", [2, 1])]
    cases = {}
    def add(name, coefficients, lower, upper, storage="rational"):
        head = wire(list(map(Fraction, coefficients)))
        queries = [wire(list(map(Fraction, q))) for q in
                   ([1], [], [-1], [0, 1], [-1, 1], coefficients,
                    [0] * 8 + [1], [0, Fraction(1, 10)])]
        cases[name] = head, queries, lower, upper, storage
    for name, coefficients in core.items():
        for i, (lower, upper) in enumerate(intervals):
            add(f"{name}/{i}", coefficients, lower, upper)
    seed = 10575
    for i in range(24):
        coefficients = []
        for _ in range(4):
            seed = (1103515245 * seed + 12345) % 2147483648
            coefficients.append(Fraction(seed % 11 - 5, seed % 5 + 1))
        for j, (lower, upper) in enumerate(intervals[:2]):
            add(f"seed-10575/{i}/{j}", coefficients, lower, upper)
    for i, (lower, upper) in enumerate(intervals):
        add(f"noncanonical/{i}", core["two-roots"], lower, upper, "noncanonical")
    return cases


INPUTS = input_cases()
REQUIRED_CASES = set(INPUTS)


def typed_equal(actual: Any, expected: Any) -> bool:
    """JSON booleans and floating-point values cannot stand in for integers."""
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(typed_equal(a, e) for a, e in zip(actual, expected))
    return actual == expected


def interpreted(raw: Any) -> list:
    require(isinstance(raw, list), "raw polynomial must be a list")
    result = []
    for pair in raw:
        require(isinstance(pair, list) and len(pair) == 2, "expected two stored coordinates")
        result.append(rational(pair[0]) + rational(pair[1]))
    return result


def check_record(record: dict) -> None:
    require(record.get("kind") == "result" and record.get("lib") == "HexSturm" and
            record.get("op") == "queries", "wrong record kind, library or operation")
    require(record.get("case") in INPUTS, "unknown case")
    data = record["value"]
    require(type(data["schema"]) is int and data["schema"] == 1 and
            type(data["seed"]) is int and data["seed"] == 10575, "wrong schema or seed")
    head, queries, lower, upper, storage = INPUTS[record["case"]]
    for key, expected in (("head", head), ("queries", queries), ("lower", lower),
                          ("upper", upper), ("storage", storage)):
        require(typed_equal(data[key], expected), f"input contract changed: {key}")
    if storage == "noncanonical":
        require(interpreted(data["raw_head"]) == polynomial(head),
                "stored head disagrees with original input")
        require([interpreted(q) for q in data["raw_queries"]] ==
                [polynomial(q) for q in queries], "stored queries disagree with original inputs")
        require(any(rational(pair[1]) != 0 for pair in data["raw_head"]),
                "noncanonical head has only canonical representatives")
        for key, bound in (("raw_lower", lower), ("raw_upper", upper)):
            if isinstance(bound, str):
                require(data[key] == bound, "wrong stored infinity")
            else:
                require(interpreted([data[key]]) == [rational(bound)], "wrong stored endpoint")
                if rational(bound) != 0:
                    require(rational(data[key][1]) != 0, "finite endpoint was stored canonically")
    words = root_words(data)
    valid = words is not None
    count = len(words) if valid else None
    signs = ([sum(word[i] for word in words) for i in range(len(queries))]
             if valid else [None] * len(queries))
    finite_integer_bounds = all(tag == 1 and bound.denominator == 1
                               for tag, bound in (endpoint(lower), endpoint(upper)))
    require(typed_equal(data["integer"], [count, signs] if valid and finite_integer_bounds else None),
            "positive-cleared integer frontends disagree on their guarded domain")
    expected = {
        "query": signs, "reduced_query": signs, "root_count": count,
        "prepared": valid, "prepared_query": signs if valid else None,
        "prepared_reduced_query": signs if valid else None, "prepared_count": count,
        "certificate_values": signs, "producer_replay": [valid] * len(queries),
        "wrong_value_replay": [False] * len(queries),
        "prepared_certificate_values": signs if valid else None,
        "prepared_replay": [True] * len(queries) if valid else None,
        "count_certificate_value": count, "count_certificate_replay": True if valid else None,
        "retargeted": valid, "retargeted_query": signs if valid else None,
        "retargeted_count": count,
    }
    require(set(data["result"]) == set(expected), "missing or unexpected operation result")
    for key, answer in expected.items():
        require(typed_equal(data["result"][key], answer),
                f"{key}: expected {answer}, got {data['result'][key]}")


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
