#!/usr/bin/env python3
"""Independent exact FLINT checks of converted native algebraic-tower roots.

The emitter runs the native root producer over two actual validated levels,
then exports canonical polynomial/disc identities for coefficients and roots.
The existing qqbar checker independently identifies those values and computes
all roots and multiplicities of the converted coefficient polynomial. This is
differential conformance after conversion. Independently reconstructed cubic
and quadratic generators also check every original recursive coefficient and
its cached sign against the emitted canonical value. Native certificate graphs
are not replayed by this oracle.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from fractions import Fraction
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.real_algebraic_flint import Checker, preflight, require
from scripts.oracle.real_algebraic_qqbar import QQBar, Unavailable, VERSION

DEFAULT = ROOT / "conformance-fixtures/HexRealClosure/trivial.jsonl"
REQUIRED = {"zero", "constant", "dependent linear", "mixed algebraic coefficients and multiplicities",
            "nonlinear algebraic head", "cubic with nonreal conjugates", "point root at zero"}


def validate_records(records: list[dict[str, Any]]) -> None:
    seen: set[str] = set()
    for record in records:
        require(record.get("kind") == "result" and record.get("lib") == "HexRealClosure" and
                record.get("op") == "trivialRoots", "unexpected native trivial-root record")
        name, data = record.get("case"), record.get("value")
        require(isinstance(name, str) and name not in seen, "invalid or duplicate fixture name")
        seen.add(name)
        require(isinstance(data, dict) and type(data.get("schema")) is int and data["schema"] == 1,
                "unsupported fixture schema")
        require(isinstance(data.get("coefficients"), list) and
                isinstance(data.get("nativeCoefficients"), list) and
                len(data["coefficients"]) == len(data["nativeCoefficients"]), "invalid coefficient lists")
        require(isinstance(data.get("generators"), list) and len(data["generators"]) == 2,
                "invalid generator list")
        roots = data.get("roots", False)
        require(roots is None or isinstance(roots, list), "invalid root set")
        if roots is not None:
            for entry in roots:
                require(isinstance(entry, dict) and type(entry.get("multiplicity")) is int and
                        entry["multiplicity"] > 0, "invalid positive multiplicity")
    require(REQUIRED <= seen, f"missing required cases: {sorted(REQUIRED - seen)}")


def native_value(q: QQBar, data: Any, generators: list[int]) -> int:
    """Evaluate the actual rational-base packed coefficients at two exact roots."""
    zero = q.number(0)
    require(isinstance(data, list), "invalid native coefficient")
    if not generators:
        require(len(data) == 3 and type(data[0]) is int and data[0] == 0 and
                type(data[1]) is int and type(data[2]) is int and data[2] > 0,
                "invalid native rational")
        value = Fraction(data[1], data[2])
        require((value.numerator, value.denominator) == (data[1], data[2]),
                "noncanonical native rational")
        return q.number(value)
    if not data:
        return zero
    require(len(data) == 2 and isinstance(data[0], list) and bool(data[0]) and
            type(data[1]) is int and data[1] in (-1, 1), "invalid packed native coefficient")
    coefficients = [native_value(q, c, generators[:-1]) for c in data[0]]
    require(q.compare(coefficients[-1], zero) != 0, "native trailing zero")
    value = zero
    for coefficient in reversed(coefficients):
        value = q.binary("add", q.binary("mul", value, generators[-1]), coefficient)
    sign = q.compare(value, zero)
    require(sign == data[1], "incorrect native cached sign")
    return value


def check_record(checker: Checker, record: dict[str, Any]) -> None:
    q, data = checker.q, record["value"]
    zero, one = q.number(0), q.number(1)
    cubic = q.roots([q.number(-2, q.integer), q.number(0, q.integer),
                     q.number(0, q.integer), q.number(1, q.integer)], integer=True)
    require(len(cubic) == 1 and q.compare(cubic[0][0], one) > 0, "cubic generator oracle failed")
    a = cubic[0][0]
    quadratic = q.roots([q.unary("neg", a), zero, one])
    positive = [v for v, _ in quadratic if q.compare(v, zero) > 0]
    require(len(positive) == 1, "quadratic Thom generator oracle failed")
    generators = [a, positive[0]]
    for actual, expected in zip(data["generators"], generators):
        checker.equal(actual, expected, "selected generator")
    for actual, native in zip(data["coefficients"], data["nativeCoefficients"]):
        checker.equal(actual, native_value(q, native, generators), "converted native coefficient")
    if record["case"] == "constant":
        require(any(len(c["poly"]) >= 3 for c in data["coefficients"]),
                "fixture has no irrational coefficient")
    checker.check("algebraicRoots", data)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", choices=("ci", "local"), default="ci")
    parser.add_argument("--require-oracles", action="store_true")
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    required = args.require_oracles or args.profile == "local" or os.getenv("HEX_REQUIRE_ORACLES") == "1"
    try:
        records = list(read_fixtures(DEFAULT if args.check else args.source))
        validate_records(records)
        available = preflight(required)
        if not available["algebraic"]:
            print(f"SKIP HexRealClosure trivial: {VERSION} algebraic roots unavailable")
            return 0
        with QQBar() as q:
            checker = Checker(q)
            for record in records:
                try:
                    check_record(checker, record)
                except (OracleMismatch, ArithmeticError, ValueError, TypeError, KeyError) as exc:
                    path = write_failure(args.failure_dir, library="HexRealClosure", profile=args.profile,
                        seed=0, case_id=record["case"], kind="trivialRoots", input_record=record,
                        lean_output=record["value"], oracle_output=None, oracle_name="python-flint qqbar",
                        oracle_version=VERSION, diff=str(exc))
                    raise OracleMismatch(f"{record['case']}: {exc}; saved {path}") from exc
        print(f"PASS HexRealClosure trivial: {len(records)} exact algebraic-coefficient root cases")
        return 0
    except (Unavailable, OracleMismatch, ArithmeticError, ValueError, TypeError, KeyError) as exc:
        print(f"FAIL HexRealClosure trivial: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
