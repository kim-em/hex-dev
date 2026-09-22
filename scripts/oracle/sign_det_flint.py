#!/usr/bin/env python3
"""Exact independent root/sign-table oracle for rational BKR fixtures.

FLINT checks the root domain over Q, enumerates its real qqbar roots and
evaluates every query at those roots. It neither solves moment systems nor
calls the Lean Tarski producer. Complete sparse table equality detects missing
conditions even when forged counts have the correct total. The shared qqbar
adapter enforces the pinned python-flint/FLINT versions.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from math import lcm
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.real_algebraic_qqbar import QQBar, Unavailable, VERSION

DEFAULT_FIXTURE = ROOT / "conformance-fixtures/HexSignDet/sign_det.jsonl"
REQUIRED_CASES = {
    "two-roots", "negative-head", "empty-queries", "zero-root",
    "duplicate-zero-constant", "irrational-common-factor", "cubic-derivatives",
    "negative-cubic-derivatives", "high-degree-queries", "rational-scaling",
    "finite-interval", "left-half-line", "right-half-line", "many-queries",
    *(f"{name}/{suffix}" for name in ("constant", "negative-constant", "root-free",
                                    "zero-head", "repeated-head", "cancelled-head")
      for suffix in ("empty", "queries")),
    *(f"invalid-interval/{i}" for i in range(9)),
    *(f"seed-10377/{i}" for i in range(24)),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise OracleMismatch(message)


def rational(value: Any) -> Fraction:
    require(isinstance(value, list) and len(value) == 2 and
            all(type(x) is int for x in value) and value[1] > 0,
            f"invalid exact rational: {value!r}")
    return Fraction(*value)


def polynomial(value: Any) -> list[Fraction]:
    require(isinstance(value, list), "polynomial coefficients must be a list")
    return [rational(c) for c in value]


def endpoint(value: Any) -> tuple[int, Fraction]:
    if value == "-inf":
        return (0, Fraction(0))
    if value == "+inf":
        return (2, Fraction(0))
    return (1, rational(value))


def expected_table(data: dict[str, Any]) -> list[dict[str, Any]] | None:
    """Return exact sorted positive counts, or mathematical domain failure."""
    from flint import fmpq, fmpq_poly

    p = polynomial(data["head"])
    require(isinstance(data["queries"], list), "queries must be an ordered list")
    queries = [polynomial(q) for q in data["queries"]]
    lower, upper = endpoint(data["lower"]), endpoint(data["upper"])
    poly = fmpq_poly([fmpq(c.numerator, c.denominator) for c in p])
    if poly.is_zero() or poly.gcd(poly.derivative()).degree() > 0 or not lower < upper:
        return None
    for tag, value in (lower, upper):
        if tag == 1 and poly(fmpq(value.numerator, value.denominator)) == 0:
            return None
    if poly.degree() == 0:
        return []

    denominator = lcm(*(c.denominator for c in p))
    integers = [int(c * denominator) for c in p]
    counts: Counter[tuple[int, ...]] = Counter()
    with QQBar() as q:
        roots = q.roots([q.number(c, q.integer) for c in integers], integer=True)
        zero = q.number(0)
        lo = q.number(lower[1]) if lower[0] == 1 else None
        hi = q.number(upper[1]) if upper[0] == 1 else None
        operands = [[q.number(c) for c in reversed(query)] for query in queries]
        for root, multiplicity in roots:
            require(multiplicity == 1, "squarefree root has nonunit multiplicity")
            if lo is not None and q.compare(lo, root) >= 0:
                continue
            if hi is not None and q.compare(root, hi) >= 0:
                continue
            signs = []
            for coefficients in operands:
                value = zero
                for coefficient in coefficients:
                    value = q.binary("add", q.binary("mul", value, root), coefficient)
                sign = q.compare(value, zero)
                signs.append((sign > 0) - (sign < 0))
            counts[tuple(signs)] += 1
    return [{"signs": list(signs), "count": count} for signs, count in sorted(counts.items())]


def check_output(output: Any, expected: list[dict[str, Any]] | None, arity: int) -> None:
    require(isinstance(output, dict), "missing constructor result")
    if expected is None:
        require(output == {"status": "invalid-domain"}, "invalid domain was accepted")
        return
    require(output.get("status") == "ok", f"valid-domain construction failed: {output!r}")
    require(output.get("replay") is True, "produced replay did not pass its checker")
    check_table(output.get("table"), expected, arity)


def check_table(table: Any, expected: list[dict[str, Any]], arity: int) -> None:
    require(isinstance(table, list), "missing sparse sign table")
    seen = set()
    for row in table:
        require(isinstance(row, dict) and set(row) == {"signs", "count"}, "malformed table row")
        signs, count = row["signs"], row["count"]
        require(isinstance(signs, list) and len(signs) == arity and
                all(type(s) is int and s in (-1, 0, 1) for s in signs), "malformed sign condition")
        require(type(count) is int and count > 0, "sparse counts must be positive integers")
        key = tuple(signs)
        require(key not in seen, "duplicate sign condition")
        seen.add(key)
    require(table == expected, f"complete sign table differs: Lean={table!r}, FLINT={expected!r}")


def check_record(record: dict[str, Any]) -> None:
    require(record.get("kind") == "result" and record.get("lib") == "HexSignDet" and
            record.get("op") == "table", "unexpected sign-determination fixture record")
    data = record["value"]
    require(isinstance(data, dict) and type(data.get("schema")) is int and data["schema"] == 1,
            "unsupported sign-table schema")
    expected = expected_table(data)
    if expected is None:
        require(data.get("algebraic", "missing") is None, "invalid domain has algebraic root table")
    else:
        check_table(data.get("algebraic"), expected, len(data["queries"]))
    for mode in ("reduced", "direct"):
        check_output(data[mode], expected, len(data["queries"]))
    if len(data["queries"]) <= 4:
        require("reference" in data, "small fixture is missing full-ternary reference")
    if "reference" in data:
        check_output(data["reference"], expected, len(data["queries"]))


def check(source: str | Path | None, failure_dir: Path, profile: str, seed: int) -> int:
    seen: set[str] = set()
    failures = 0
    for record in read_fixtures(source):
        case = record["case"]
        try:
            require(case not in seen, "duplicate case")
            seen.add(case)
            check_record(record)
        except (OracleMismatch, KeyError, TypeError, ValueError, ArithmeticError) as exc:
            failures += 1
            write_failure(failure_dir, library="HexSignDet", profile=profile, seed=seed,
                          case_id=case, kind="sign-table", input_record=record,
                          lean_output=record.get("value"), oracle_output=None,
                          oracle_name="FLINT qqbar", oracle_version=VERSION, diff=str(exc))
            print(f"FAIL {case}: {exc}", file=sys.stderr)
    require(REQUIRED_CASES <= seen,
            f"incomplete sign-table fixture stream: missing {sorted(REQUIRED_CASES - seen)}")
    print(f"HexSignDet: {len(seen)} exact root/sign cases, {failures} failures ({VERSION})")
    return int(failures != 0)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", choices=("ci", "local"), default="ci")
    parser.add_argument("--seed", type=int, default=10377)
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    try:
        with QQBar():
            pass
        return check(args.source or (DEFAULT_FIXTURE if args.check else None),
                     args.failure_dir, args.profile, args.seed)
    except (Unavailable, OracleMismatch, OSError) as exc:
        print(f"FAIL HexSignDet oracle: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
