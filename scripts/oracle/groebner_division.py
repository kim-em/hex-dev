#!/usr/bin/env python3
"""Compare checked ordered division with independent exact SymPy division."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import sympy
from sympy.polys.orderings import monomial_key

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.common import write_failure


def canonical(poly, p, n):
    previous = None
    for powers, coefficient in poly:
        assert len(powers) == n and all(isinstance(e, int) and e >= 0 for e in powers)
        assert isinstance(coefficient, int) and 0 < coefficient < p
        assert previous is None or tuple(previous) > tuple(powers)
        previous = powers


def check(value):
    p, n, order = value["p"], value["variables"], value["order"]
    divisors, dividend = value["generators"], value["dividend"]
    quotients, remainder = value["quotients"], value["remainder"]
    assert len(quotients) == len(divisors)
    for poly in divisors + [dividend] + quotients + [remainder]:
        canonical(poly, p, n)
    if n == 0:
        expected_q, expected_r = [[] for _ in divisors], dividend
        for j, divisor in enumerate(divisors):
            if divisor and expected_r:
                expected_q[j] = [[[], expected_r[0][1] * pow(divisor[0][1], -1, p) % p]]
                expected_r = []
                break
    else:
        symbols = sympy.symbols(f"x0:{n}")
        def expression(poly):
            return sum(c * sympy.prod(x**e for x, e in zip(symbols, powers)) for powers, c in poly)
        def terms(expr):
            result = [[list(powers), int(c) % p] for powers, c in
                      sympy.Poly(expr, *symbols, modulus=p).terms() if int(c) % p]
            return sorted(result, key=lambda t: t[0], reverse=True)
        nonzero = [j for j, divisor in enumerate(divisors) if divisor]
        expected_q = [[] for _ in divisors]
        if nonzero:
            q, r = sympy.reduced(expression(dividend), [expression(divisors[j]) for j in nonzero],
                                  *symbols, modulus=p, order=order)
            for j, quotient in zip(nonzero, q):
                expected_q[j] = terms(quotient)
            expected_r = terms(r)
        else:
            expected_r = dividend
    if value.get("normalForm", False):
        original = value["original"]
        for poly in original:
            canonical(poly, p, n)
        gb = sympy.groebner([expression(poly) for poly in original], *symbols,
                            modulus=p, order=order, method="f5b")
        expected_basis = [terms(poly.as_expr()) for poly in gb.polys]
        key = monomial_key(order)
        expected_basis.sort(key=lambda f: max(key(tuple(t[0])) for t in f), reverse=True)
        if expected_basis != divisors:
            raise ValueError("accepted basis differs from independent reduced basis of original ideal")
        if value["member"] != (expected_r == []):
            raise ValueError("membership result differs from independent normal form")
    if expected_q != quotients or expected_r != remainder:
        raise ValueError(f"different ordered division: expected {(expected_q, expected_r)}, got {(quotients, remainder)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--failure-dir", type=Path, default=Path("conformance-failures"))
    parser.add_argument("--require-oracles", action="store_true")
    args = parser.parse_args()
    records = (args.check.read_text() if args.check else sys.stdin.read()).splitlines()
    seen = set()
    for line in records:
        record = json.loads(line)
        try:
            assert record["kind"] == "result" and record["lib"] == "HexGroebner" and record["op"] == "division"
            assert record["case"] not in seen
            seen.add(record["case"])
            check(record["value"])
        except (ValueError, AssertionError, KeyError, TypeError, IndexError) as exc:
            path = write_failure(args.failure_dir, library="HexGroebner", profile="core", seed=0,
                case_id=record.get("case", "unknown"), kind="division", input_record=record,
                lean_output=record.get("value"), oracle_output=None,
                oracle_name="SymPy reduced", oracle_version=sympy.__version__, diff=str(exc))
            raise SystemExit(f"{record.get('case')}: {exc}; replay: {path}") from exc
    assert len(records) == 1288, f"incomplete division corpus: {len(records)}"
    assert {json.loads(line)["value"]["order"] for line in records} == {"lex", "grlex", "grevlex"}
    assert {json.loads(line)["value"]["p"] for line in records} == {2, 3, 7, 251, 257, 65521, 65537, 2147483647}
    nonzero_fields = {json.loads(line)["value"]["p"] for line in records
                      if json.loads(line)["value"]["dividend"]}
    assert nonzero_fields == {2, 3, 7, 251, 257, 65521, 65537, 2147483647}
    assert sum(bool(json.loads(line)["value"].get("normalForm")) for line in records) == 154
    print(f"OK: {len(records)} ordered divisions, including 154 certified normal forms/membership results, match SymPy {sympy.__version__}")


if __name__ == "__main__":
    main()
