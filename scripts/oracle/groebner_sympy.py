#!/usr/bin/env python3
"""Compare F4 candidates with independent SymPy reduced Groebner bases.

SymPy's F5B implementation uses exact prime-field coefficients. Orders, variable
precedence, reducedness and coefficient representatives are matched explicitly.
Ordinary F2 polynomials are compared in the polynomial ring, without field
equations or Boolean-quotient reductions.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import sympy
from sympy.polys.orderings import monomial_key

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.common import write_failure


def check(value):
    p, n, order = value["p"], value["variables"], value["order"]
    symbols = sympy.symbols(f"x0:{n}")
    def expression(terms):
        result = sympy.Integer(0)
        for powers, coefficient in terms:
            assert len(powers) == n and 0 <= coefficient < p
            result += coefficient * sympy.prod(x**e for x, e in zip(symbols, powers))
        return result
    generators = [expression(f) for f in value["generators"]]
    if n == 0:
        expected = [[[[], 1]]] if any(int(f) % p for f in generators) else []
    else:
        gb = sympy.groebner(generators, *symbols, modulus=p, order=order, method="f5b")
        expected = [[ [list(powers), int(coefficient) % p]
                      for powers, coefficient in f.terms(order=order)] for f in gb.polys]
        expected.sort(key=lambda f: monomial_key(order)(tuple(f[0][0])), reverse=True)
    if expected != value["basis"]:
        raise ValueError(f"different reduced basis\nLean: {value['basis']}\nSymPy: {expected}")
    return expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--failure-dir", type=Path, default=Path("conformance-failures"))
    args = parser.parse_args()
    records = (args.check.read_text() if args.check else sys.stdin.read()).splitlines()
    seen = set()
    for line in records:
        record = json.loads(line)
        try:
            assert record["kind"] == "result" and record["lib"] == "HexGroebner" and record["op"] == "f4"
            assert record["case"] not in seen
            seen.add(record["case"])
            check(record["value"])
        except (ValueError, AssertionError, KeyError, TypeError, IndexError) as exc:
            path = write_failure(args.failure_dir, library="HexGroebner", profile="core", seed=0,
                case_id=record.get("case", "unknown"), kind="f4", input_record=record,
                lean_output=record.get("value"), oracle_output=None,
                oracle_name="SymPy F5B", oracle_version=sympy.__version__, diff=str(exc))
            raise SystemExit(f"{record.get('case')}: {exc}; replay: {path}") from exc
    assert len(records) == 567, f"incomplete F4 corpus: {len(records)}"
    assert any(json.loads(line)["value"]["chainPairs"] > 0 for line in records), "chain criterion not exercised"
    assert any(json.loads(line)["value"]["serialChainPairs"] > 0 for line in records), "serial chain criterion not exercised"
    print(f"OK: {len(records)} reduced bases match SymPy {sympy.__version__} F5B")


if __name__ == "__main__":
    main()
