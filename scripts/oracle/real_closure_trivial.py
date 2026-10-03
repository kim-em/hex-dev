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
from scripts.oracle.real_algebraic_flint import Checker, preflight, require, disc
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
        require(isinstance(data, dict) and type(data.get("schema")) is int and data["schema"] == 2,
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
                require(entry.get("kind") in ("point", "selected"), "invalid native root kind")
    require(REQUIRED <= seen, f"missing required cases: {sorted(REQUIRED - seen)}")


class TrivialChecker(Checker):
    """Identify real operands directly in the emitted isolating square.

    Exact interval comparisons avoid constructing squared distances to every
    nonreal conjugate. FLINT verifies irreducibility and enumerates real roots;
    exactly one must lie in the square's real interval, with zero in its
    imaginary interval. Native certificate graphs are not accepted as proofs.
    """

    def value(self, record: dict[str, Any]) -> int:
        import json
        from flint import fmpz_poly
        key = json.dumps(record, sort_keys=True)
        if key in self.values:
            return self.values[key]
        polynomial, real, imaginary, width = disc(record)
        require(abs(imaginary) <= width, "real operand square excludes the real axis")
        if tuple(polynomial) not in self.roots:
            unit, factors = fmpz_poly(polynomial).factor()
            require(int(unit) == 1 and len(factors) == 1 and factors[0][1] == 1,
                    "serialized polynomial is not primitive irreducible")
            self.roots[tuple(polynomial)] = self.q.roots(
                [self.q.number(c, self.q.integer) for c in polynomial], integer=True)
        lower, upper = self.q.number(real - width), self.q.number(real + width)
        matches = [value for value, _ in self.roots[tuple(polynomial)]
                   if self.q.compare(lower, value) <= 0 and self.q.compare(value, upper) <= 0]
        require(len(matches) == 1, "real isolation square did not select exactly one root")
        self.values[key] = matches[0]
        return matches[0]


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


def polynomial_roots(q: QQBar, coefficients: list[int], generators: list[int]) -> list[tuple[int, int]]:
    """Remove exact known generator factors before general qqbar root finding.

    Linear and pure quadratic/cubic residuals use FLINT's exact division,
    principal square root and cube root; their real roots and multiplicities
    follow the standard binomial cases. Other residuals use general qqbar roots.
    Candidates come from the independently reconstructed generators and zero,
    never from emitted roots. Exact synthetic division proves each removed
    factor and its multiplicity. FLINT computes the complete remaining roots.
    """
    zero = q.number(0)
    polynomial = list(coefficients)
    while polynomial and q.compare(polynomial[-1], zero) == 0:
        polynomial.pop()
    roots: list[tuple[int, int]] = []
    for candidate in generators + [zero]:
        multiplicity = 0
        while len(polynomial) > 1:
            quotient = [polynomial[-1]]
            for coefficient in reversed(polynomial[1:-1]):
                quotient.append(q.binary("add", coefficient,
                    q.binary("mul", candidate, quotient[-1])))
            remainder = q.binary("add", polynomial[0],
                q.binary("mul", candidate, quotient[-1]))
            if q.compare(remainder, zero) != 0:
                break
            polynomial = list(reversed(quotient))
            multiplicity += 1
        if multiplicity:
            roots.append((candidate, multiplicity))
    if len(polynomial) == 2:
        roots.append((q.binary("div", q.unary("neg", polynomial[0]), polynomial[1]), 1))
    elif len(polynomial) in (3, 4) and all(q.compare(c, zero) == 0 for c in polynomial[1:-1]):
        radicand = q.binary("div", q.unary("neg", polynomial[0]), polynomial[-1])
        sign = q.compare(radicand, zero)
        if len(polynomial) == 3:
            if sign > 0:
                root = q.unary("sqrt", radicand)
                roots.extend([(root, 1), (q.unary("neg", root), 1)])
            elif sign == 0:
                roots.append((zero, 2))
        else:
            magnitude = radicand if sign >= 0 else q.unary("neg", radicand)
            complex_root = q.nth_root(magnitude, 3)
            root = q.to_real(complex_root)
            require(root is not None, "positive cube root is nonreal")
            roots.append((root if sign >= 0 else q.unary("neg", root), 3 if sign == 0 else 1))
    elif len(polynomial) > 1:
        roots.extend(q.roots(polynomial))
    return roots


def check_record(checker: Checker, record: dict[str, Any]) -> None:
    q, data = checker.q, record["value"]
    if record["case"] == "point root at zero":
        require(data["roots"] is not None and any(r["kind"] == "point" for r in data["roots"]),
                "missing native point root")
    if record["case"] in ("nonlinear algebraic head", "cubic with nonreal conjugates"):
        require(bool(data["roots"]) and all(r["kind"] == "selected" for r in data["roots"]),
                "missing native selected roots")
    zero, one = q.number(0), q.number(1)
    if record["case"] == "point root at zero":
        require(any(r["kind"] == "point" and q.compare(checker.value(r["root"]), zero) == 0
                    for r in data["roots"]), "missing native point root at zero")
    a = q.to_real(q.nth_root(q.number(2, q.complex), 3))
    require(a is not None and q.compare(a, one) > 0, "cubic generator oracle failed")
    generators = [a, q.unary("sqrt", a)]
    for actual, expected in zip(data["generators"], generators):
        checker.equal(actual, expected, "selected generator")
    for actual, native in zip(data["coefficients"], data["nativeCoefficients"]):
        checker.equal(actual, native_value(q, native, generators), "converted native coefficient")
    if record["case"] == "constant":
        require(any(len(c["poly"]) >= 3 for c in data["coefficients"]),
                "fixture has no irrational coefficient")
    coefficients = [checker.value(c) for c in data["coefficients"]]
    all_zero = all(q.compare(c, zero) == 0 for c in coefficients)
    require((data["roots"] is None) is all_zero, "incorrect universal root set")
    if all_zero:
        return
    expected = polynomial_roots(q, coefficients, generators)
    actual = [(checker.value(r["root"]), r["multiplicity"]) for r in data["roots"]]
    require(len(actual) == len(expected), "incorrect algebraic real-root count")
    hits = [0] * len(expected)
    for value, multiplicity in actual:
        matches = [i for i, (root, label) in enumerate(expected)
                   if q.compare(value, root) == 0 and multiplicity == label]
        require(len(matches) == 1, "incorrect algebraic root or multiplicity")
        hits[matches[0]] += 1
    require(all(hit == 1 for hit in hits), "duplicate or missing algebraic root")
    require(all(q.compare(a[0], b[0]) < 0 for a, b in zip(actual, actual[1:])),
            "algebraic roots are not strictly ordered")


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
            checker = TrivialChecker(q)
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
