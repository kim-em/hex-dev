#!/usr/bin/env python3
"""Exact qqbar oracle for the ordered real algebraic field.

Consumes self-contained ``result`` records from hexrealalgebraic_emit_fixtures.
Operands and answers carry integer minimal polynomials and certified dyadic
isolation discs. Exact qqbar roots identify each value independently; no
producer index or printed decimal is used as its identity. Integer root sets
also undergo independent certified Arb-ball matching after factorization.

The default CI mode skips unavailable components explicitly. --require-oracles,
HEX_REQUIRE_ORACLES=1, and --profile local require every component. Available
oracles reporting a mismatch or inconclusive matching always fail.
"""
from __future__ import annotations

import argparse
import json
import os
import math
import re
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.common import OracleMismatch, read_fixtures, write_failure
from scripts.oracle.real_algebraic_qqbar import QQBar, Unavailable

DEFAULT = ROOT / "conformance-fixtures/HexRealAlgebraic/real_algebraic.jsonl"
VERSION = "python-flint 0.9.0 / FLINT 3.6.0"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise OracleMismatch(message)


def rational(value: Any) -> Fraction:
    require(isinstance(value, list) and len(value) == 2 and
            all(type(x) is int for x in value) and value[1] > 0,
            f"invalid rational {value!r}")
    return Fraction(*value)


def versions() -> None:
    try:
        import flint
    except ImportError as exc:
        raise Unavailable("python-flint is not installed") from exc
    if (flint.__version__, flint.__FLINT_VERSION__) != ("0.9.0", "3.6.0"):
        raise Unavailable(f"required version is {VERSION}")


def probe_scalar() -> None:
    versions()
    try:
        from flint.types import _gr
        R, C = _gr.gr_real_qqbar_ctx.new(), _gr.gr_complex_qqbar_ctx.new()
        s = R.sqrt(R(2))
        require(R.cmp(s, R(1)) > 0 and R.cmp(s, R(2)) < 0, "qqbar comparison probe failed")
        require(R.cmp(R.floor(s), R(1)) == 0 and R.cmp(R.ceil(s), R(2)) == 0,
                "qqbar rounding probe failed")
        try:
            R(C.i())
        except (AssertionError, ValueError):
            pass
        else:
            raise OracleMismatch("qqbar real context accepted i")
        with QQBar() as q:
            s = q.number("sqrt(2)")
            require(q.compare(q.binary("mul", s, s), q.number(2)) == 0,
                    "qqbar C adapter comparison probe failed")
    except (ImportError, AttributeError) as exc:
        raise Unavailable(f"scalar qqbar capability is missing: {exc}") from exc


def probe_integer() -> None:
    versions()
    try:
        from flint import fmpz_poly
        roots = fmpz_poly([-2, 0, 1]).complex_roots()
        require(len(roots) == 2 and all(r.imag.is_zero() for r, _ in roots),
                "certified integer-root probe failed")
    except AttributeError as exc:
        raise Unavailable(f"certified integer-root capability is missing: {exc}") from exc


def probe_algebraic() -> None:
    probe_scalar()
    with QQBar() as q:
        s = q.number("sqrt(2)")
        roots = q.roots([q.unary("neg", s), q.number(0), q.number(1)])
        require(len(roots) == 2 and all(m == 1 and q.compare(q.binary("mul", r, r), s) == 0
                                      for r, m in roots), "algebraic-coefficient root probe failed")


def preflight(required: bool) -> dict[str, bool]:
    available = {}
    for name, probe in (("scalar", probe_scalar), ("integer", probe_integer),
                        ("algebraic", probe_algebraic)):
        try:
            probe()
        except Unavailable as exc:
            available[name] = False
            print(f"{'FAIL' if required else 'SKIP'} {name}: {exc}", file=sys.stderr)
        else:
            available[name] = True
    if required and not all(available.values()):
        raise Unavailable("a required real-algebraic oracle component is unavailable")
    return available


def disc(record: dict[str, Any]) -> tuple[list[int], Fraction, Fraction, Fraction]:
    require(isinstance(record, dict) and set(record) == {"poly", "re", "im", "prec"},
            "invalid algebraic number record")
    poly, prec = record["poly"], record["prec"]
    require(isinstance(poly, list) and len(poly) >= 2 and
            all(type(c) is int for c in poly) and poly[-1] > 0,
            "invalid canonical integer polynomial")
    require(type(prec) is int, "invalid isolation precision")
    return poly, rational(record["re"]), rational(record["im"]), Fraction(2) ** -prec


class Checker:
    def __init__(self, q: QQBar) -> None:
        self.q = q
        self.values: dict[str, int] = {}
        self.roots: dict[tuple[int, ...], list[tuple[int, int]]] = {}

    def squared_distance(self, value: int, real: int, imag: int) -> int:
        re = self.q.to_real(self.q.unary("re", value, self.q.complex))
        im = self.q.to_real(self.q.unary("im", value, self.q.complex))
        require(re is not None and im is not None, "qqbar coordinate is nonreal")
        dr = self.q.binary("sub", re, real)
        di = self.q.binary("sub", im, imag)
        return self.q.binary("add", self.q.binary("mul", dr, dr), self.q.binary("mul", di, di))

    def complex_value(self, record: dict[str, Any]) -> int:
        key = json.dumps(record, sort_keys=True)
        if key in self.values:
            return self.values[key]
        p, re, im, width = disc(record)
        if tuple(p) not in self.roots:
            from flint import fmpz_poly
            unit, factors = fmpz_poly(p).factor()
            require(int(unit) == 1 and len(factors) == 1 and factors[0][1] == 1,
                    "serialized value polynomial is not primitive irreducible")
            self.roots[tuple(p)] = self.q.roots(
                [self.q.number(c, self.q.integer) for c in p], integer=True, complex_output=True)
        matches = []
        center_re, center_im = self.q.number(re), self.q.number(im)
        radius_sq = self.q.number(2 * width * width)
        for value, _ in self.roots[tuple(p)]:
            distance_sq = self.squared_distance(value, center_re, center_im)
            if self.q.compare(distance_sq, radius_sq) <= 0:
                matches.append(value)
        require(len(matches) == 1, f"isolation disc selected {len(matches)} roots, expected one")
        self.values[key] = matches[0]
        return matches[0]

    def value(self, record: dict[str, Any]) -> int:
        value = self.q.to_real(self.complex_value(record))
        require(value is not None, "real operand or result is nonreal")
        return value

    def equal(self, record: dict[str, Any], expected: int, name: str) -> None:
        require(self.q.compare(self.value(record), expected) == 0, f"incorrect {name}")

    def check(self, operation: str, d: dict[str, Any]) -> None:
        q = self.q
        zero = q.number(0)
        if operation == "reject":
            require(d["accepted"] is (q.to_real(self.complex_value(d["a"])) is not None),
                    "incorrect real construction acceptance")
            return
        if operation == "rejectPolynomial":
            accepted = all(q.to_real(self.complex_value(a)) is not None for a in d["coefficients"])
            require(d["accepted"] is accepted, "incorrect real coefficient acceptance")
            return
        if operation == "algebraicRoots":
            coefficients = [self.value(c) for c in d["coefficients"]]
            all_zero = all(q.compare(c, zero) == 0 for c in coefficients)
            require((d["roots"] is None) is all_zero, "incorrect universal root set")
            if all_zero:
                return
            expected = q.roots(coefficients)
            actual = [(self.value(r["root"]), r["multiplicity"]) for r in d["roots"]]
            require(len(actual) == len(expected), "incorrect algebraic real-root count")
            hits = [0] * len(expected)
            for value, mult in actual:
                matches = [i for i, (r, m) in enumerate(expected) if q.compare(value, r) == 0 and mult == m]
                require(len(matches) == 1, "incorrect algebraic root or multiplicity")
                hits[matches[0]] += 1
            require(all(h == 1 for h in hits), "duplicate or missing algebraic root")
            require(all(q.compare(a[0], b[0]) < 0 for a, b in zip(actual, actual[1:])),
                    "algebraic roots are not strictly ordered")
            if all(len(c["poly"]) == 2 for c in d["coefficients"]):
                rational_coeffs = [Fraction(-c["poly"][0], c["poly"][1]) for c in d["coefficients"]]
                denominator = math.lcm(*(c.denominator for c in rational_coeffs))
                integer_roots({"poly": [int(c * denominator) for c in rational_coeffs],
                    "roots": [r["root"] for r in d["roots"]],
                    "multiplicities": [r["multiplicity"] for r in d["roots"]]})
            return
        a = self.value(d["a"])
        if operation == "repr":
            self.equal(d["roundtrip"], a, "Repr round trip")
            pattern = (r'\(RealAlgebraicNumber\.ofAlgebraic\? \(ZPoly\.rootNear '
                r'#p\[([0-9, \-]+)\] (\(?-?[0-9]+(?:\.[0-9]+)?\)?)\)\)\.getD '
                r'\(Hex\.panicWith RealAlgebraicNumber\.zero "RealAlgebraicNumber\.repr: nonreal result"\)')
            match = re.fullmatch(pattern, d["text"])
            require(match is not None, "invalid emitted real representation")
            polynomial = [int(c.strip()) for c in match[1].split(",")]
            require(polynomial == d["a"]["poly"], "Repr changed the defining polynomial")
            point = q.number(Fraction(match[2].strip("()")))
            delta = q.binary("sub", a, point)
            distance = q.binary("mul", delta, delta)
            for root, _ in self.roots[tuple(polynomial)]:
                real_root = q.to_real(root)
                if real_root is None or q.compare(real_root, a) != 0:
                    require(q.compare(distance, self.squared_distance(root, point, zero)) < 0,
                            "Repr decimal does not uniquely name the root")
        elif operation == "order":
            b = self.value(d["b"])
            cmp = q.compare(a, b)
            for name, expected in {"compare": cmp, "reverse": -cmp, "eq": cmp == 0,
                                   "lt": cmp < 0, "le": cmp <= 0, "gt": cmp > 0, "ge": cmp >= 0}.items():
                require(d[name] == expected and type(d[name]) is type(expected), f"incorrect {name}")
            self.equal(d["min"], a if cmp <= 0 else b, "min")
            self.equal(d["max"], a if cmp >= 0 else b, "max")
        elif operation == "scalar":
            sign = q.compare(a, zero)
            require(d["sign"] == sign, "incorrect sign")
            for name in ("abs", "floor", "ceil"):
                expected = q.unary(name, a)
                if name == "abs":
                    self.equal(d[name], expected, name)
                else:
                    require(type(d[name]) is int and q.compare(q.number(d[name]), expected) == 0,
                            f"incorrect {name}")
            is_rat = bool(q.lib.qqbar_is_rational(a))
            require((d["rational"] is not None) is is_rat, "incorrect rational recognition")
            if is_rat:
                require(q.compare(a, q.number(rational(d["rational"]))) == 0, "incorrect rational value")
            require((d["sqrt"] is None) is (sign < 0), "incorrect square-root acceptance")
            if sign >= 0:
                self.equal(d["sqrt"], q.unary("sqrt", a), "sqrt")
            self.equal(d["sqrtSquare"], q.unary("abs", a), "sqrt of square")
            self.equal(d["conj"], a, "conjugation")
        elif operation == "arithmetic":
            b = self.value(d["b"])
            inv = zero if q.compare(a, zero) == 0 else q.unary("inv", a)
            results = {name: q.binary(name, a, b) for name in ("add", "sub", "mul")}
            results.update(div=zero if q.compare(b, zero) == 0 else q.binary("div", a, b),
                neg=q.unary("neg", a), inv=inv, natPow=q.binary("mul", q.binary("mul", a, a), a),
                intPow=q.binary("mul", inv, inv), nsmul=q.binary("mul", q.number(3), a),
                zsmul=q.binary("mul", q.number(-3), a), qsmul=q.binary("mul", q.number(Fraction(2, 3)), a))
            for name, value in results.items():
                self.equal(d[name], value, name)
        elif operation == "approx":
            error = q.unary("abs", q.binary("sub", a, q.number(rational(d["center"]))))
            radius = rational(d["radius"])
            require(0 <= radius <= Fraction(2) ** -d["prec"], "incorrect approximation radius bound")
            require(q.compare(error, q.number(radius)) <= 0, "approximation misses its value")
        else:
            raise OracleMismatch(f"unknown operation {operation}")


def integer_roots(d: dict[str, Any]) -> None:
    """Certified ball bijection on irreducible factors, never on repeated inputs."""
    from flint import fmpz_poly, ctx
    p = fmpz_poly(d["poly"])
    if p.degree() <= 0:
        require(d["roots"] == [], "integer constant must have no finite roots")
        return
    _, factors = p.factor()
    isolations = []
    factors_by_coefficients = {tuple(int(c) for c in f): int(m) for f, m in factors}
    for record in d["roots"]:
        minimal, real, imag, width = disc(record)
        require(tuple(minimal) in factors_by_coefficients,
                "returned root has a different minimal polynomial from every input factor")
        isolations.append((real, imag, width, tuple(minimal)))
    saved = ctx.prec
    try:
        for precision in (64, 128, 256, 512, 1024, 2048, 4096):
            ctx.prec = precision
            found, ambiguous = [], False
            for factor, multiplicity in factors:
                # Each irreducible factor is squarefree in characteristic zero.
                for root, _ in factor.complex_roots():
                    if root.imag.is_zero():
                        lo, hi = root.real.lower().fmpq(), root.real.upper().fmpq()
                        found.append((Fraction(int(lo.numer()), int(lo.denom())),
                                      Fraction(int(hi.numer()), int(hi.denom())), int(multiplicity),
                                      tuple(int(c) for c in factor)))
                    elif root.imag.contains(0):
                        ambiguous = True
            if ambiguous:
                continue
            require(len(found) == len(isolations), "incorrect integer real-root count")
            hits = []
            for lo, hi, multiplicity, factor in found:
                matches = [i for i, (real, imag, width, minimal) in enumerate(isolations)
                    if minimal == factor and max((lo - real) ** 2, (hi - real) ** 2) + imag ** 2 < 2 * width ** 2]
                if "multiplicities" in d and len(matches) == 1:
                    require(d["multiplicities"][matches[0]] == multiplicity,
                            "incorrect integer-factor root multiplicity")
                if len(matches) != 1:
                    break
                hits.append(matches[0])
            else:
                if len(set(hits)) == len(isolations):
                    ordered = sorted(zip(hits, found))
                    if all(a[1][1] < b[1][0] for a, b in zip(ordered, ordered[1:])):
                        return
        raise OracleMismatch("certified integer-root matching or ordering remained inconclusive")
    finally:
        ctx.prec = saved


OPERATIONS = {"order", "scalar", "arithmetic", "approx", "integerRoots", "algebraicRoots",
              "reject", "rejectPolynomial", "repr"}
REQUIRED_CASES = {
    **{op: names for op, names in [
        ("order", {"zero", "rational", "sqrt-signs", "sqrt-lower", "sqrt-upper", "negative-lower",
                   "negative-upper", "equal-sqrt", "equal-square", "equal-cancel", "cross-factor",
                   "mignotte-close", "mignotte-left-rational", "mignotte-right-rational"}),
        ("scalar", {"zero", "rational", "sqrt", "negative-sqrt", "negative-one", "rational-square",
                    "negative-integer", "positive-integer", "sqrt-above-two"}),
        ("arithmetic", {"zero", "rational", "sqrt"}),
        ("integerRoots", {"mignotte", "degree-eight", "zero", "constant", "nonreal"}),
        ("algebraicRoots", {"irrational-coefficient", "repeated", "zero", "constant", "nonreal"}),
        ("reject", {"conjugate/0", "conjugate/1"}),
        ("rejectPolynomial", {"nonreal-coefficient"}),
        ("repr", {"zero", "rational", "sqrt", "negative-sqrt"}),
    ]},
    "approx": {f"{case}/{prec}" for case in ("zero", "rational", "sqrt", "negative-sqrt")
               for prec in (-8, 0, 16)},
}


def validate_records(records: list[dict[str, Any]]) -> None:
    require(bool(records), "empty fixture stream")
    seen = set()
    for record in records:
        require(record.get("kind") == "result" and record.get("lib") == "HexRealAlgebraic",
                "unexpected fixture record")
        require(record.get("op") in OPERATIONS, "unknown fixture operation")
        require(isinstance(record.get("value"), dict) and record["value"].get("schema") == 1,
                "unsupported fixture schema")
        key = (record["op"], record["case"])
        require(key not in seen, f"duplicate case {key}")
        seen.add(key)
    missing = {(op, name) for op, names in REQUIRED_CASES.items() for name in names} - seen
    require(not missing, f"missing required fixture cases: {sorted(missing)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", help="JSONL file, or stdin when omitted")
    parser.add_argument("--check", action="store_true", help="check the committed fixture")
    parser.add_argument("--profile", choices=("ci", "local"), default="ci")
    parser.add_argument("--require-oracles", action="store_true")
    parser.add_argument("--preflight", action="store_true")
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    required = args.require_oracles or args.profile == "local" or os.getenv("HEX_REQUIRE_ORACLES") == "1"
    try:
        available = preflight(required)
        if args.preflight:
            print(f"PASS real-algebraic oracle preflight: {VERSION}")
            return 0
        records = list(read_fixtures(DEFAULT if args.check else args.source))
        validate_records(records)
        q = QQBar() if available["scalar"] or available["algebraic"] else None
        checker = Checker(q) if q is not None else None
        checked, skipped, seen = 0, 0, set()
        try:
            for record in records:
                require(record["kind"] == "result" and record["lib"] == "HexRealAlgebraic",
                        "unexpected fixture record")
                operation, data = record["op"], record["value"]
                require(data["schema"] == 1, "unsupported fixture schema")
                key = (operation, record["case"])
                require(key not in seen, f"duplicate case {key}")
                seen.add(key)
                component = "integer" if operation == "integerRoots" else (
                    "algebraic" if operation == "algebraicRoots" else "scalar")
                if not available[component]:
                    skipped += 1
                    continue
                try:
                    if component == "integer":
                        integer_roots(data)
                    else:
                        checker.check(operation, data)
                except (OracleMismatch, ArithmeticError, ValueError, TypeError, KeyError) as exc:
                    path = write_failure(args.failure_dir, library="HexRealAlgebraic", profile=args.profile,
                        seed=0, case_id=f"{operation}/{record['case']}", kind=operation,
                        input_record=record, lean_output=data, oracle_output=None,
                        oracle_name="python-flint qqbar/Arb", oracle_version=VERSION, diff=str(exc))
                    raise OracleMismatch(f"{operation}/{record['case']}: {exc}; saved {path}") from exc
                checked += 1
        finally:
            if q is not None:
                q.close()
        print(f"PASS HexRealAlgebraic: {checked} exact oracle cases; {skipped} unavailable-component skips")
        return 0
    except (Unavailable, OracleMismatch, ArithmeticError, ValueError, TypeError, KeyError) as exc:
        print(f"FAIL HexRealAlgebraic: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
