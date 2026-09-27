#!/usr/bin/env python3
"""Check infinitesimal fractions with Z3 RCF and exact rational specialization.

For the independent Fraction check, choose each positive rational argument
small enough that the first nonzero term dominates every polynomial at that
level. If p = X^i (a + X q), X <= min(1/2, |a|/(2 sum |q_j|)) suffices.
All lower-level coefficient signs have already been preserved. Z3 checks
fraction identities symbolically, including each comparison's difference.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from importlib.metadata import version
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.common import OracleMismatch, write_failure

VERSION = "z3-solver 4.15.4.0"
DEFAULT = ROOT / "conformance-fixtures/HexOrderedFn/infinitesimal.jsonl"
REQUIRED = {f"level{d}/{op}/{i}" for d, count in ((1, 12), (2, 12), (3, 6))
            for op in ("sign", "compare") for i in range(count)} | {
    f"normalize/{i}/{a}" for i in (0, 1, 3, 8) for a in (-3, -1, 1, 3)} | {
    "normalize/nonmonic", "normalize/negative-factor"}


def require(condition, message):
    if not condition:
        raise OracleMismatch(message)


def validate(value, depth):
    if depth == 0:
        require(isinstance(value, list) and len(value) == 2 and
                all(type(x) is int for x in value) and value[1] > 0,
                "invalid rational coefficient")
        return
    require(isinstance(value, dict) and set(value) == {"num", "den"},
            "invalid fraction encoding")
    for key in ("num", "den"):
        require(isinstance(value[key], list), "invalid coefficient array")
        for c in value[key]:
            validate(c, depth - 1)


def polynomials(value, depth):
    if depth:
        for key in ("num", "den"):
            yield depth, value[key]
            for c in value[key]:
                yield from polynomials(c, depth - 1)


def horner(coeffs, point, zero):
    result = zero
    for c in reversed(coeffs):
        result = result * point + c
    return result


def exact(value, depth, points):
    if depth == 0:
        return Fraction(*value)
    p, q = (horner([exact(c, depth - 1, points) for c in value[key]],
                   points[depth - 1], Fraction(0)) for key in ("num", "den"))
    require(q != 0, "zero denominator in exact specialization")
    return p / q


def radius(coeffs):
    for i, a in enumerate(coeffs):
        if a:
            tail = sum(map(abs, coeffs[i + 1:]))
            return min(Fraction(1, 2), abs(a) / (2 * tail)) if tail else Fraction(1, 2)
    return Fraction(1, 2)


def specialize(roots, depth):
    polys = [p for value in roots for p in polynomials(value, depth)]
    points = []
    for level in range(1, depth + 1):
        points.append(min([Fraction(1, 2)] + [
            radius([exact(c, level - 1, points) for c in p])
            for d, p in polys if d == level]))
    return points


class RCF:
    def __init__(self, depth):
        import z3
        from z3 import z3rcf
        self.ctx = z3.Context()
        self.api = z3rcf
        self.points = [z3rcf.MkInfinitesimal(f"epsilon{i + 1}", self.ctx)
                       for i in range(depth)]
        self.zero = z3rcf.RCFNum(0, self.ctx)

    def value(self, value, depth):
        if depth == 0:
            return self.api.RCFNum(f"{value[0]}/{value[1]}", self.ctx)
        p, q = (horner([self.value(c, depth - 1) for c in value[key]],
                       self.points[depth - 1], self.zero) for key in ("num", "den"))
        require(q != 0, "zero denominator in Hahn field")
        return p.__div__(q)  # The pinned API uses Python 2's division method name.


def sign(x):
    return 1 if x > 0 else -1 if x < 0 else 0


def check_record(record):
    require(record.get("kind") == "ordered-fn" and record.get("lib") == "HexOrderedFn",
            "wrong library or fixture kind")
    depth = record["depth"]
    require(type(depth) is int and 1 <= depth <= 3, "invalid tower depth")
    op = record["operation"]
    if op == "sign":
        roots = [record["input"]]
        expected = record["value"]
    elif op == "compare":
        roots = [record[k] for k in ("left", "right", "difference")]
        expected = record["value"]
    elif op == "normalize":
        roots = [{k: record[k] for k in ("num", "den")}, record["value"]]
        expected = record["sign"]
    else:
        raise OracleMismatch(f"unknown operation {op!r}")
    require(type(expected) is int and expected in (-1, 0, 1), "invalid sign")
    for value in roots:
        validate(value, depth)
    model = RCF(depth)
    zs = [model.value(value, depth) for value in roots]
    points = specialize(roots, depth)
    qs = [exact(value, depth, points) for value in roots]
    if op == "compare":
        require(zs[0] - zs[1] == zs[2], "incorrect symbolic difference")
        require(qs[0] - qs[1] == qs[2], "incorrect specialized difference")
        z, q = zs[0] - zs[1], qs[0] - qs[1]
    else:
        if op == "normalize":
            require(zs[0] == zs[1], "normalization changed the fraction")
            require(qs[0] == qs[1], "normalization changed its specialization")
        z, q = zs[0], qs[0]
    require(sign(z) == expected, f"Z3 sign {sign(z)} != Lean sign {expected}")
    require(sign(q) == expected, f"exact specialization sign {sign(q)} != Lean sign {expected}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=10376)
    parser.add_argument("--failure-dir", type=Path, default=ROOT / "conformance-failures")
    args = parser.parse_args()
    import z3
    require(version("z3-solver") == "4.15.4.0" and z3.get_version() == (4, 15, 4, 0),
            f"requires {VERSION}")
    source = args.source or (DEFAULT if args.check else None)
    stream = Path(source).open() if source else sys.stdin
    seen, failures = set(), 0
    try:
        for line in stream:
            record = json.loads(line)
            case = record["case"]
            try:
                require(case not in seen, "duplicate case")
                seen.add(case)
                check_record(record)
            except (OracleMismatch, KeyError, TypeError, ValueError, ArithmeticError) as exc:
                failures += 1
                write_failure(args.failure_dir, library="HexOrderedFn", profile=args.profile,
                              seed=args.seed, case_id=case, kind="ordered-fn", input_record=record,
                              lean_output=record.get("value"), oracle_output=None,
                              oracle_name="Z3 RCF and exact Fraction specialization",
                              oracle_version=VERSION, diff=str(exc))
                print(f"FAIL {case}: {exc}", file=sys.stderr)
        require(REQUIRED <= seen, f"missing cases: {sorted(REQUIRED - seen)}")
    finally:
        if source:
            stream.close()
    print(f"HexOrderedFn: {len(seen)} cases, {failures} failures ({VERSION}, exact Fraction)")
    return int(failures != 0)


if __name__ == "__main__":
    raise SystemExit(main())
