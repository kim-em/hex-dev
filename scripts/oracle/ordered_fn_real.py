#!/usr/bin/env python3
"""Check real-refinement fixtures with exact intervals and Z3 real arithmetic.

The caller fixtures enclose rational subjects and refine either just the argument
or coefficients and argument together. Z3 independently checks the Horner bounds
for every assignment inside the supplied source intervals. These finite successes
do not assert transcendence or register a rational subject as a new field.
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
from scripts.oracle.ordered_fn_z3 import require

VERSION = "z3-solver 4.15.4.0"
DEFAULT = ROOT / "conformance-fixtures/HexOrderedFn/real.jsonl"
REQUIRED = {f"{name}/{joint}/{n}" for name in (
    "positive", "negative-denominator", "pole", "near-zero", "zero",
    "non-dyadic", "degree", "quotient") for joint in ("false", "true")
    for n in (0, 1, 2, 4, 8, 12)}


def rational(value):
    require(isinstance(value, list) and len(value) == 2 and
            all(type(x) is int for x in value) and value[1] > 0, "invalid rational")
    return Fraction(*value)


def interval(value):
    require(isinstance(value, list) and len(value) == 2, "invalid bound")
    a, b = map(rational, value)
    require(a <= b, "reversed bound")
    return a, b


def window(q, delta):
    return q - delta / 2, q + delta / 2


def horner(coeffs, point):
    result = (Fraction(0), Fraction(0))
    for a, b in reversed(coeffs):
        products = [x * y for x in point for y in result]
        result = a + min(products), b + max(products)
    return result


def separated(bound):
    return 1 if bound[0] > 0 else -1 if bound[1] < 0 else None


def exact_sign(bound):
    return 0 if bound == (0, 0) else separated(bound)


def quotient(a, b):
    if separated(b) is None:
        return None
    corners = [x / y for x in a for y in b]
    return min(corners), max(corners)


def trial(num, den, q, joint, n, width):
    delta = Fraction(1, 2**n)
    box = window(q, delta)
    sources = [[window(c, delta) if joint else (c, c) for c in poly]
               for poly in (num, den)]
    nb, db = [horner(cs, box) for cs in sources]
    sn, sd = separated(nb), separated(db)
    is_zero = not any(num)
    sign = 0 if is_zero else sn * sd if sn is not None and sd is not None else None
    sn_exact = exact_sign(nb)
    finite = sn_exact * sd if sn_exact is not None and sd is not None else None
    result = (Fraction(0), Fraction(0)) if is_zero else quotient(nb, db)
    if result is not None and result[1] - result[0] > width:
        result = None
    return sources, box, nb, db, sign, finite, result


def check_horner_z3(coeffs, box, output):
    import z3
    def real(q):
        return z3.RealVal(f"{q.numerator}/{q.denominator}")
    solver = z3.SolverFor("QF_NRA")
    solver.set(timeout=10000)
    x = z3.Real("argument")
    solver.add(real(box[0]) <= x, x <= real(box[1]))
    value = real(Fraction(0))
    for i, (lo, hi) in enumerate(reversed(coeffs)):
        c = z3.Real(f"coefficient_{i}")
        solver.add(real(lo) <= c, c <= real(hi))
        value = c + x * value
    solver.add(z3.Or(value < real(output[0]), value > real(output[1])))
    require(solver.check() == z3.unsat, "Z3 did not prove the Horner enclosure")


def check_record(record):
    require(record.get("kind") == "ordered-fn-real" and record.get("lib") == "HexOrderedFn",
            "wrong library or fixture kind")
    n, joint = record["precision"], record["joint"]
    require(type(n) is int and n >= 0 and type(joint) is bool, "invalid refinement context")
    q, request = rational(record["subject"]), rational(record["request"])
    require(request == Fraction(1, 2**n), "request does not match precision")
    num, den = [[rational(c) for c in record[k]] for k in ("num", "den")]
    require(any(den), "formally zero denominator")
    width = rational(record["approx_request"])
    require(width > 0, "invalid requested width")
    cs, box, nb, db, sign, finite, result = trial(num, den, q, joint, n, width)
    require(interval(record["constant"]) == box, "constant provider/context mismatch")
    for key, expected in zip(("coeff_num", "coeff_den"), cs):
        require([interval(b) for b in record[key]] == expected, "coefficient provider/context mismatch")
    require(interval(record["num_bound"]) == nb and interval(record["den_bound"]) == db,
            "incorrect exact Horner bound")
    for key in ("attempt", "finite", "total_sign"):
        value = record[key]
        require(value is None or (type(value) is int and value in (-1, 0, 1)), "invalid sign")
    require(record["attempt"] == sign, "incorrect total-sign trial")
    require(record["finite"] == finite, "incorrect finite sign")
    require((None if record["approx_attempt"] is None else interval(record["approx_attempt"])) == result,
            "incorrect approximation trial")
    require(record["total_sign"] == sign, "total sign disagrees with successful trials")
    first = next((trial(num, den, q, joint, k, width)[-1] for k in range(n + 1)
                  if trial(num, den, q, joint, k, width)[-1] is not None), None)
    actual = None if record["total_approx"] is None else interval(record["total_approx"])
    require(actual == (first if result is not None else None), "approximation did not return the first success")
    # Each coefficient varies independently: this checks simultaneous refinement,
    # rather than just evaluating one exact rational point inside the intervals.
    check_horner_z3(cs[0], box, nb)
    check_horner_z3(cs[1], box, db)


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
                              seed=args.seed, case_id=case, kind="ordered-fn-real", input_record=record,
                              lean_output=record.get("attempt"), oracle_output=None,
                              oracle_name="Z3 real arithmetic and exact Fraction intervals",
                              oracle_version=VERSION, diff=str(exc))
                print(f"FAIL {case}: {exc}", file=sys.stderr)
        require(REQUIRED <= seen, f"missing cases: {sorted(REQUIRED - seen)}")
    finally:
        if source:
            stream.close()
    print(f"HexOrderedFn real: {len(seen)} cases, {failures} failures ({VERSION}, exact Fraction)")
    return int(failures != 0)


if __name__ == "__main__":
    raise SystemExit(main())
