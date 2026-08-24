#!/usr/bin/env python3
"""SymPy oracle for ``HexPolyZGcd`` integer and rational gcd fixtures."""
from __future__ import annotations

import argparse
import math
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexPolyZGcd" / "zgcd.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _sympy_version() -> str:
    import sympy  # type: ignore[import-not-found]

    return getattr(sympy, "__version__", "unknown")


def _int_poly(record: dict[str, Any]):
    import sympy as sp  # type: ignore[import-not-found]

    if record["kind"] != "poly" or record.get("modulus") is not None:
        raise OracleMismatch(f"expected an integer poly fixture, got {record!r}")
    x = sp.Symbol("x")
    expr = sum(int(c) * x**i for i, c in enumerate(record["coeffs"]))
    return sp.Poly(expr, x, domain=sp.ZZ)


def _rat_poly(record: dict[str, Any]):
    import sympy as sp  # type: ignore[import-not-found]

    if (
        record["kind"] != "sparsepoly"
        or record.get("domain") != "rat"
        or record.get("mod") is not None
    ):
        raise OracleMismatch(f"expected a rational sparsepoly fixture, got {record!r}")
    x = sp.Symbol("x")
    expr = sum(
        sp.Rational(int(num), int(den)) * x ** int(exponent)
        for exponent, num, den in record["terms"]
    )
    return sp.Poly(expr, x, domain=sp.QQ)


def _coeffs(poly) -> list[int]:
    if poly.is_zero:
        return []
    return [int(poly.nth(i)) for i in range(poly.degree() + 1)]


def _rat_value(poly) -> dict[str, list[int]]:
    if poly.is_zero:
        return {"num": [], "den": []}
    coeffs = [poly.nth(i) for i in range(poly.degree() + 1)]
    return {
        "num": [int(c.p) for c in coeffs],
        "den": [int(c.q) for c in coeffs],
    }


def _primitive(poly):
    if poly.is_zero:
        return poly
    content = 0
    for coefficient in _coeffs(poly):
        content = math.gcd(content, coefficient)
    return poly.exquo_ground(content)


def _normalize_positive(poly):
    if poly.is_zero or poly.LC() > 0:
        return poly
    return -poly


def _sqf_value(poly) -> list[list[int]]:
    primitive = _primitive(poly)
    if primitive.is_zero:
        return [[], [], []]
    derivative = primitive.diff()
    if derivative.is_zero:
        return [_coeffs(primitive), _coeffs(_normalize_positive(primitive)), [1]]
    repeated = primitive.gcd(derivative)
    core = _normalize_positive(primitive.exquo(repeated))
    return [_coeffs(primitive), _coeffs(core), _coeffs(repeated)]


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    cases, results = split_fixtures_results(read_fixtures(source))
    oracle_version = _sympy_version()
    failures = 0
    checked = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        lean_value = result["value"]
        try:
            if op in {"gcd", "cofactors", "is_coprime", "lcm"}:
                left_record = cases[(lib, f"{case_id}/left")]
                right_record = cases[(lib, f"{case_id}/right")]
                left = _int_poly(left_record)
                right = _int_poly(right_record)
                common = left.gcd(right)
                if op == "gcd":
                    oracle_value: Any = _coeffs(common)
                elif op == "cofactors":
                    oracle_value = (
                        [[1], [1]]
                        if left.is_zero and right.is_zero
                        else [
                            _coeffs(left.exquo(common)),
                            _coeffs(right.exquo(common)),
                        ]
                    )
                elif op == "is_coprime":
                    oracle_value = _coeffs(common) == [1]
                else:
                    oracle_value = [] if left.is_zero or right.is_zero else _coeffs(
                        _normalize_positive(left.exquo(common) * right)
                    )
                input_record: dict[str, Any] = {
                    "left": left_record,
                    "right": right_record,
                }
            elif op == "sqf":
                input_record = cases[(lib, f"{case_id}/input")]
                oracle_value = _sqf_value(_int_poly(input_record))
            elif op == "rat_gcd":
                left_record = cases[(lib, f"{case_id}/left")]
                right_record = cases[(lib, f"{case_id}/right")]
                oracle_value = _rat_value(
                    _rat_poly(left_record).gcd(_rat_poly(right_record))
                )
                input_record = {"left": left_record, "right": right_record}
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} in zgcd_sympy.py"
                )
            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{op}",
                kind=op,
                input_record=input_record,
                oracle_name="SymPy",
                oracle_version=oracle_version,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"zgcd_sympy.py: checked {checked} case(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group()
    src.add_argument("input", nargs="?", help="JSONL input (default: stdin)")
    src.add_argument(
        "--check",
        action="store_true",
        help=f"read {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)
    source = str(DEFAULT_FIXTURE) if args.check else args.input
    try:
        import sympy  # noqa: F401
    except ImportError:
        print("SKIP: SymPy not installed", file=sys.stderr)
        return 0
    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
