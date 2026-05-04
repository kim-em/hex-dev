#!/usr/bin/env python3
"""python-flint oracle driver for ``hex-poly-z``.

Reads a JSONL stream produced by ``lake exe hexpolyz_emit_fixtures``
(or the committed sample at
``conformance-fixtures/HexPolyZ/polyz.jsonl``) and re-runs each
operation through python-flint's ``fmpz_poly``::

* ``content``               — ``fmpz_poly.content``
* ``primitive_part``        — ``fmpz_poly`` divided by its content
  (python-flint exposes ``content`` but not a direct ``primitive_part``;
  ``f // content(f)`` is FLINT's standard idiom).
* ``gcd_z``                 — ``fmpz_poly.gcd``
* ``divmod``                — ``divmod(fmpz_poly, fmpz_poly)``
* ``mignotte_coeff_bound``  — ``binom(k, j) * ceil_sqrt(∑ cᵢ²)``,
  recomputed from the raw coefficient list.

The script is intentionally narrow in what operations it understands.
On mismatch it writes a JSON failure record under
``conformance-failures/`` and exits non-zero so CI fails the job.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexpolyz_emit_fixtures | python3 scripts/oracle/polyz_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/polyz_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/polyz_flint.py path/to/file.jsonl
"""
from __future__ import annotations

import argparse
import math
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexPolyZ" / "polyz.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _trim_zeros(coeffs) -> list[int]:
    """Match Lean's normalised representation: cast `fmpz` coefficients
    down to native Python `int` and drop trailing zeros."""
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _coeffs(record: dict[str, Any]) -> list[int]:
    if record["kind"] != "poly":
        raise ValueError(f"expected poly record, got {record['kind']}")
    if record.get("modulus") is not None:
        raise NotImplementedError(
            f"polyz_flint.py: modular fixtures not supported "
            f"(case {record['lib']}/{record['case']})"
        )
    return list(record["coeffs"])


def _fmpz_poly(coeffs: list[int]):
    from flint import fmpz_poly  # type: ignore[import-not-found]
    return fmpz_poly(coeffs)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _ceil_sqrt(n: int) -> int:
    """Match `Hex.ZPoly.ceilSqrt`: smallest `r` with `r*r ≥ n`."""
    r = math.isqrt(n)
    return r if r * r == n else r + 1


def _binom(n: int, k: int) -> int:
    """Match `Hex.ZPoly.binom`: zero when `k > n`, otherwise the
    standard symmetric formula."""
    if k > n:
        return 0
    if k < 0:
        return 0
    k = min(k, n - k)
    out = 1
    for i in range(k):
        out = out * (n - i) // (i + 1)
    return out


def _mignotte(coeffs: list[int], k: int, j: int) -> int:
    norm_sq = sum(c * c for c in coeffs)
    return _binom(k, j) * _ceil_sqrt(norm_sq)


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    cases, results = split_fixtures_results(read_fixtures(source))
    oracle_version = _flint_version()
    failures = 0
    checked = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        lean_value = result["value"]
        try:
            if op == "content":
                input_record = cases[(lib, f"{case_id}/input")]
                p = _fmpz_poly(_coeffs(input_record))
                oracle_value = int(p.content())
            elif op == "primitive_part":
                input_record = cases[(lib, f"{case_id}/input")]
                p = _fmpz_poly(_coeffs(input_record))
                content = int(p.content())
                if content == 0:
                    oracle_value: list[int] = []
                else:
                    oracle_value = _trim_zeros(list((p // content).coeffs()))
            elif op == "gcd_z":
                left = cases[(lib, f"{case_id}/left")]
                right = cases[(lib, f"{case_id}/right")]
                p = _fmpz_poly(_coeffs(left))
                q = _fmpz_poly(_coeffs(right))
                oracle_value = _trim_zeros(list(p.gcd(q).coeffs()))
                input_record = {"left": left, "right": right}
            elif op == "divmod":
                dividend = cases[(lib, f"{case_id}/dividend")]
                divisor = cases[(lib, f"{case_id}/divisor")]
                a = _fmpz_poly(_coeffs(dividend))
                b = _fmpz_poly(_coeffs(divisor))
                quot, rem = divmod(a, b)
                oracle_value = [
                    _trim_zeros(list(quot.coeffs())),
                    _trim_zeros(list(rem.coeffs())),
                ]
                input_record = {"dividend": dividend, "divisor": divisor}
            elif op == "mignotte_coeff_bound":
                if (
                    not isinstance(lean_value, list)
                    or len(lean_value) != 3
                    or not all(isinstance(x, int) for x in lean_value)
                ):
                    raise OracleMismatch(
                        f"{lib}/{case_id} (mignotte_coeff_bound): "
                        f"value must be [k, j, bound], got {lean_value!r}"
                    )
                input_record = cases[(lib, f"{case_id}/input")]
                k, j, lean_bound = lean_value
                oracle_value = [k, j, _mignotte(_coeffs(input_record), k, j)]
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} "
                    f"in polyz_flint.py; extend the driver."
                )
            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{op}",
                kind=op,
                input_record=(
                    input_record
                    if isinstance(input_record, dict)
                    else {"input": input_record}
                ),
                oracle_name="python-flint",
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
        f"polyz_flint.py: checked {checked} case(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group()
    src.add_argument(
        "input",
        nargs="?",
        help="JSONL fixture path (default: stdin)",
    )
    src.add_argument(
        "--check",
        action="store_true",
        help=f"read the committed sample at {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
        help="directory for JSON failure records",
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)

    if args.check:
        source: str | None = str(DEFAULT_FIXTURE)
    else:
        source = args.input  # may be None → stdin

    try:
        import flint  # noqa: F401  (presence check)
    except ImportError:
        print("SKIP: python-flint not installed", file=sys.stderr)
        return 0

    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
