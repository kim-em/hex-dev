#!/usr/bin/env python3
"""python-flint oracle driver for `hex-poly`.

Reads a JSONL stream produced by `lake exe hexpoly_emit_fixtures`
(or the committed sample at `conformance-fixtures/HexPoly/poly.jsonl`)
and re-runs each `mul` / `divmod` / `gcd` operation through
python-flint's `fmpz_poly` / `fmpq_poly`.  On mismatch, writes a JSON
failure record under `conformance-failures/` and exits non-zero so
CI fails the job.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexpoly_emit_fixtures | python3 scripts/oracle/poly_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/poly_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/poly_flint.py path/to/file.jsonl

`--check` is exactly equivalent to passing
``conformance-fixtures/HexPoly/poly.jsonl`` and is the form CI also
uses for the regression sentinel: if Lean's emission ever drifts from
the committed sample, the next agent regenerating the file should
note the diff in their progress entry.

Operations:

* ``mul`` and ``divmod`` are cross-checked over ``fmpz_poly`` (Z[x]).
  Lean's integer multiplication and exact integer division match
  FLINT's outputs verbatim.
* ``gcd`` is cross-checked over ``fmpq_poly`` (Q[x]) up to the monic
  associate.  ``Hex.DensePoly Int.gcd`` is structurally unsuitable for
  Z[x] gcd cross-check (truncating integer division destroys the
  Euclidean trajectory), so EmitFixtures runs gcd over ``DensePoly Rat``
  and emits the rational result as parallel ``num`` / ``den`` arrays.
  Both Lean's value and FLINT's are normalised to monic before
  comparison.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexPoly" / "poly.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

# Allow `import scripts.oracle.common` even when the script is invoked
# directly (rather than via `python -m`).
sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _trim_zeros(coeffs) -> list[int]:
    """Match Lean's normalised representation: cast fmpz/Fraction-like
    coefficients down to native Python `int` and drop trailing zeros."""
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _coeffs(record: dict[str, Any]) -> list[int]:
    if record["kind"] != "poly":
        raise ValueError(f"expected poly record, got {record['kind']}")
    if record.get("modulus") is not None:
        # F_p[x] cross-checks live in HexPolyFp (#1989), not here.
        raise NotImplementedError(
            f"poly_flint.py: modular fixtures not supported "
            f"(case {record['lib']}/{record['case']})"
        )
    return list(record["coeffs"])


def _fmpz_poly(coeffs: list[int]):
    from flint import fmpz_poly  # type: ignore[import-not-found]
    return fmpz_poly(coeffs)


def _fmpq_poly(coeffs):
    """Build an `fmpq_poly` from either ``list[int]`` (treated as
    integer coefficients) or a parallel ``(nums, dens)`` pair."""
    from flint import fmpq, fmpq_poly  # type: ignore[import-not-found]
    if isinstance(coeffs, tuple):
        nums, dens = coeffs
        return fmpq_poly([fmpq(int(n), int(d)) for n, d in zip(nums, dens)])
    return fmpq_poly([fmpq(int(c), 1) for c in coeffs])


def _monic_qq_coeffs(p) -> list[tuple[int, int]]:
    """Return the monic associate of ``p`` (an `fmpq_poly`) as a list
    of ``(numerator, denominator)`` pairs (denominator > 0).  Returns
    ``[]`` for the zero polynomial."""
    from flint import fmpq  # type: ignore[import-not-found]
    if p.degree() < 0:
        return []
    lead = fmpq(p.coeffs()[-1])
    monic = p / lead
    out: list[tuple[int, int]] = []
    for c in monic.coeffs():
        q = fmpq(c)
        out.append((int(q.p), int(q.q)))
    return out


def _normalise_lean_gcd_value(value: dict[str, Any]):
    """Build an `fmpq_poly` from the Lean ``{"num":[...],"den":[...]}``
    result-value shape and return the monic associate as
    ``(numerator, denominator)`` pairs."""
    nums = value.get("num")
    dens = value.get("den")
    if not isinstance(nums, list) or not isinstance(dens, list):
        raise ValueError(f"gcd value must be {{'num': [...], 'den': [...]}}: {value!r}")
    if len(nums) != len(dens):
        raise ValueError(
            f"gcd value: num/den length mismatch ({len(nums)} vs {len(dens)})"
        )
    return _monic_qq_coeffs(_fmpq_poly((nums, dens)))


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


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
            if op == "mul":
                left = cases[(lib, f"{case_id}/left")]
                right = cases[(lib, f"{case_id}/right")]
                p = _fmpz_poly(_coeffs(left))
                q = _fmpz_poly(_coeffs(right))
                oracle_value = _trim_zeros(list((p * q).coeffs()))
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
            elif op == "gcd":
                # Lean's `Hex.DensePoly Rat.gcd` returns a rational
                # scalar associate of the true gcd; FLINT's
                # `fmpq_poly.gcd` returns the monic associate.  We
                # compare both after normalising to monic.
                left = cases[(lib, f"{case_id}/left")]
                right = cases[(lib, f"{case_id}/right")]
                p = _fmpq_poly(_coeffs(left))
                q = _fmpq_poly(_coeffs(right))
                if not isinstance(lean_value, dict):
                    raise OracleMismatch(
                        f"{lib}/{case_id}: gcd result-value must be a "
                        f"{{'num': [...], 'den': [...]}} object, got {lean_value!r}"
                    )
                oracle_value = _monic_qq_coeffs(p.gcd(q))
                lean_value = _normalise_lean_gcd_value(lean_value)
                input_record = {"left": left, "right": right}
            else:
                # Unknown op = oracle-side bug (Lean emitted something we
                # don't know how to verify).  Fail loudly so the gap is
                # caught immediately rather than silently passing.
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} "
                    f"in poly_flint.py; extend the driver."
                )
            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{op}",
                kind=op,
                input_record=input_record,
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
        f"poly_flint.py: checked {checked} case(s), {failures} failure(s)",
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
        # Mirror the SPEC's `if_available` mode: a missing oracle is a
        # skip, not a failure.  CI invokes `pip install python-flint`
        # before this script, so a failure here in CI means install
        # failed.
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
