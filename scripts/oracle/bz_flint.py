#!/usr/bin/env python3
"""python-flint oracle driver for `hex-berlekamp-zassenhaus`.

Reads a JSONL stream produced by `lake exe hexbz_emit_fixtures` (or the
committed sample at
`conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl`) and re-runs each
operation through python-flint's `fmpz_poly` integer factorisation.  On
mismatch, writes a JSON failure record under `conformance-failures/`
and exits non-zero so CI fails the job.

Fixture records may also carry optional pinned modular-factor metadata:
``modFactorPrime`` plus ``modFactorDegrees``.  When present, this driver
independently factors the integer input reduced modulo that prime and
checks the sorted irreducible factor degree multiset.  Plain historical
``factor`` fixtures omit these fields and keep the original behaviour.

Operation cross-checked
-----------------------

* `factor` — `Hex.factor` from `HexBerlekampZassenhaus.Basic` (the
  default-bound public entry point).  Lean serialises the resulting
  array of factors as a JSON array of coefficient lists.  The oracle
  factors the original input once with `fmpz_poly.factor()` and compares
  Lean's reported components directly against that irreducible-factor
  multiset after primitive normalisation.

  Factor order is unspecified by SPEC.  Each nonconstant Lean component
  must be one irreducible factor slot from FLINT's factorisation; the
  oracle never re-factors Lean's output as a canonicalisation step.
  This rejects unfactored or partially factored reducible components.
  Content and signs are accumulated separately, matching FLINT's
  positive-leading-factor convention.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexbz_emit_fixtures | \\
        python3 scripts/oracle/bz_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/bz_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/bz_flint.py path/to/file.jsonl

`--check` is exactly equivalent to passing
``conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl``.
"""
from __future__ import annotations

import argparse
import math
import os
import sys
from collections import Counter
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexBerlekampZassenhaus" / "bz.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _trim_zeros(coeffs) -> list[int]:
    """Match Lean's normalised representation: drop trailing zeros and
    cast `fmpz`-like coefficients down to native Python `int`."""
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _coeffs(record: dict[str, Any]) -> list[int]:
    if record["kind"] != "poly":
        raise ValueError(f"expected poly record, got {record['kind']}")
    if record.get("modulus") is not None:
        raise ValueError(
            f"bz_flint.py: integer (non-modular) fixture required (case "
            f"{record['lib']}/{record['case']})"
        )
    return list(record["coeffs"])


def _fmpz_poly(coeffs: list[int]):
    from flint import fmpz_poly  # type: ignore[import-not-found]
    return fmpz_poly([int(c) for c in coeffs])


def _nmod_poly(coeffs: list[int], p: int):
    from flint import nmod_poly  # type: ignore[import-not-found]
    return nmod_poly([int(c) % p for c in coeffs], p)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _primitive_component(
    coeffs: list[int],
) -> tuple[int, tuple[int, ...] | None]:
    """Split one Lean component into `(content, primitive_factor)`.

    Nonconstant primitive factors are normalised to positive leading
    coefficient.  Constant components contribute only to content.
    """
    coeffs = _trim_zeros(coeffs)
    if not coeffs:
        raise OracleMismatch("zero polynomial is not a valid factor component")
    if len(coeffs) == 1:
        return int(coeffs[0]), None

    content = 0
    for c in coeffs:
        content = math.gcd(content, abs(int(c)))
    if content == 0:
        raise OracleMismatch("zero polynomial is not a valid factor component")
    if coeffs[-1] < 0:
        content = -content
    primitive = tuple(int(c // content) for c in coeffs)
    return int(content), primitive


def _oracle_signature(coeffs: list[int]) -> tuple[int, dict[tuple[int, ...], int]]:
    """Return FLINT's canonical `(content, irreducible multiset)`.

    `content` is the signed integer leading content reported by
    `fmpz_poly.factor()`.  Each factor has positive leading coefficient.
    """
    f = _fmpz_poly(coeffs)
    content, factors = f.factor()
    out: Counter[tuple[int, ...]] = Counter()
    for g, m in factors:
        key = tuple(int(c) for c in g.coeffs())
        out[key] += int(m)
    return int(content), dict(out)


def _lean_signature(
    components: list[list[int]],
) -> tuple[int, dict[tuple[int, ...], int]]:
    """Accumulate Lean's direct primitive-factor report.

    This intentionally does not call `factor()` on the components.  A
    reducible component remains a single key and will fail comparison
    against FLINT's irreducible-factor multiset.
    """
    total_content = 1
    out: Counter[tuple[int, ...]] = Counter()
    for coeffs in components:
        if not coeffs:
            raise OracleMismatch("empty coefficient list is not a valid factor")
        content, factor = _primitive_component(coeffs)
        total_content *= content
        if factor is not None:
            out[factor] += 1
    return total_content, dict(out)


def _signature_to_serialisable(
    sig: tuple[int, dict[tuple[int, ...], int]],
) -> dict[str, Any]:
    """Convert a `(content, multiset)` signature into a JSON-friendly
    record so failure diffs round-trip through `assert_equal`."""
    content, multiset = sig
    items = sorted(
        (list(coeffs), mult) for coeffs, mult in multiset.items()
    )
    return {"content": int(content), "factors": items}


def _mod_factor_degrees(coeffs: list[int], p: int) -> list[int]:
    if p <= 1:
        raise OracleMismatch(f"modFactorPrime must be > 1, got {p}")
    f = _nmod_poly(coeffs, p)
    if f.is_zero():
        raise OracleMismatch(
            f"input reduces to zero modulo pinned prime {p}"
        )
    _unit, factors = f.factor()
    degrees: list[int] = []
    for factor, multiplicity in factors:
        degree = int(factor.degree())
        for _ in range(int(multiplicity)):
            degrees.append(degree)
    return sorted(degrees)


def _check_mod_factor_metadata(
    *,
    case_id: str,
    lib: str,
    poly_record: dict[str, Any],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    p = poly_record.get("modFactorPrime")
    expected = poly_record.get("modFactorDegrees")
    if p is None and expected is None:
        return
    if not isinstance(p, int) or not isinstance(expected, list) or not all(
        isinstance(deg, int) and deg > 0 for deg in expected
    ):
        raise OracleMismatch(
            f"{lib}/{case_id}: invalid pinned modular-factor metadata"
        )
    coeffs = _coeffs(poly_record)
    actual = _mod_factor_degrees(coeffs, p)
    assert_equal(
        actual,
        sorted(expected),
        library=lib,
        case_id=f"{case_id}:modFactorDegrees",
        kind="modFactorDegrees",
        input_record=poly_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )


def _check_factor(
    *,
    case_id: str,
    lib: str,
    poly_record: dict[str, Any],
    lean_value: list[Any],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    coeffs = _coeffs(poly_record)
    _check_mod_factor_metadata(
        case_id=case_id, lib=lib, poly_record=poly_record,
        failure_dir=failure_dir, profile=profile, seed=seed,
        oracle_version=oracle_version,
    )
    flint_sig = _oracle_signature(coeffs)

    if not isinstance(lean_value, list) or not all(
        isinstance(component, list)
        and all(isinstance(c, int) for c in component)
        for component in lean_value
    ):
        raise OracleMismatch(
            f"{lib}/{case_id}: factor result must be a list of "
            f"coefficient lists, got {lean_value!r}"
        )
    lean_components = [_trim_zeros(component) for component in lean_value]
    lean_sig = _lean_signature(lean_components)

    assert_equal(
        _signature_to_serialisable(lean_sig),
        _signature_to_serialisable(flint_sig),
        library=lib,
        case_id=f"{case_id}:factor",
        kind="factor",
        input_record=poly_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )


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
        poly_record = cases.get((lib, case_id))
        if poly_record is None:
            print(
                f"FAIL {lib}/{case_id} ({op}): missing poly fixture",
                file=sys.stderr,
            )
            failures += 1
            continue
        try:
            if op == "factor":
                _check_factor(
                    case_id=case_id, lib=lib, poly_record=poly_record,
                    lean_value=lean_value,
                    failure_dir=failure_dir, profile=profile, seed=seed,
                    oracle_version=oracle_version,
                )
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} "
                    f"in bz_flint.py; extend the driver."
                )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"bz_flint.py: checked {checked} case(s), {failures} failure(s)",
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
        # Mirror SPEC's `if_available` mode: a missing oracle is a
        # skip, not a failure.  CI installs python-flint before this
        # script runs.
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
