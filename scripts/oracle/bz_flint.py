#!/usr/bin/env python3
"""python-flint oracle driver for `hex-berlekamp-zassenhaus`.

Reads a JSONL stream produced by `lake exe hexbz_emit_fixtures` (or the
committed sample at
`conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl`) and re-runs each
operation through python-flint's `fmpz_poly` integer factorisation.  On
mismatch, writes a JSON failure record under `conformance-failures/`
and exits non-zero so CI fails the job.

Operation cross-checked
-----------------------

* `factor` — `Hex.factor` from `HexBerlekampZassenhaus.Basic` (the
  default-bound public entry point).  Lean serialises the resulting
  array of factors as a JSON array of coefficient lists; the oracle
  re-factors each Lean component with `fmpz_poly.factor()`,
  accumulates the combined integer content and irreducible-factor
  multiset, and compares against `flint.fmpz_poly.factor()` on the
  input polynomial.

  The cross-check is multiset-only: factor order is unspecified by
  SPEC, and Lean's pipeline reports content/`X`-power/repeated-part
  components separately from the LLL-recovered primitive factors.
  Re-factoring each component canonicalises the comparison: if Lean
  has a duplicate primitive irreducible split across two output
  entries the multiset still matches FLINT's multiplicity report.

  Each FLINT factor has a positive leading coefficient (FLINT's own
  normalisation); signs flow into the content unit.  We compare
  contents as signed integers and factors as coefficient tuples.

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


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _factor_signature(coeffs: list[int]) -> tuple[int, dict[tuple[int, ...], int]]:
    """Return `(content, multiset)` for the integer polynomial whose
    coefficients are `coeffs`.

    `content` is the signed integer leading content as reported by
    `fmpz_poly.factor()` (FLINT canonicalises factors to have positive
    leading coefficient and folds the sign into this content).  The
    multiset maps each canonical factor's coefficient tuple to its
    multiplicity.
    """
    f = _fmpz_poly(coeffs)
    content, factors = f.factor()
    out: Counter[tuple[int, ...]] = Counter()
    for g, m in factors:
        # FLINT factors are already content-free with positive leading
        # coefficient.  `tuple(g.coeffs())` keys uniquely up to that
        # canonicalisation.
        key = tuple(int(c) for c in g.coeffs())
        out[key] += int(m)
    return int(content), dict(out)


def _combine_signature(
    components: list[list[int]],
) -> tuple[int, dict[tuple[int, ...], int]]:
    """Re-factor each Lean output component and accumulate the
    combined `(content, multiset)`.

    Constant components contribute only to the content.  Empty arrays
    (i.e. recombination failures reported by Lean) collapse to content
    `1` and the empty multiset, so the oracle reports a clean diff
    against FLINT's true factorisation.
    """
    total_content = 1
    out: Counter[tuple[int, ...]] = Counter()
    for coeffs in components:
        if not coeffs:
            continue
        content, factors = _factor_signature(coeffs)
        total_content *= content
        for key, m in factors.items():
            out[key] += m
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
    flint_sig = _factor_signature(coeffs)

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
    lean_sig = _combine_signature(lean_components)

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
