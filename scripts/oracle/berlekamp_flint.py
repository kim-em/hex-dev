#!/usr/bin/env python3
"""python-flint oracle driver for `hex-berlekamp`.

Reads a JSONL stream produced by `lake exe hexberlekamp_emit_fixtures`
(or the committed sample at
`conformance-fixtures/HexBerlekamp/berlekamp.jsonl`) and re-runs each
operation through python-flint's `nmod_poly` factorisation.  On
mismatch, writes a JSON failure record under `conformance-failures/`
and exits non-zero so CI fails the job.

Operations cross-checked
------------------------

* `rabin` — `Berlekamp.rabinTest` (Bool).  python-flint factors the
  input and reports irreducibility iff the factorisation has exactly
  one factor of multiplicity 1 and the expected total degree.
* `ddf` — `Berlekamp.distinctDegreeFactor` (degree-bucketed factor
  product + residual).  python-flint cross-checks two invariants:
  (a) `∏ bucket_factors * residual == f` always (Lean's bucket-product
  invariant); (b) for square-free `f`, each bucket's polynomial
  matches the product of FLINT's irreducible factors of that degree
  exactly.  Non-square-free inputs skip (b) — Lean's DDF buckets are
  only canonical for square-free input.

Square-free decomposition is intentionally not cross-checked here;
see `HexBerlekamp/EmitFixtures.lean` for the rationale.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexberlekamp_emit_fixtures | \\
        python3 scripts/oracle/berlekamp_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/berlekamp_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/berlekamp_flint.py path/to/file.jsonl

`--check` is exactly equivalent to passing
``conformance-fixtures/HexBerlekamp/berlekamp.jsonl``.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexBerlekamp" / "berlekamp.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

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


def _coeffs(record: dict[str, Any]) -> tuple[list[int], int]:
    if record["kind"] != "poly":
        raise ValueError(f"expected poly record, got {record['kind']}")
    modulus = record.get("modulus")
    if not isinstance(modulus, int):
        raise ValueError(
            f"berlekamp_flint.py: modular fixture required (case "
            f"{record['lib']}/{record['case']})"
        )
    return list(record["coeffs"]), modulus


def _nmod_poly(coeffs: list[int], p: int):
    from flint import nmod_poly  # type: ignore[import-not-found]
    return nmod_poly(coeffs, p)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _monic_normalize(g):
    """Divide a non-zero `nmod_poly` by its leading coefficient.

    Lean's `DensePoly.gcd` over a field normalises only up to a unit;
    FLINT's factorisation returns monic factors.  To compare the two
    we monic-normalise both sides."""
    coeffs = list(g.coeffs())
    if not coeffs:
        return g
    # `nmod_poly` over a prime modulus is a field; division is well-defined.
    lead = coeffs[-1]
    if lead == 0:
        return g
    inv = pow(int(lead), -1, int(g.modulus()))
    from flint import nmod_poly  # type: ignore[import-not-found]
    return g * nmod_poly([inv], int(g.modulus()))


def _factor_pairs(f) -> list[tuple[Any, int]]:
    """Return `[(factor_poly, multiplicity), ...]` from FLINT's
    `nmod_poly.factor()`.  Drops the leading-coefficient unit.

    `flint.nmod_poly.factor()` returns `(unit, [(factor, mult), ...])`.
    Each factor is monic; the `unit` is the leading coefficient.
    """
    _unit, parts = f.factor()
    return [(g, int(m)) for (g, m) in parts]


def _is_irreducible(f, total_degree: int) -> bool:
    """`f` is irreducible iff its factorisation has exactly one
    factor of multiplicity 1 with full degree."""
    pairs = _factor_pairs(f)
    return (
        len(pairs) == 1
        and pairs[0][1] == 1
        and pairs[0][0].degree() == total_degree
    )


def _is_squarefree(f) -> bool:
    return all(m == 1 for (_, m) in _factor_pairs(f))


def _grouped_by_degree(pairs: list[tuple[Any, int]], p: int):
    """Group factor pairs by degree into `{deg: product_poly}`.

    Each value is the product of all factors of that degree, with
    multiplicities included (so for square-free input each factor
    appears once)."""
    from flint import nmod_poly  # type: ignore[import-not-found]
    out: dict[int, Any] = {}
    for g, m in pairs:
        d = g.degree()
        prod = out.get(d, nmod_poly([1], p))
        for _ in range(m):
            prod = prod * g
        out[d] = prod
    return out


def _check_rabin(
    *,
    case_id: str,
    lib: str,
    poly_record: dict[str, Any],
    lean_value: bool,
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    coeffs, p = _coeffs(poly_record)
    f = _nmod_poly(coeffs, p)
    oracle_value = _is_irreducible(f, f.degree())
    assert_equal(
        lean_value,
        oracle_value,
        library=lib,
        case_id=f"{case_id}:rabin",
        kind="rabin",
        input_record=poly_record,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )


def _check_ddf(
    *,
    case_id: str,
    lib: str,
    poly_record: dict[str, Any],
    lean_value: dict[str, Any],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    coeffs, p = _coeffs(poly_record)
    from flint import nmod_poly  # type: ignore[import-not-found]
    f = _nmod_poly(coeffs, p)

    lean_buckets = lean_value["buckets"]  # list of [degree, [coeffs]]
    lean_residual_coeffs = lean_value["residual"]
    lean_residual = _nmod_poly(lean_residual_coeffs, p)

    # (a) Always verify Lean's bucket-product invariant: the buckets
    # times the residual reconstruct the input.
    lean_product = nmod_poly([1], p)
    for _, bucket_coeffs in lean_buckets:
        lean_product = lean_product * _nmod_poly(bucket_coeffs, p)
    lean_product = lean_product * lean_residual
    if lean_product != f:
        assert_equal(
            _trim_zeros(list(f.coeffs())),
            _trim_zeros(list(lean_product.coeffs())),
            library=lib,
            case_id=f"{case_id}:ddf-product",
            kind="ddf-product",
            input_record=poly_record,
            oracle_name="python-flint",
            oracle_version=oracle_version,
            failure_dir=failure_dir,
            profile=profile,
            seed=seed,
        )

    # (b) For square-free input, each Lean bucket equals the FLINT
    # product of irreducible factors of that degree.  The residual
    # must equal `1`.
    if not _is_squarefree(f):
        return
    flint_pairs = _factor_pairs(f)
    flint_groups = _grouped_by_degree(flint_pairs, p)
    if _trim_zeros(list(lean_residual.coeffs())) != [1]:
        assert_equal(
            _trim_zeros(list(lean_residual.coeffs())),
            [1],
            library=lib,
            case_id=f"{case_id}:ddf-residual",
            kind="ddf-residual",
            input_record=poly_record,
            oracle_name="python-flint",
            oracle_version=oracle_version,
            failure_dir=failure_dir,
            profile=profile,
            seed=seed,
        )
    # Lean's `DensePoly.gcd` over a field is canonical only up to a
    # unit; FLINT's `nmod_poly.factor` returns monic factors.  Compare
    # both sides after monic normalisation.
    lean_groups = {int(deg): _monic_normalize(_nmod_poly(bucket_coeffs, p))
                   for deg, bucket_coeffs in lean_buckets}
    flint_groups = {d: _monic_normalize(g) for d, g in flint_groups.items()}
    all_degrees = set(lean_groups) | set(flint_groups)
    for d in sorted(all_degrees):
        lean_g = lean_groups.get(d, nmod_poly([1], p))
        flint_g = flint_groups.get(d, nmod_poly([1], p))
        if lean_g != flint_g:
            assert_equal(
                _trim_zeros(list(lean_g.coeffs())),
                _trim_zeros(list(flint_g.coeffs())),
                library=lib,
                case_id=f"{case_id}:ddf-deg{d}",
                kind="ddf-bucket",
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
            if op == "rabin":
                _check_rabin(
                    case_id=case_id, lib=lib, poly_record=poly_record,
                    lean_value=bool(lean_value),
                    failure_dir=failure_dir, profile=profile, seed=seed,
                    oracle_version=oracle_version,
                )
            elif op == "ddf":
                _check_ddf(
                    case_id=case_id, lib=lib, poly_record=poly_record,
                    lean_value=lean_value,
                    failure_dir=failure_dir, profile=profile, seed=seed,
                    oracle_version=oracle_version,
                )
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} "
                    f"in berlekamp_flint.py; extend the driver."
                )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"berlekamp_flint.py: checked {checked} case(s), {failures} failure(s)",
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
