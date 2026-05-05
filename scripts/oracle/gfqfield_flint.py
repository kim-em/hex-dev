#!/usr/bin/env python3
"""python-flint oracle driver for `hex-gfq-field`.

Reads a JSONL stream produced by `lake exe hexgfqfield_emit_fixtures`
(or the committed sample at
`conformance-fixtures/HexGfqField/gfqfield.jsonl`) and re-runs each
finite-field operation through python-flint's `fq_default_ctx`
configured with the same explicit modulus.  On mismatch, writes a
JSON failure record under `conformance-failures/` and exits non-zero
so CI fails the job.

Operations cross-checked
------------------------

* ``mul``  — Lean returns the canonical `(a * b) mod m` over `F_p`.
  python-flint computes ``a * b`` in ``fq_default_ctx(p, modulus=m)``.
* ``inv``  — Lean returns the canonical `a⁻¹` (well-defined: `a` is
  nonzero in every emitted case).  python-flint computes ``a ** (-1)``.
* ``div``  — Lean returns ``a / b`` (well-defined: `b` is nonzero).
  python-flint computes ``a / b``.
* ``frob`` — Lean returns the Frobenius `a^p`.  python-flint
  computes ``a ** p``.
* ``zpow`` — Lean returns `a^zexp` for the integer exponent carried
  by the fixture.  python-flint computes ``a ** zexp``.

Lean serialises canonical reduced field elements as ascending
coefficient lists with trailing zeros trimmed.  python-flint
reproduces that exact form via ``fq_default.polynomial().coeffs()``
plus a ``_trim_zeros`` pass.  Both representations agree because we
hand python-flint the same modulus polynomial that Lean reduced
against.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexgfqfield_emit_fixtures | \\
        python3 scripts/oracle/gfqfield_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/gfqfield_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/gfqfield_flint.py path/to/file.jsonl

``--check`` is exactly equivalent to passing
``conformance-fixtures/HexGfqField/gfqfield.jsonl``.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexGfqField" / "gfqfield.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _trim_zeros(coeffs) -> list[int]:
    """Cast python-flint coefficients to native ints and drop trailing
    zeros so the result matches Lean's canonical normalised form."""
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _coeffs(elem) -> list[int]:
    """Return ``elem`` as a coefficient list ascending in degree, trimmed
    to match Lean's canonical reduced representation."""
    return _trim_zeros(list(elem.polynomial().coeffs()))


def _ctx(p: int, modulus_coeffs: list[int]):
    """Build an `fq_default_ctx` over `F_p[x] / m(x)`."""
    from flint import fmpz_mod_poly_ctx, fq_default_ctx  # type: ignore[import-not-found]
    poly_ctx = fmpz_mod_poly_ctx(p)
    modulus = poly_ctx(modulus_coeffs)
    return fq_default_ctx(modulus=modulus)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _gfqfield_inputs(record: dict[str, Any]) -> tuple[int, list[int], list[int], list[int], int]:
    if record["kind"] != "gfqfield":
        raise ValueError(f"expected gfqfield record, got {record['kind']}")
    return (
        int(record["p"]),
        list(record["modulus"]),
        list(record["a"]),
        list(record["b"]),
        int(record["zexp"]),
    )


def _check_op(
    *,
    case_id: str,
    lib: str,
    fixture: dict[str, Any],
    op: str,
    lean_value: list[int],
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    p, m_coeffs, a_coeffs, b_coeffs, zexp = _gfqfield_inputs(fixture)
    ctx = _ctx(p, m_coeffs)
    a = ctx(a_coeffs)
    b = ctx(b_coeffs)
    if op == "mul":
        oracle_value = _coeffs(a * b)
    elif op == "inv":
        oracle_value = _coeffs(a ** (-1))
    elif op == "div":
        oracle_value = _coeffs(a / b)
    elif op == "frob":
        oracle_value = _coeffs(a ** p)
    elif op == "zpow":
        oracle_value = _coeffs(a ** zexp)
    else:
        raise OracleMismatch(
            f"{lib}/{case_id}: unsupported op {op!r} in gfqfield_flint.py; "
            f"extend the driver."
        )
    lean_normalised = _trim_zeros(lean_value)
    assert_equal(
        lean_normalised,
        oracle_value,
        library=lib,
        case_id=f"{case_id}:{op}",
        kind=op,
        input_record=fixture,
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
        fixture = cases.get((lib, case_id))
        if fixture is None:
            print(
                f"FAIL {lib}/{case_id} ({op}): missing gfqfield fixture",
                file=sys.stderr,
            )
            failures += 1
            continue
        if fixture["kind"] != "gfqfield":
            print(
                f"FAIL {lib}/{case_id} ({op}): expected gfqfield fixture, "
                f"got {fixture['kind']!r}",
                file=sys.stderr,
            )
            failures += 1
            continue
        try:
            _check_op(
                case_id=case_id, lib=lib, fixture=fixture, op=op,
                lean_value=lean_value,
                failure_dir=failure_dir, profile=profile, seed=seed,
                oracle_version=oracle_version,
            )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"gfqfield_flint.py: checked {checked} case(s), {failures} failure(s)",
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
