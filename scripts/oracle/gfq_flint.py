#!/usr/bin/env python3
"""python-flint oracle driver for `hex-gfq` packed/generic bridge.

Reads a JSONL stream produced by `lake exe hexgfq_emit_fixtures`
(or the committed sample at `conformance-fixtures/HexGfq/gfq.jsonl`)
and re-runs each operation through python-flint's `nmod_poly(p)`
arithmetic plus explicit reduction by the modulus `m(x)` over `F_p`.
Each python-flint result is compared independently against both the
packed (`HexGF2.GF2n`) and the generic (`HexGfqField.FiniteField`)
Lean answers.  On mismatch, writes a JSON failure record under
`conformance-failures/` and exits non-zero so CI fails the job.

Operations cross-checked
------------------------

* ``add``  — Lean returns `(a + b) mod m` over `F_p`.  python-flint
  computes `(nmod_poly(a, p) + nmod_poly(b, p)) % nmod_poly(m, p)`.
* ``mul``  — Lean returns `(a * b) mod m` over `F_p`.  python-flint
  computes `(nmod_poly(a, p) * nmod_poly(b, p)) % nmod_poly(m, p)`.
* ``inv``  — Lean returns the multiplicative inverse `a⁻¹ mod m`.
  python-flint reduces `a` to its canonical form, runs
  `nmod_poly.gcdex` for the Bezout identity, and normalises the
  resulting Bezout coefficient by the gcd's leading coefficient.
* ``frob`` — Lean returns the Frobenius image `a^p`.  python-flint
  computes `nmod_poly_powmod(a, p, m)` via repeated multiplication
  modulo `m`.

The op-name encoding is `<rep>_<op>` (one of ``packed_add``,
``generic_add``, ``packed_mul``, ``generic_mul``, ``packed_inv``,
``generic_inv``, ``packed_frob``, ``generic_frob``); the python-flint
answer is the same regardless of which Lean rep emitted the result,
but reporting the rep separately on failure makes it obvious whether
the bug is in the packed `GF2n` path, the generic `GFqField` path, or
both.

Both Lean reps serialise the canonical reduced polynomial as a
coefficient list ascending in degree, with trailing zeros trimmed.
python-flint reproduces that exact form via `nmod_poly.coeffs()` plus
a `_trim_zeros` pass.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexgfq_emit_fixtures | \\
        python3 scripts/oracle/gfq_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/gfq_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/gfq_flint.py path/to/file.jsonl

`--check` is exactly equivalent to passing
``conformance-fixtures/HexGfq/gfq.jsonl``.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexGfq" / "gfq.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


REP_OPS = {
    "packed_add":   "add",
    "generic_add":  "add",
    "packed_mul":   "mul",
    "generic_mul":  "mul",
    "packed_inv":   "inv",
    "generic_inv":  "inv",
    "packed_frob":  "frob",
    "generic_frob": "frob",
}


def _trim_zeros(coeffs) -> list[int]:
    """Cast python-flint coefficients down to native ints and drop
    trailing zeros so the result matches Lean's canonical normalised
    form."""
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _nmod_poly(coeffs: list[int], p: int):
    from flint import nmod_poly  # type: ignore[import-not-found]
    return nmod_poly(coeffs, p)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _reduce(poly, modulus):
    """Canonical polynomial reduction `poly mod modulus` matching
    Lean's `FpPoly` form (trailing zeros trimmed)."""
    return _trim_zeros(list((poly % modulus).coeffs()))


def _inverse(a, modulus):
    """`a⁻¹ mod modulus` via the extended GCD identity, normalised so
    that the gcd is the constant 1.  Raises if `a` is not coprime to
    the modulus."""
    g, s, _t = a.xgcd(modulus)
    g_coeffs = list(g.coeffs())
    if not g_coeffs:
        raise OracleMismatch(
            "gfq_flint.py: xgcd returned zero gcd; operand is divisible "
            "by the modulus and has no inverse"
        )
    if len(g_coeffs) != 1:
        raise OracleMismatch(
            f"gfq_flint.py: xgcd returned non-constant gcd "
            f"{g_coeffs!r}; operand is not coprime to the modulus"
        )
    leading = int(g_coeffs[-1])
    p = modulus.modulus()
    inv_lead = pow(leading, -1, p)
    s_coeffs = [(int(c) * inv_lead) % p for c in s.coeffs()]
    s_normalised = _nmod_poly(s_coeffs, p)
    return s_normalised % modulus


def _compute_oracle(op: str, fixture: dict[str, Any]):
    p = int(fixture["p"])
    modulus_coeffs = list(fixture["modulus"])
    a_coeffs = list(fixture["a"])
    b_coeffs = list(fixture["b"])
    modulus = _nmod_poly(modulus_coeffs, p)
    a = _nmod_poly(a_coeffs, p) % modulus
    b = _nmod_poly(b_coeffs, p) % modulus
    if op == "add":
        return _reduce(a + b, modulus)
    if op == "mul":
        return _reduce(a * b, modulus)
    if op == "inv":
        return _trim_zeros(list(_inverse(a, modulus).coeffs()))
    if op == "frob":
        return _trim_zeros(list(a.pow_mod(p, modulus).coeffs()))
    raise OracleMismatch(f"gfq_flint.py: unsupported op {op!r}")


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
        rep_op = result["op"]
        lean_value = result["value"]
        if rep_op not in REP_OPS:
            print(
                f"FAIL {lib}/{case_id} ({rep_op}): unsupported op; "
                f"extend gfq_flint.py.",
                file=sys.stderr,
            )
            failures += 1
            continue
        op = REP_OPS[rep_op]
        fixture = cases.get((lib, case_id))
        if fixture is None or fixture.get("kind") != "gfq_bridge":
            print(
                f"FAIL {lib}/{case_id} ({rep_op}): missing or wrong-kind "
                f"fixture record",
                file=sys.stderr,
            )
            failures += 1
            continue
        try:
            oracle_value = _compute_oracle(op, fixture)
            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{rep_op}",
                kind=op,
                input_record=fixture,
                oracle_name="python-flint",
                oracle_version=oracle_version,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({rep_op}): {exc}", file=sys.stderr)
    print(
        f"gfq_flint.py: checked {checked} case(s), {failures} failure(s)",
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
