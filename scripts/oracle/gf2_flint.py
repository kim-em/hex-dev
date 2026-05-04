#!/usr/bin/env python3
"""python-flint oracle driver for `hex-gf2`.

Reads a JSONL stream produced by `lake exe hexgf2_emit_fixtures` (or
the committed sample at `conformance-fixtures/HexGF2/gf2.jsonl`) and
re-runs each operation through python-flint.  On mismatch, writes a
JSON failure record under `conformance-failures/` and exits non-zero
so CI fails the job.

Operations cross-checked
------------------------

`F_2[x]` arithmetic (one fixture pair `<case>/a`, `<case>/b` plus
three result records per case):

* ``mul``    — Lean ``GF2Poly.mul`` (clmul + XOR shift-add).
  python-flint replays via ``nmod_poly(a, 2) * nmod_poly(b, 2)``.
* ``gcd``    — Lean ``GF2Poly.gcd`` (binary Euclidean over `F_2`).
  python-flint replays via ``nmod_poly.gcd``.  Both sides return
  monic over the prime field `F_2`, so the comparison is direct.
* ``divmod`` — Lean ``GF2Poly.divMod``.  python-flint replays via
  ``nmod_poly.divmod`` and compares ``[quot, rem]`` coefficient pairs.

`GF(2^n)` field arithmetic (one fixture triple `<case>/modulus`,
`<case>/a`, `<case>/b` plus three result records per case):

* ``gf_mul``       — ``(a_poly * b_poly) % modulus`` over `F_2[x]`.
* ``gf_inverse``   — extended-GCD inverse modulo the irreducible.
* ``gf_frobenius`` — characteristic-2 Frobenius `a → a^2`, computed
  as ``(a_poly * a_poly) % modulus``.

The oracle reconstructs the field directly from the emitted modulus
polynomial; constructing a ``fq_default_ctx`` would also validate
irreducibility but is not necessary for the cross-check itself, since
the inverse / mul / square operations modulo any polynomial agree
with the field operations whenever the modulus is irreducible (which
the Lean side asserts via its `Irreducible` typeclass argument).

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexgf2_emit_fixtures | python3 scripts/oracle/gf2_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/gf2_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/gf2_flint.py path/to/file.jsonl

`--check` is exactly equivalent to passing
``conformance-fixtures/HexGF2/gf2.jsonl``.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexGF2" / "gf2.jsonl"
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
    cast `nmod`-like coefficients down to native Python `int`."""
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _coeffs(record: dict[str, Any]) -> list[int]:
    if record["kind"] != "poly":
        raise ValueError(f"expected poly record, got {record['kind']}")
    if record.get("modulus") != 2:
        raise ValueError(
            f"gf2_flint.py: F_2 fixture required (case "
            f"{record['lib']}/{record['case']}); got modulus={record.get('modulus')!r}"
        )
    return list(record["coeffs"])


def _nmod_poly(coeffs: list[int]):
    from flint import nmod_poly  # type: ignore[import-not-found]
    return nmod_poly([int(c) for c in coeffs], 2)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _modular_inverse(a, modulus):
    """Return ``a^{-1} mod modulus`` as an ``nmod_poly``.

    Lean's ``GF2n.inv`` returns the canonical zero residue when the
    input residue is zero, mirroring the convention ``0⁻¹ = 0``.  We
    match that here so a deliberate corruption of the inverse value
    surfaces as a normal coefficient diff rather than an exception.
    """
    if a == 0:
        return _nmod_poly([])
    g, s, _t = a.xgcd(modulus)
    if g != 1:
        raise OracleMismatch(
            f"non-trivial gcd({a}, modulus) = {g}; modulus is not irreducible "
            f"or input is not coprime to modulus"
        )
    return s % modulus


def _check_f2x_mul(*, lib, case_id, cases, lean_value, **kw):
    a_record = cases[(lib, f"{case_id}/a")]
    b_record = cases[(lib, f"{case_id}/b")]
    a = _nmod_poly(_coeffs(a_record))
    b = _nmod_poly(_coeffs(b_record))
    oracle_value = _trim_zeros(list((a * b).coeffs()))
    assert_equal(
        lean_value, oracle_value,
        library=lib, case_id=f"{case_id}:mul", kind="mul",
        input_record={"a": a_record, "b": b_record}, **kw,
    )


def _check_f2x_gcd(*, lib, case_id, cases, lean_value, **kw):
    a_record = cases[(lib, f"{case_id}/a")]
    b_record = cases[(lib, f"{case_id}/b")]
    a = _nmod_poly(_coeffs(a_record))
    b = _nmod_poly(_coeffs(b_record))
    oracle_value = _trim_zeros(list(a.gcd(b).coeffs()))
    assert_equal(
        lean_value, oracle_value,
        library=lib, case_id=f"{case_id}:gcd", kind="gcd",
        input_record={"a": a_record, "b": b_record}, **kw,
    )


def _check_f2x_divmod(*, lib, case_id, cases, lean_value, **kw):
    a_record = cases[(lib, f"{case_id}/a")]
    b_record = cases[(lib, f"{case_id}/b")]
    a = _nmod_poly(_coeffs(a_record))
    b = _nmod_poly(_coeffs(b_record))
    quot, rem = divmod(a, b)
    oracle_value = [
        _trim_zeros(list(quot.coeffs())),
        _trim_zeros(list(rem.coeffs())),
    ]
    assert_equal(
        lean_value, oracle_value,
        library=lib, case_id=f"{case_id}:divmod", kind="divmod",
        input_record={"a": a_record, "b": b_record}, **kw,
    )


def _check_gf_mul(*, lib, case_id, cases, lean_value, **kw):
    mod_record = cases[(lib, f"{case_id}/modulus")]
    a_record = cases[(lib, f"{case_id}/a")]
    b_record = cases[(lib, f"{case_id}/b")]
    modulus = _nmod_poly(_coeffs(mod_record))
    a = _nmod_poly(_coeffs(a_record))
    b = _nmod_poly(_coeffs(b_record))
    oracle_value = _trim_zeros(list(((a * b) % modulus).coeffs()))
    assert_equal(
        lean_value, oracle_value,
        library=lib, case_id=f"{case_id}:gf_mul", kind="gf_mul",
        input_record={"modulus": mod_record, "a": a_record, "b": b_record},
        **kw,
    )


def _check_gf_inverse(*, lib, case_id, cases, lean_value, **kw):
    mod_record = cases[(lib, f"{case_id}/modulus")]
    a_record = cases[(lib, f"{case_id}/a")]
    modulus = _nmod_poly(_coeffs(mod_record))
    a = _nmod_poly(_coeffs(a_record))
    oracle_value = _trim_zeros(list(_modular_inverse(a, modulus).coeffs()))
    assert_equal(
        lean_value, oracle_value,
        library=lib, case_id=f"{case_id}:gf_inverse", kind="gf_inverse",
        input_record={"modulus": mod_record, "a": a_record},
        **kw,
    )


def _check_gf_frobenius(*, lib, case_id, cases, lean_value, **kw):
    mod_record = cases[(lib, f"{case_id}/modulus")]
    a_record = cases[(lib, f"{case_id}/a")]
    modulus = _nmod_poly(_coeffs(mod_record))
    a = _nmod_poly(_coeffs(a_record))
    oracle_value = _trim_zeros(list(((a * a) % modulus).coeffs()))
    assert_equal(
        lean_value, oracle_value,
        library=lib, case_id=f"{case_id}:gf_frobenius", kind="gf_frobenius",
        input_record={"modulus": mod_record, "a": a_record},
        **kw,
    )


HANDLERS = {
    "mul":           _check_f2x_mul,
    "gcd":           _check_f2x_gcd,
    "divmod":        _check_f2x_divmod,
    "gf_mul":        _check_gf_mul,
    "gf_inverse":    _check_gf_inverse,
    "gf_frobenius":  _check_gf_frobenius,
}


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
        handler = HANDLERS.get(op)
        if handler is None:
            raise OracleMismatch(
                f"{lib}/{case_id}: unsupported op {op!r} "
                f"in gf2_flint.py; extend the driver."
            )
        try:
            handler(
                lib=lib, case_id=case_id, cases=cases, lean_value=lean_value,
                oracle_name="python-flint",
                oracle_version=oracle_version,
                failure_dir=failure_dir, profile=profile, seed=seed,
            )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"gf2_flint.py: checked {checked} case(s), {failures} failure(s)",
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
