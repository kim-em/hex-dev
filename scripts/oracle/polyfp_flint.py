#!/usr/bin/env python3
"""python-flint oracle driver for `hex-poly-fp`.

Reads a JSONL stream produced by `lake exe hexpolyfp_emit_fixtures`
(or the committed sample at
`conformance-fixtures/HexPolyFp/poly.jsonl`) and re-runs each `mul`,
`gcd`, `divrem`, `frobenius`, and `squarefree` operation through
python-flint's `nmod_poly`.  Mismatches are written to
`conformance-failures/` and the script exits non-zero.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexpolyfp_emit_fixtures | python3 scripts/oracle/polyfp_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/polyfp_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/polyfp_flint.py path/to/file.jsonl

`--check` is equivalent to passing
``conformance-fixtures/HexPolyFp/poly.jsonl`` and is the form CI uses
for the regression sentinel: if Lean's emission ever drifts from the
committed sample, the next agent regenerating the file should note the
diff in their progress entry.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexPolyFp" / "poly.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _modulus(record: dict[str, Any]) -> int:
    if record["kind"] != "poly":
        raise ValueError(f"expected poly record, got {record['kind']}")
    p = record.get("modulus")
    if not isinstance(p, int):
        raise ValueError(
            f"poly_fp record missing integer modulus: {record!r}"
        )
    return p


def _coeffs(record: dict[str, Any]) -> list[int]:
    if record["kind"] != "poly":
        raise ValueError(f"expected poly record, got {record['kind']}")
    return list(record["coeffs"])


def _nmod_poly(coeffs: list[int], p: int):
    from flint import nmod_poly  # type: ignore[import-not-found]
    return nmod_poly(coeffs, p)


def _trim_zeros(coeffs) -> list[int]:
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _coeff_list(poly) -> list[int]:
    """Lean-compatible coefficient list: low-to-high, trimmed."""
    return _trim_zeros(list(poly.coeffs()))


def _normalize_squarefree(coeff: int, raw_factors, p: int) -> tuple[int, list]:
    """Match the Lean canonicalisation: hoist constant factors and
    leading coefficients into the unit, then sort by (factor coeffs,
    multiplicity).  python-flint already returns monic factors so the
    extra hoisting only ever fires for the leading-coeff case where
    nothing changes; we still apply it defensively."""
    unit = coeff % p
    factors: list[tuple[list[int], int]] = []
    for factor, exp in raw_factors:
        coeffs = list(factor.coeffs())
        if len(coeffs) <= 1:
            # Constant factor: absorb into unit.
            c = coeffs[0] if coeffs else 0
            unit = (unit * pow(int(c), int(exp), p)) % p
            continue
        lead = int(coeffs[-1])
        if lead != 1:
            inv_lead = pow(lead, -1, p)
            coeffs = [(int(c) * inv_lead) % p for c in coeffs]
            unit = (unit * pow(lead, int(exp), p)) % p
        else:
            coeffs = [int(c) for c in coeffs]
        factors.append((coeffs, int(exp)))
    factors.sort(key=lambda f: (f[0], f[1]))
    return unit, [[coeffs, mult] for coeffs, mult in factors]


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
                p = _modulus(left)
                if _modulus(right) != p:
                    raise OracleMismatch(
                        f"{lib}/{case_id}: inconsistent moduli on mul inputs"
                    )
                poly = _nmod_poly(_coeffs(left), p) * _nmod_poly(_coeffs(right), p)
                oracle_value = _coeff_list(poly)
                input_record = {"left": left, "right": right}
            elif op == "gcd":
                left = cases[(lib, f"{case_id}/left")]
                right = cases[(lib, f"{case_id}/right")]
                p = _modulus(left)
                if _modulus(right) != p:
                    raise OracleMismatch(
                        f"{lib}/{case_id}: inconsistent moduli on gcd inputs"
                    )
                # python-flint's nmod_poly gcd is monic by construction.
                poly = _nmod_poly(_coeffs(left), p).gcd(_nmod_poly(_coeffs(right), p))
                oracle_value = _coeff_list(poly)
                input_record = {"left": left, "right": right}
            elif op == "divrem":
                dividend = cases[(lib, f"{case_id}/dividend")]
                divisor = cases[(lib, f"{case_id}/divisor")]
                p = _modulus(dividend)
                if _modulus(divisor) != p:
                    raise OracleMismatch(
                        f"{lib}/{case_id}: inconsistent moduli on divrem inputs"
                    )
                a = _nmod_poly(_coeffs(dividend), p)
                b = _nmod_poly(_coeffs(divisor), p)
                quot, rem = divmod(a, b)
                oracle_value = [_coeff_list(quot), _coeff_list(rem)]
                input_record = {"dividend": dividend, "divisor": divisor}
            elif op == "frobenius":
                base = cases[(lib, f"{case_id}/base")]
                modulus = cases[(lib, f"{case_id}/mod")]
                p = _modulus(base)
                if _modulus(modulus) != p:
                    raise OracleMismatch(
                        f"{lib}/{case_id}: inconsistent moduli on frobenius inputs"
                    )
                base_poly = _nmod_poly(_coeffs(base), p)
                mod_poly = _nmod_poly(_coeffs(modulus), p)
                # Power-mod reduces base mod mod_poly internally, matching
                # `Hex.FpPoly.powModMonic`'s behaviour.
                oracle_value = _coeff_list(base_poly.pow_mod(p, mod_poly))
                input_record = {"base": base, "mod": modulus}
            elif op == "squarefree":
                poly_record = cases[(lib, f"{case_id}/poly")]
                p = _modulus(poly_record)
                f = _nmod_poly(_coeffs(poly_record), p)
                coeff, raw_factors = f.factor_squarefree()
                unit, factors = _normalize_squarefree(int(coeff), raw_factors, p)
                oracle_value = [unit, factors]
                input_record = {"poly": poly_record}
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} in polyfp_flint.py"
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
        f"polyfp_flint.py: checked {checked} case(s), {failures} failure(s)",
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
