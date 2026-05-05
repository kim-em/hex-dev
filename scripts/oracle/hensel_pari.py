#!/usr/bin/env python3
"""PARI (via cypari2) oracle driver for `hex-hensel`.

Reads a JSONL stream produced by `lake exe hexhensel_emit_fixtures`
(or the committed sample at
`conformance-fixtures/HexHensel/hensel.jsonl`) and re-runs each
multifactor Hensel-lift case through PARI's `factorpadic`.  On
mismatch, writes a JSON failure record under `conformance-failures/`
and exits non-zero so CI fails the job.

`python-flint` does not expose mod-`p^k` polynomial factorisation, so
the canonical exact oracle for the multifactor Hensel lift is PARI
(via cypari2).

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexhensel_emit_fixtures | python3 scripts/oracle/hensel_pari.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/hensel_pari.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/hensel_pari.py path/to/file.jsonl

The oracle compares the **multiset** of factor coefficient lists, not
the ordered list, because `factorpadic` and Lean's
`multifactorLiftQuadratic` may emit factors in different orders.  Both
sides are reduced to canonical integer representatives in
``[0, p^k)``.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexHensel" / "hensel.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

# Allow `import scripts.oracle.common` even when invoked as a script.
sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _trim_zeros(coeffs) -> list[int]:
    out = [int(c) for c in coeffs]
    while out and out[-1] == 0:
        out.pop()
    return out


def _coeffs(record: dict[str, Any]) -> list[int]:
    if record["kind"] != "poly":
        raise ValueError(f"expected poly record, got {record['kind']}")
    return list(record["coeffs"])


def _pari_poly(pari, coeffs: list[int]):
    """Build a PARI ``t_POL`` in `x` from a coefficient list ascending."""
    # `Polrev` interprets the vector as constant-first, matching our schema.
    return pari.Polrev(list(coeffs))


def _factor_to_coeffs(pari, factor, p: int, k: int) -> list[int]:
    """Lift a `factorpadic` factor to integer coefficients in ``[0, p^k)``.

    `factor` is a PARI ``t_POL`` whose coefficients are ``t_PADIC``
    elements at precision ``p^k``.  ``lift`` collapses the padic layer
    to native integers; ``Vecrev`` returns the coefficients
    constant-first; we then normalise into ``[0, p^k)`` and drop
    trailing zeros to match Lean's canonical form.
    """
    modulus = p ** k
    lifted = pari.lift(factor)
    raw = [int(c) for c in pari.Vecrev(lifted)]
    return _trim_zeros([c % modulus for c in raw])


def _pari_version(pari) -> str:
    try:
        v = pari("Str(version())")
        return str(v)
    except Exception:
        return "unknown"


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    import cypari2  # type: ignore[import-not-found]
    pari = cypari2.Pari()
    cases, results = split_fixtures_results(read_fixtures(source))
    oracle_version = _pari_version(pari)
    failures = 0
    checked = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        lean_value = result["value"]
        try:
            if op == "multifactor_lift":
                pk = cases[(lib, f"{case_id}/pk")]
                if pk["kind"] != "prime":
                    raise OracleMismatch(
                        f"{lib}/{case_id}: expected prime fixture for /pk, "
                        f"got kind {pk['kind']!r}"
                    )
                p = int(pk["p"])
                k = int(pk["n"])
                target = cases[(lib, f"{case_id}/f")]
                target_coeffs = _coeffs(target)
                # Collect input factors (kept for failure-record context;
                # the oracle re-derives factors from `target` alone).
                input_factors: list[list[int]] = []
                idx = 0
                while True:
                    key = (lib, f"{case_id}/factor/{idx}")
                    if key not in cases:
                        break
                    input_factors.append(_coeffs(cases[key]))
                    idx += 1
                target_pari = _pari_poly(pari, target_coeffs)
                fac = pari.factorpadic(target_pari, p, k)
                nrows = int(pari.matsize(fac)[0])
                oracle_factors: list[list[int]] = []
                for i in range(nrows):
                    g = fac[i, 0]
                    exponent = int(fac[i, 1])
                    coeffs = _factor_to_coeffs(pari, g, p, k)
                    for _ in range(exponent):
                        oracle_factors.append(coeffs)
                # Compare as multisets — split-tree order on the Lean
                # side need not match PARI's internal ordering.
                lean_sorted = sorted([list(fc) for fc in lean_value])
                oracle_sorted = sorted(oracle_factors)
                input_record = {
                    "p": p,
                    "k": k,
                    "target": target_coeffs,
                    "factors": input_factors,
                }
                assert_equal(
                    lean_sorted,
                    oracle_sorted,
                    library=lib,
                    case_id=f"{case_id}:{op}",
                    kind=op,
                    input_record=input_record,
                    oracle_name="cypari2/PARI",
                    oracle_version=oracle_version,
                    failure_dir=failure_dir,
                    profile=profile,
                    seed=seed,
                )
                checked += 1
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} "
                    f"in hensel_pari.py; extend the driver."
                )
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"hensel_pari.py: checked {checked} case(s), {failures} failure(s)",
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
        import cypari2  # noqa: F401
    except ImportError:
        # Mirror the SPEC's `if_available` mode: a missing oracle is a
        # skip, not a failure.  CI installs cypari2 (which itself needs
        # `libpari-dev`) before this script runs; a failure here in CI
        # means install failed.
        print("SKIP: cypari2 not installed", file=sys.stderr)
        return 0

    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
