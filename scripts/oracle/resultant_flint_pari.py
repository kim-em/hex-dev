#!/usr/bin/env python3
"""Independent FLINT/PARI oracle for ``HexResultant``.

Reads the JSONL stream from ``lake exe hexresultant_emit_fixtures`` and
recomputes every ``resultant`` and ``disc_left`` value from the original
coefficient lists. python-flint is primary and cypari2/PARI is secondary; when
both are installed, both must agree with Lean and therefore with each other.
The library's special zero/constant formal-degree conventions are covered by
Lean-only core checks and are deliberately absent from this external profile,
whose inputs all have exact degree ten.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT
    / "conformance-fixtures"
    / "HexResultant"
    / "resultant.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _coeffs(record: dict[str, Any]) -> list[int]:
    if record["kind"] != "poly":
        raise OracleMismatch(f"expected poly record, got {record['kind']!r}")
    return [int(c) for c in record["coeffs"]]


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except ImportError:
        return "unavailable"


def _pari_version(pari) -> str:
    try:
        return str(pari("Str(version())"))
    except Exception:
        return "unknown"


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    try:
        from flint import fmpz_poly  # type: ignore[import-not-found]
    except ImportError:
        fmpz_poly = None
    try:
        import cypari2  # type: ignore[import-not-found]
        pari = cypari2.Pari()
    except ImportError:
        pari = None

    if fmpz_poly is None and pari is None:
        print("SKIP: neither python-flint nor cypari2 is installed", file=sys.stderr)
        return 0

    versions: list[str] = []
    if fmpz_poly is not None:
        versions.append(f"python-flint/{_flint_version()}")
    if pari is not None:
        versions.append(f"PARI/{_pari_version(pari)}")
    oracle_name = "+".join(versions)

    cases, results = split_fixtures_results(read_fixtures(source))
    failures = 0
    checked = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        lean_value = int(result["value"])
        left_record = cases[(lib, f"{case_id}/left")]
        right_record = cases[(lib, f"{case_id}/right")]
        left_coeffs = _coeffs(left_record)
        right_coeffs = _coeffs(right_record)
        input_record = {"left": left_record, "right": right_record}
        oracle_values: list[tuple[str, int]] = []
        if fmpz_poly is not None:
            left = fmpz_poly(left_coeffs)
            right = fmpz_poly(right_coeffs)
            if op == "resultant":
                oracle_values.append(("python-flint", int(left.resultant(right))))
            elif op == "disc_left":
                oracle_values.append(("python-flint", int(left.discriminant())))
            else:
                raise OracleMismatch(f"unsupported operation {op!r}")
        if pari is not None:
            left = pari.Polrev(left_coeffs, "x")
            right = pari.Polrev(right_coeffs, "x")
            if op == "resultant":
                oracle_values.append(("cypari2/PARI", int(pari.polresultant(left, right))))
            elif op == "disc_left":
                oracle_values.append(("cypari2/PARI", int(pari.poldisc(left))))
            else:
                raise OracleMismatch(f"unsupported operation {op!r}")
        case_failed = False
        for implementation, oracle_value in oracle_values:
            try:
                assert_equal(
                    lean_value,
                    oracle_value,
                    library=lib,
                    case_id=f"{case_id}:{op}:{implementation}",
                    kind=op,
                    input_record=input_record,
                    oracle_name=implementation,
                    oracle_version=oracle_name,
                    failure_dir=failure_dir,
                    profile=profile,
                    seed=seed,
                )
            except OracleMismatch as exc:
                case_failed = True
                print(
                    f"FAIL {lib}/{case_id} ({op}, {implementation}): {exc}",
                    file=sys.stderr,
                )
        checked += 1
        if case_failed:
            failures += 1
    print(
        f"resultant_flint_pari.py: checked {checked} result(s), "
        f"{failures} failure(s) with {oracle_name}",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("input", nargs="?", help="JSONL fixture path (default: stdin)")
    source.add_argument(
        "--check",
        action="store_true",
        help=f"read {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0xC0FFEE)
    args = parser.parse_args(argv)
    input_path: str | None = str(DEFAULT_FIXTURE) if args.check else args.input
    return check(
        input_path,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
