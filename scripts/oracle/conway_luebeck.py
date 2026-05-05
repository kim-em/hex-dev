#!/usr/bin/env python3
"""Lübeck-cache oracle driver for `hex-conway`.

Reads JSONL produced by `lake exe hexconway_emit_fixtures` and compares
Lean's committed Conway coefficients against:

* `scripts/oracle/luebeck_conway_cache.json` (always);
* the optional `conway-polynomials` package table adapter when requested.

The optional package leg is a table-source check, not an independent
Conway recomputation.  Use `--require-conway-polynomials` in CI jobs
that install the package; if the dependency is unavailable in that mode,
this script fails with an actionable error.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexConway" / "conway.jsonl"
DEFAULT_CACHE = REPO_ROOT / "scripts" / "oracle" / "luebeck_conway_cache.json"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)
from scripts.oracle.conway_polynomials_table import (  # noqa: E402
    ConwayTableError,
    lookup as package_lookup,
)


def _load_cache(path: Path) -> dict[tuple[int, int], list[int]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("coefficient_order") != "ascending":
        raise ValueError(f"{path}: expected ascending coefficient_order")
    out: dict[tuple[int, int], list[int]] = {}
    for entry in payload.get("entries", []):
        p = int(entry["p"])
        n = int(entry["n"])
        coeffs = list(entry["coeffs"])
        if not all(isinstance(c, int) for c in coeffs):
            raise ValueError(f"{path}: non-integer coeff in {(p, n)}")
        out[(p, n)] = coeffs
    return out


def _fixture_key(fixture: dict[str, Any]) -> tuple[int, int]:
    if fixture["kind"] != "conway":
        raise ValueError(f"expected conway fixture, got {fixture['kind']!r}")
    return int(fixture["p"]), int(fixture["n"])


def _compare_one(
    *,
    fixture: dict[str, Any],
    lean_value: list[int],
    expected: list[int],
    oracle_name: str,
    oracle_version: str,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> None:
    assert_equal(
        lean_value,
        expected,
        library=fixture["lib"],
        case_id=f"{fixture['case']}:{oracle_name}",
        kind="coeffs",
        input_record=fixture,
        oracle_name=oracle_name,
        oracle_version=oracle_version,
        failure_dir=failure_dir,
        profile=profile,
        seed=seed,
    )


def check(
    source: str | Path | None,
    *,
    cache_path: Path,
    check_package: bool,
    require_package: bool,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    cache = _load_cache(cache_path)
    cases, results = split_fixtures_results(read_fixtures(source))
    failures = 0
    checked = 0
    if check_package:
        try:
            package_lookup(2, 1)
        except ConwayTableError as exc:
            if require_package:
                print(f"FAIL conway-polynomials: {exc}", file=sys.stderr)
                return 1
            print("SKIP: conway-polynomials not installed", file=sys.stderr)
            check_package = False

    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        if op != "coeffs":
            print(f"FAIL {lib}/{case_id}: unsupported op {op!r}", file=sys.stderr)
            failures += 1
            continue
        fixture = cases.get((lib, case_id))
        if fixture is None:
            print(f"FAIL {lib}/{case_id}: missing conway fixture", file=sys.stderr)
            failures += 1
            continue
        try:
            key = _fixture_key(fixture)
            expected = cache[key]
        except (KeyError, ValueError) as exc:
            print(f"FAIL {lib}/{case_id}: {exc}", file=sys.stderr)
            failures += 1
            continue

        lean_value = list(result["value"])
        try:
            _compare_one(
                fixture=fixture,
                lean_value=lean_value,
                expected=expected,
                oracle_name="luebeck-cache",
                oracle_version=cache_path.name,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except OracleMismatch as exc:
            print(f"FAIL {lib}/{case_id} (luebeck-cache): {exc}", file=sys.stderr)
            failures += 1

        if check_package:
            try:
                package_expected = package_lookup(*key)
            except ConwayTableError as exc:
                if require_package:
                    print(f"FAIL {lib}/{case_id} (conway-polynomials): {exc}", file=sys.stderr)
                    failures += 1
                continue
            try:
                _compare_one(
                    fixture=fixture,
                    lean_value=lean_value,
                    expected=package_expected,
                    oracle_name="conway-polynomials",
                    oracle_version="runtime-package",
                    failure_dir=failure_dir,
                    profile=profile,
                    seed=seed,
                )
                checked += 1
            except OracleMismatch as exc:
                print(f"FAIL {lib}/{case_id} (conway-polynomials): {exc}", file=sys.stderr)
                failures += 1

    print(
        f"conway_luebeck.py: checked {checked} comparison(s), "
        f"{failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group()
    src.add_argument("input", nargs="?", help="JSONL fixture path (default: stdin)")
    src.add_argument(
        "--check",
        action="store_true",
        help=f"read the committed sample at {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    parser.add_argument("--cache", type=Path, default=DEFAULT_CACHE)
    parser.add_argument(
        "--check-conway-polynomials",
        action="store_true",
        help="also compare against the optional conway-polynomials package",
    )
    parser.add_argument(
        "--require-conway-polynomials",
        action="store_true",
        help="enable the optional package leg and fail if its dependency is missing",
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
        help="directory for JSON failure records",
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)

    source = str(DEFAULT_FIXTURE) if args.check else args.input
    check_package = args.check_conway_polynomials or args.require_conway_polynomials
    return check(
        source,
        cache_path=args.cache,
        check_package=check_package,
        require_package=args.require_conway_polynomials,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
