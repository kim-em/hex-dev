#!/usr/bin/env python3
"""PARI (via cypari2) oracle driver for `hex-primality`.

Reads a JSONL stream produced by `lake exe hexprimality_emit_fixtures`
(or the committed sample at
`conformance-fixtures/HexPrimality/primality.jsonl`) and re-checks each
case: `isprime` verdicts against PARI's `isprime` (with python-flint's
`is_prime` as a second opinion on every verdict), `nextprime` values against
PARI's `nextprime`, `segment` listings against PARI's `primes` over the
interval, and `certcheck` verdicts against an independent Python
reimplementation of
the certificate checker, whose small-table leaf uses the table's proven
semantics (prime and below `10^5`) with PARI supplying the primality.
Route selection, multiplicative-order laws, search accounting, bounded
failure state, sieve representation, and elaborator behavior are deliberately
not emitted: PARI cannot independently establish those implementation-level
properties, so `HexPrimality.Conformance` checks them directly instead.
On mismatch, writes a JSON failure record under `conformance-failures/`
and exits non-zero so CI fails the job.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexprimality_emit_fixtures | python3 scripts/oracle/primality_pari.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/primality_pari.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/primality_pari.py path/to/file.jsonl
"""
from __future__ import annotations

import argparse
import math
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexPrimality" / "primality.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

# Allow `import scripts.oracle.common` even when invoked as a script.
sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)

# Mirrors `Hex.Nat.primeTableBound`.
PRIME_TABLE_BOUND = 100000


def _pari_version(pari) -> str:
    try:
        return str(pari("Str(version())"))
    except Exception:  # pragma: no cover - version formatting only
        return "unknown"


def _is_prime(pari, n: int) -> bool:
    verdict = bool(int(pari.isprime(n)))
    import flint  # type: ignore[import-not-found]

    try:
        second = bool(flint.fmpz(n).is_prime())
    except AttributeError as exc:
        raise OracleMismatch(
            "python-flint does not provide the required fmpz.is_prime API"
        ) from exc
    if second != verdict:
        raise OracleMismatch(
            f"cypari2 and python-flint disagree on isprime({n}): "
            f"{verdict} vs {second}"
        )
    return verdict


def _segment(pari, lo: int, hi: int) -> list[int]:
    vec = pari.primes([lo, hi - 1])
    return [int(p) for p in vec]


def _check_witness(n: int, q: int, a: int) -> bool:
    if q == 0:
        return False
    return (
        pow(a, n - 1, n) == 1 % n
        and math.gcd((pow(a, (n - 1) // q, n) + n - 1) % n, n) == 1
    )


def _check_cert(pari, cert: dict[str, Any]) -> bool:
    """Independent replay of `Hex.Nat.checkPrime` on the serialized form.

    The `small` leaf uses the committed table's proven semantics — prime
    and below the bound — with PARI supplying primality.
    """
    t = cert["t"]
    n = int(cert["n"])
    if t == "small":
        return n < PRIME_TABLE_BOUND and _is_prime(pari, n)
    factors = [(int(a), int(e), ch) for a, e, ch in cert["f"]]
    if not all(_check_cert(pari, ch) for _, _, ch in factors):
        return False
    subjects = [int(ch["n"]) for _, _, ch in factors]
    if any(s < 2 for s in subjects):
        return False
    if any(a >= b for a, b in zip(subjects, subjects[1:])):
        return False
    if n < 2 or n % 2 == 0:
        return False
    # Match `Hex.Nat.certProduct`'s verdict: accumulate one multiplication at
    # a time and reject when the total first exceeds `n - 1`. The Lean checker
    # authorizes each multiplication before constructing it.
    F = 1
    for (_, e, ch) in factors:
        q = int(ch["n"])
        for _ in range(e + 1):
            F *= q
            if F > n - 1:
                return False
    if F == 0 or (n - 1) % F != 0:
        return False
    if not all(_check_witness(n, int(ch["n"]), a) for a, _, ch in factors):
        return False
    if t == "pock":
        return n < F * F
    if t != "pock3":
        raise OracleMismatch(f"unknown certificate node {t!r}")
    r, s, w = int(cert["r"]), int(cert["s"]), int(cert["w"])
    big_r = (n - 1) // F
    if F % 2 != 0 or big_r % 2 != 1:
        return False
    if big_r != 2 * F * s + r or not (1 <= r < 2 * F):
        return False
    if n >= (F + 1) * (2 * F * F + (r - 1) * F + 1):
        return False
    d = r * r - 8 * s
    return s == 0 or r * r < 8 * s or (w * w < d < (w + 1) * (w + 1))


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
            fixture = cases[(lib, case_id)]
            if op == "isprime":
                if fixture["kind"] != "isprime":
                    raise OracleMismatch(
                        f"{lib}/{case_id}: expected isprime fixture, got "
                        f"{fixture['kind']!r}"
                    )
                n = int(fixture["n"])
                oracle_value = _is_prime(pari, n)
                input_record: dict[str, Any] = {"n": n}
            elif op == "nextprime":
                if fixture["kind"] != "nextprime":
                    raise OracleMismatch(
                        f"{lib}/{case_id}: expected nextprime fixture, got "
                        f"{fixture['kind']!r}"
                    )
                n = int(fixture["n"])
                oracle_value = int(pari.nextprime(n + 1))
                if not _is_prime(pari, oracle_value):
                    raise OracleMismatch(
                        f"{lib}/{case_id}: PARI nextprime returned nonprime "
                        f"{oracle_value}"
                    )
                input_record = {"n": n}
            elif op == "segment":
                if fixture["kind"] != "segment":
                    raise OracleMismatch(
                        f"{lib}/{case_id}: expected segment fixture, got "
                        f"{fixture['kind']!r}"
                    )
                lo, hi = int(fixture["lo"]), int(fixture["hi"])
                oracle_value = _segment(pari, lo, hi)
                input_record = {"lo": lo, "hi": hi}
            elif op == "certcheck":
                if fixture["kind"] != "certcheck":
                    raise OracleMismatch(
                        f"{lib}/{case_id}: expected certcheck fixture, got "
                        f"{fixture['kind']!r}"
                    )
                cert = fixture["cert"]
                oracle_value = _check_cert(pari, cert)
                if oracle_value and int(cert["n"]) >= 2:
                    # An accepted certificate's subject must be prime;
                    # anything else is a checker soundness bug.
                    if not _is_prime(pari, int(cert["n"])):
                        raise OracleMismatch(
                            f"{lib}/{case_id}: certificate accepted for "
                            f"composite subject {cert['n']}"
                        )
                input_record = {"n": int(fixture["n"]), "cert": cert}
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r} in "
                    f"primality_pari.py; extend the driver."
                )
            assert_equal(
                lean_value,
                oracle_value,
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
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"primality_pari.py: checked {checked} case(s), {failures} failure(s)",
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
    parser.add_argument(
        "--require-oracles",
        action="store_true",
        help="fail instead of skipping when cypari2 or python-flint is missing",
    )
    args = parser.parse_args(argv)

    if args.check:
        source: str | None = str(DEFAULT_FIXTURE)
    else:
        source = args.input  # may be None → stdin

    require_oracles = (
        args.require_oracles or os.environ.get("HEX_REQUIRE_ORACLES") == "1"
    )
    try:
        import cypari2  # noqa: F401
        import flint  # noqa: F401
    except ImportError as exc:
        if require_oracles:
            print(
                "FAIL: required oracles cypari2 and python-flint are not installed "
                f"({exc.name})",
                file=sys.stderr,
            )
            return 1
        print(
            "SKIP: cypari2 and python-flint are not both installed "
            f"({exc.name})",
            file=sys.stderr,
        )
        return 0

    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
