#!/usr/bin/env python3
"""PARI/python-flint oracle for ``hex-int-factor`` JSONL fixtures."""
from __future__ import annotations

import argparse
import math
import os
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures/HexIntFactor/intfactor.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"
sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _version(pari) -> str:
    return str(pari("Str(version())"))


def _factors(pari, n: int) -> list[list[int]] | str:
    if n == 0:
        return "refused"
    if n == 1:
        return []
    factorization = pari.factor(n)
    rows = int(pari.matsize(factorization)[0])
    answer = sorted(
        [
            [int(factorization[i, 0]), int(factorization[i, 1])]
            for i in range(rows)
        ]
    )
    try:
        import flint  # type: ignore[import-not-found]

        second = sorted(
            [[int(p), int(e)] for p, e in flint.fmpz(n).factor()]
        )
        if second != answer:
            raise OracleMismatch(
                f"PARI and python-flint disagree on factor({n}): "
                f"{answer!r} vs {second!r}"
            )
    except (ImportError, AttributeError):
        pass
    return answer


def _divisor_functions(pari, n: int) -> dict[str, int]:
    factors = _factors(pari, n)
    assert isinstance(factors, list)
    radical = math.prod(p for p, _ in factors)
    sqfpart = math.prod(p for p, e in factors if e % 2 == 1)
    sqdiv = math.prod(p ** (e // 2) for p, e in factors)
    return {
        "tau": len(pari.divisors(n)),
        "sigma0": int(pari.sigma(n, 0)),
        "sigma1": int(pari.sigma(n)),
        "sigma2": int(pari.sigma(n, 2)),
        "phi": int(pari.eulerphi(n)),
        "rad": radical,
        "sqfpart": sqfpart,
        "sqdiv": sqdiv,
    }


def _indices(n: int, sign: str) -> list[int]:
    if sign == "minus":
        return [d for d in range(1, n + 1) if n % d == 0]
    return [d for d in range(1, 2 * n + 1) if (2 * n) % d == 0 and n % d != 0]


def _cyclotomic(pari, b: int, n: int, sign: str) -> list[list[int]]:
    parts = [
        [d, int(pari(f"subst(polcyclo({d}),x,{b})"))]
        for d in _indices(n, sign)
    ]
    target = b**n - 1 if sign == "minus" else b**n + 1
    if math.prod(value for _, value in parts) != target:
        raise OracleMismatch(f"PARI cyclotomic product does not equal {target}")
    # Independently force PARI's integer factorization on the original input.
    _factors(pari, target)
    return parts


def check(source: str | Path | None, *, failure_dir: Path, profile: str, seed: int) -> int:
    import cypari2  # type: ignore[import-not-found]

    pari = cypari2.Pari()
    cases, results = split_fixtures_results(read_fixtures(source))
    failures = 0
    checked = 0
    for result in results:
        lib, case_id, op = result["lib"], result["case"], result["op"]
        lean_value = result["value"]
        try:
            fixture = cases[(lib, case_id)]
            if fixture["kind"] != op:
                raise OracleMismatch(
                    f"{lib}/{case_id}: fixture kind {fixture['kind']!r} != op {op!r}"
                )
            if op == "factor":
                n = int(fixture["n"])
                oracle_value: Any = _factors(pari, n)
                inputs = {"n": n}
            elif op == "divisorfn":
                n = int(fixture["n"])
                oracle_value = _divisor_functions(pari, n)
                inputs = {"n": n}
            elif op == "order":
                a, n = int(fixture["base"]), int(fixture["modulus"])
                oracle_value = int(pari(f"znorder(Mod({a},{n}))"))
                inputs = {"base": a, "modulus": n}
            elif op == "cyclotomic":
                b, n, sign = int(fixture["b"]), int(fixture["n"]), fixture["sign"]
                oracle_value = _cyclotomic(pari, b, n, sign)
                inputs = {"b": b, "n": n, "sign": sign}
            else:
                raise OracleMismatch(f"unsupported operation {op!r}")
            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{op}",
                kind=op,
                input_record=inputs,
                oracle_name="cypari2/PARI+python-flint",
                oracle_version=_version(pari),
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(f"intfactor_pari.py: checked {checked} case(s), {failures} failure(s)", file=sys.stderr)
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("input", nargs="?")
    source.add_argument("--check", action="store_true")
    parser.add_argument("--failure-dir", default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)))
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)
    try:
        import cypari2  # noqa: F401
    except ImportError:
        print("SKIP: cypari2 not installed", file=sys.stderr)
        return 0
    selected = str(DEFAULT_FIXTURE) if args.check else args.input
    return check(selected, failure_dir=Path(args.failure_dir), profile=args.profile, seed=args.seed)


if __name__ == "__main__":
    raise SystemExit(main())
