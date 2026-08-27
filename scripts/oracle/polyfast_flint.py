#!/usr/bin/env python3
"""FLINT/exact-Python oracle for ``hex-poly-fast`` JSONL fixtures.

Integer whole products are recomputed by python-flint. Rational division and
Euclidean results, interpolation, cyclic products, and Padé constraints are
checked independently with exact ``Fraction`` arithmetic. Kernel labels are
treated only as reported metadata: the oracle checks their result, never tells
Hex which kernel to select.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexPolyFast" / "polyfast.jsonl"
)


def _trim(values: list[Any]) -> list[Any]:
    out = list(values)
    while out and out[-1] == 0:
        out.pop()
    return out


def _add(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    n = max(len(a), len(b))
    return _trim([
        (a[i] if i < len(a) else Fraction(0))
        + (b[i] if i < len(b) else Fraction(0))
        for i in range(n)
    ])


def _neg(a: list[Fraction]) -> list[Fraction]:
    return _trim([-x for x in a])


def _sub(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    return _add(a, _neg(b))


def _scale(c: Fraction, a: list[Fraction]) -> list[Fraction]:
    return _trim([c * x for x in a])


def _mul(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    if not a or not b:
        return []
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return _trim(out)


def _divmod(a: list[Fraction], b: list[Fraction]):
    a = _trim(a)
    b = _trim(b)
    if not b:
        return [], a
    q = [Fraction(0)] * max(len(a) - len(b) + 1, 0)
    r = list(a)
    while r and len(r) >= len(b):
        shift = len(r) - len(b)
        c = r[-1] / b[-1]
        q[shift] += c
        for i, value in enumerate(b):
            r[shift + i] -= c * value
        r = _trim(r)
    return _trim(q), r


def _monic(a: list[Fraction]) -> list[Fraction]:
    a = _trim(a)
    return [] if not a else _scale(1 / a[-1], a)


def _gcd(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    while b:
        _, r = _divmod(a, b)
        a, b = b, r
    return _monic(a)


def _decode_rat(value: dict[str, list[int]]) -> list[Fraction]:
    return _trim([
        Fraction(n, d)
        for n, d in zip(value["num"], value["den"], strict=True)
    ])


def _encode_rat(values: list[Fraction]) -> dict[str, list[int]]:
    values = _trim(values)
    return {
        "num": [x.numerator for x in values],
        "den": [x.denominator for x in values],
    }


def _poly(cases: dict[str, dict[str, Any]], case: str) -> list[int]:
    record = cases[case]
    if record["kind"] != "poly":
        raise ValueError(f"{case}: expected poly fixture")
    return list(record["coeffs"])


def _rat_poly(cases: dict[str, dict[str, Any]], case: str) -> list[Fraction]:
    return [Fraction(x) for x in _poly(cases, case)]


def _flint_mul(a: list[int], b: list[int]) -> list[int]:
    try:
        from flint import fmpz_poly  # type: ignore[import-not-found]

        return _trim([int(x) for x in (fmpz_poly(a) * fmpz_poly(b)).coeffs()])
    except ImportError:
        return [int(x) for x in _mul([Fraction(x) for x in a], [Fraction(x) for x in b])]


def _eval(poly: list[Fraction], x: Fraction) -> Fraction:
    out = Fraction(0)
    for coefficient in reversed(poly):
        out = out * x + coefficient
    return out


def _interpolate(points: list[Fraction], values: list[Fraction]):
    if len(points) != len(values) or len(set(points)) != len(points):
        return None
    out: list[Fraction] = []
    for i, point in enumerate(points):
        numerator = [Fraction(1)]
        denominator = Fraction(1)
        for j, other in enumerate(points):
            if i != j:
                numerator = _mul(numerator, [-other, Fraction(1)])
                denominator *= point - other
        out = _add(out, _scale(values[i] / denominator, numerator))
    return out


def _fold_product(
    a: list[Fraction], b: list[Fraction], n: int, *, negacyclic: bool
) -> list[Fraction] | None:
    if n == 0:
        return None
    out = [Fraction(0)] * n
    for degree, value in enumerate(_mul(a, b)):
        quotient, remainder = divmod(degree, n)
        sign = -1 if negacyclic and quotient % 2 else 1
        out[remainder] += sign * value
    return _trim(out)


def _modular_product(a: list[int], b: list[int], modulus: int) -> list[int]:
    return _trim([int(x) % modulus for x in _flint_mul(a, b)])


def _is_power_of_two(n: int) -> bool:
    return n > 0 and n & (n - 1) == 0


def _valid_ntt_plan(p: int, n: int, root: int) -> bool:
    if p <= 1 or not _is_power_of_two(n) or (p - 1) % n != 0:
        return False
    if pow(root, n, p) != 1:
        return False
    return n == 1 or pow(root, n // 2, p) != 1


def _series(cases: dict[str, dict[str, Any]], case: str) -> list[Fraction]:
    return _decode_rat(cases[case]["coeffs"])


def _pade_has_normalized(series: list[Fraction], m: int, n: int) -> bool:
    rows = []
    for k in range(m + 1, m + n + 1):
        row = [
            series[k - j] if 0 <= k - j < len(series) else Fraction(0)
            for j in range(1, n + 1)
        ]
        row.append(-(series[k] if k < len(series) else Fraction(0)))
        rows.append(row)
    if n == 0:
        return True
    pivot_row = 0
    for col in range(n):
        pivot = next(
            (row for row in range(pivot_row, n) if rows[row][col] != 0),
            None,
        )
        if pivot is None:
            continue
        rows[pivot_row], rows[pivot] = rows[pivot], rows[pivot_row]
        scale = rows[pivot_row][col]
        rows[pivot_row] = [entry / scale for entry in rows[pivot_row]]
        for row in range(n):
            if row != pivot_row and rows[row][col] != 0:
                factor = rows[row][col]
                rows[row] = [
                    left - factor * right
                    for left, right in zip(rows[row], rows[pivot_row], strict=True)
                ]
        pivot_row += 1
    return not any(all(entry == 0 for entry in row[:n]) and row[n] != 0 for row in rows)


def _check_pade(
    value: Any,
    series: list[Fraction],
    m: int,
    n: int,
    *,
    normalized: bool,
) -> None:
    if value is None:
        if not normalized or _pade_has_normalized(series, m, n):
            raise AssertionError("reported Padé failure despite an admissible result")
        return
    p = _decode_rat(value["p"])
    q = _decode_rat(value["q"])
    if not q or len(p) > m + 1 or len(q) > n + 1:
        raise AssertionError("Padé degree/nontriviality bound failed")
    if normalized and (not q or q[0] != 1):
        raise AssertionError("normalized Padé denominator does not start with one")
    discrepancy = _sub(_mul(q, series), p)
    for i in range(m + n + 1):
        if i < len(discrepancy) and discrepancy[i] != 0:
            raise AssertionError(f"Padé congruence failed at coefficient {i}")


def _check_result(result: dict[str, Any], cases: dict[str, dict[str, Any]]) -> None:
    case = result["case"]
    op = result["op"]
    value = result["value"]

    if op in {"mul", "square"}:
        left = _poly(cases, f"{case}/left")
        right = left if op == "square" else _poly(cases, f"{case}/right")
        if value.get("kernel") not in {
            "schoolbook", "karatsuba", "ks1", "ks2", "ks3", "ks4", "crt_ntt"
        }:
            raise AssertionError(f"unknown reported kernel {value.get('kernel')!r}")
        if value["coeffs"] != _flint_mul(left, right):
            raise AssertionError("FLINT multiplication mismatch")
        return

    if op in {"ks1", "ks2", "ks3", "ks4", "z_dispatch"}:
        left = _poly(cases, f"{case}/left")
        right = _poly(cases, f"{case}/right")
        if value.get("kernel") not in {
            "schoolbook", "karatsuba", "ks1", "ks2", "ks3", "ks4", "crt_ntt"
        }:
            raise AssertionError(f"unknown reported kernel {value.get('kernel')!r}")
        if op.startswith("ks") and value["kernel"] != op:
            raise AssertionError("forced KS result reported the wrong kernel")
        if value["coeffs"] != _flint_mul(left, right):
            raise AssertionError("coefficient-kernel multiplication mismatch")
        return

    if op.startswith("slice/"):
        _, lo_text, len_text = op.split("/")
        lo, length = int(lo_text), int(len_text)
        product = _flint_mul(
            _poly(cases, f"{case}/left"), _poly(cases, f"{case}/right")
        )
        expected = _trim((product + [0] * (lo + length))[lo : lo + length])
        if value["kernel"] != "karatsuba" or value["coeffs"] != expected:
            raise AssertionError("clipped multiplication mismatch")
        return

    if op == "divmod":
        left = _rat_poly(cases, f"{case}/left")
        right = _rat_poly(cases, f"{case}/right")
        q, r = _divmod(left, right)
        if value != [_encode_rat(q), _encode_rat(r)]:
            raise AssertionError("rational divmod mismatch")
        return

    if op in {"gcd", "xgcd", "xgcd_left"}:
        left = _rat_poly(cases, f"{case}/left")
        right = _rat_poly(cases, f"{case}/right")
        if op == "gcd":
            got = _decode_rat(value)
        else:
            got = _decode_rat(value["gcd"])
        if _monic(got) != _gcd(left, right):
            raise AssertionError("gcd associate mismatch")
        if op == "xgcd":
            s = _decode_rat(value["left"])
            t = _decode_rat(value["right"])
            if _add(_mul(s, left), _mul(t, right)) != got:
                raise AssertionError("xgcd Bézout identity mismatch")
        elif op == "xgcd_left":
            s = _decode_rat(value["left"])
            if right:
                _, remainder = _divmod(_sub(got, _mul(s, left)), right)
                if remainder:
                    raise AssertionError("one-sided xgcd congruence mismatch")
            elif _mul(s, left) != got:
                raise AssertionError("one-sided xgcd zero-modulus mismatch")
        return

    if op.startswith("cyclic/") or op.startswith("negacyclic/"):
        n = int(op.split("/")[1])
        expected = _fold_product(
            _rat_poly(cases, f"{case}/left"),
            _rat_poly(cases, f"{case}/right"),
            n,
            negacyclic=op.startswith("negacyclic/"),
        )
        expected_ints = None if expected is None else [int(x) for x in expected]
        if value != expected_ints:
            raise AssertionError("cyclic product mismatch")
        return

    if op == "eval_many":
        points = _rat_poly(cases, f"{case}/points")
        polynomial = _rat_poly(cases, f"{case}/polynomial")
        if value != [int(_eval(polynomial, x)) for x in points]:
            raise AssertionError("multipoint evaluation mismatch")
        return

    if op == "interpolate":
        points = _rat_poly(cases, f"{case}/points")
        values = _rat_poly(cases, f"{case}/values")
        expected = _interpolate(points, values)
        encoded = None if expected is None else _encode_rat(expected)
        if value != encoded:
            raise AssertionError("interpolation mismatch")
        return

    if op.startswith("ntt_plan/"):
        _, p, n, root = op.split("/")
        if value != _valid_ntt_plan(int(p), int(n), int(root)):
            raise AssertionError("NTT plan validation mismatch")
        return

    if op.startswith("ntt_forward/"):
        p = int(op.split("/")[1])
        inputs = _poly(cases, f"{case}/input")
        if p == 5 and len(inputs) == 2:
            expected = [(inputs[0] + inputs[1]) % p, (inputs[0] - inputs[1]) % p]
        else:
            raise AssertionError("oracle forward transform fixture is not pinned")
        if value != expected:
            raise AssertionError("forward NTT mismatch")
        return

    if op.startswith("ntt_roundtrip/"):
        p = int(op.split("/")[1])
        if value != [x % p for x in _poly(cases, f"{case}/input")]:
            raise AssertionError("NTT round-trip mismatch")
        return

    if op.startswith("ntt_capacity/"):
        _, max_log, n = op.split("/")
        expected = _is_power_of_two(int(n)) and int(n) <= 2 ** int(max_log)
        if value != expected:
            raise AssertionError("NTT catalogue capacity mismatch")
        return

    if op.startswith("fp_direct_ntt/") or op.startswith("fp_crt_ntt/"):
        p = int(op.split("/")[1])
        expected = _modular_product(
            _poly(cases, f"{case}/left"), _poly(cases, f"{case}/right"), p
        )
        if value != expected:
            raise AssertionError("finite-field NTT convolution mismatch")
        return

    if op == "z_crt_ntt":
        expected = _flint_mul(
            _poly(cases, f"{case}/left"), _poly(cases, f"{case}/right")
        )
        if value != expected:
            raise AssertionError("integer CRT-NTT convolution mismatch")
        return

    if op.startswith("pade_homogeneous/") or op.startswith("pade/"):
        m, n = [int(x) for x in op.rsplit("/", 2)[1:]]
        _check_pade(
            value,
            _series(cases, f"{case}/series"),
            m,
            n,
            normalized=op.startswith("pade/"),
        )
        return

    raise AssertionError(f"unsupported operation {op!r}")


def check(source) -> int:
    records = [json.loads(line) for line in source if line.strip()]
    cases = {
        record["case"]: record
        for record in records
        if record.get("kind") != "result"
    }
    results = [record for record in records if record.get("kind") == "result"]
    failures = 0
    for result in results:
        try:
            _check_result(result, cases)
        except Exception as exc:
            failures += 1
            print(
                f"FAIL {result['case']} {result['op']}: "
                f"{type(exc).__name__}: {exc}",
                file=sys.stderr,
            )
    if failures:
        print(f"HexPolyFast oracle: {failures} failure(s)", file=sys.stderr)
        return 1
    print(f"HexPolyFast FLINT/exact-Python oracle: checked {len(results)} results")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        import flint  # noqa: F401
    except ImportError:
        print(
            "HexPolyFast oracle: python-flint unavailable; "
            "using the exact Python convolution fallback",
            file=sys.stderr,
        )
    if args.check:
        with DEFAULT_FIXTURE.open() as source:
            return check(source)
    if args.input:
        with Path(args.input).open() as source:
            return check(source)
    return check(sys.stdin)


if __name__ == "__main__":
    raise SystemExit(main())
