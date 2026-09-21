#!/usr/bin/env python3
"""Check closed-form coefficient costs against retained production certificates.

This is an untimed input-family calculation, not a polynomial/query backend or
an empirical fit. All formulas use exact integers and no timing observations.
"""
from __future__ import annotations

import json
from math import comb, gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "reports/bench-results/sturm-ec8f7c14f914/fixtures.jsonl"


def primitive_u(k: int) -> list[int]:
    coefficients = [0] * (k + 1)
    content = (k + 1) & -(k + 1)
    for j in range(k // 2 + 1):
        coefficients[k - 2 * j] = (-1) ** j * comb(k - j, j) * 2 ** (k - 2 * j)
    assert gcd(*coefficients) == content
    return [c // content for c in coefficients]


def normalization_cost(coefficients: list[int]) -> tuple[int, int, int]:
    stored = iterations = bit_work = 0
    for c in coefficients:
        c = abs(c)
        if c:
            b = c.bit_length()
            t = (c & -c).bit_length() - 1
            stored += b
            iterations += t
            # Sizes of the successive integer divisions by two.
            bit_work += t * b - t * (t - 1) // 2
    return stored, iterations, bit_work


def main() -> None:
    checked_head = checked_query = 0
    for line in FIXTURES.read_text().splitlines():
        row = json.loads(line)
        n = row["parameter"]
        chain = row["certificate"]["remainders"]
        if row["family"] == "head-degree":
            assert chain["chain"][1:] == [primitive_u(k) for k in reversed(range(n))]
            checked_head += 1
        else:
            assert n % 2 == 0
            quotient = [0 if k % 2 == 0 else 2 ** ((n + 1 - k) // 2) for k in range(n)]
            assert chain["initial"][0] == 1
            assert chain["initial"][1][0] == quotient
            assert chain["initial"][1][1] == 2 ** (n // 2 + 1) + 2
            assert sum(c.bit_length() for c in quotient) == (n // 2) * (n // 2 + 3) // 2
            checked_query += 1
    print(json.dumps({"checked_head_certificates": checked_head,
                      "checked_query_certificates": checked_query}))
    total = [0, 0, 0]
    for k in range(1024):
        total = [a + b for a, b in zip(total, normalization_cost(primitive_u(k)))]
        if k + 1 in (128, 256, 512, 1024):
            print(json.dumps({"head_degree": k + 1, "tail_stored_bits": total[0],
                              "tail_trailing_zero_iterations": total[1],
                              "tail_division_bit_volume": total[2]}))


if __name__ == "__main__":
    main()
