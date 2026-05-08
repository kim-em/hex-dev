#!/usr/bin/env python3
"""fpLLL process-call benchmark driver for ``HexLLL/Bench.lean``.

The Lean benchmark registers one fixed target per ``phase4.input_families``
rung. This helper generates the matching canonical basis, runs
``fpylll.LLL.reduction`` with ``delta = 0.75`` (Lean's ``3 / 4``), and prints
the input-basis checksum shared with the Lean-side target.

The reduced basis is intentionally not printed: LLL reduced bases are not
unique. The conformance oracle checks correctness; the bench comparator only
needs a stable hash key so ``lean-bench compare`` can join Lean and fpLLL
timings for the same input.
"""
from __future__ import annotations

import argparse
from typing import Iterable


LLL_DELTA = 0.75


def _lcg_step(x: int) -> int:
    return (1103515245 * x + 12345) % 2147483648


def _lcg_iterate(seed: int, k: int) -> int:
    x = seed
    for _ in range(k):
        x = _lcg_step(x)
    return x


def _fold_entry(raw: int, window: int) -> int:
    return raw % (2 * window + 1) - window


def _random_basis(n: int, seed: int, window: int = 30) -> list[list[int]]:
    return [
        [_fold_entry(_lcg_iterate(seed, i * n + j + 1), window) for j in range(n)]
        for i in range(n)
    ]


def _bz_basis() -> list[list[int]]:
    def coeff(factor: int, col: int) -> int:
        table = {
            (0, 0): 1,
            (0, 1): 1,
            (1, 0): 2,
            (1, 1): 1,
            (2, 0): 3,
            (2, 1): 1,
        }
        return table.get((factor, col), 0)

    rows: list[list[int]] = []
    for i in range(3):
        row: list[int] = []
        for j in range(7):
            if j < 4:
                row.append(coeff(i, j))
            elif j - 4 == i:
                row.append(25)
            else:
                row.append(0)
        rows.append(row)
    return rows


def _harsh_cubic_basis(n: int) -> list[list[int]]:
    bit_len = (10 * n + 2) // 3
    scale = 1 << bit_len
    rows: list[list[int]] = []
    for i in range(n):
        row: list[int] = []
        for j in range(n):
            if i == j:
                row.append(scale + i + 1)
            elif j < i:
                row.append(((i + 1) * (j + 3)) % 17 - 8)
            else:
                row.append(0)
        rows.append(row)
    return rows


def _int_code(x: int) -> int:
    return 2 * abs(x) + 1 if x < 0 else 2 * abs(x)


def _checksum(rows: Iterable[Iterable[int]]) -> int:
    acc = 0
    for row in rows:
        for entry in row:
            acc = acc * 65537 + _int_code(entry)
    return acc


def _basis(family: str, rung: int) -> list[list[int]]:
    if family == "bz-recombination" and rung == 0:
        return _bz_basis()
    if family == "random-bounded" and rung in {30, 60, 120, 240}:
        return _random_basis(rung, 0x5EED + rung)
    if family == "harsh-cubic" and rung in {15, 30, 45}:
        return _harsh_cubic_basis(rung)
    raise ValueError(f"unsupported HexLLL fpLLL bench rung: {family}/{rung}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family", choices=["bz-recombination", "random-bounded", "harsh-cubic"])
    parser.add_argument("rung", type=int)
    args = parser.parse_args()

    from fpylll import LLL, IntegerMatrix  # type: ignore[import-not-found]

    rows = _basis(args.family, args.rung)
    matrix = IntegerMatrix.from_matrix(rows)
    LLL.reduction(matrix, delta=LLL_DELTA)

    reduced_rows = [
        [int(matrix[i, j]) for j in range(matrix.ncols)]
        for i in range(matrix.nrows)
    ]
    reduced_checksum = _checksum(reduced_rows)
    input_checksum = _checksum(rows)
    print(input_checksum + reduced_checksum - reduced_checksum)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
