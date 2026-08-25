#!/usr/bin/env python3
"""Regression tests for the FLINT/PARI Hermite benchmark adapters."""

from __future__ import annotations

import unittest

from scripts.oracle import flint_bench_driver, pari_bench_driver


class HermiteBenchDriverTests(unittest.TestCase):
    CASES = (
        [[2, 4], [3, 5]],
        [[2, 4], [4, 8]],
        [[2, 4, 6], [3, 5, 7]],
        [[2, 4], [3, 5], [1, 7]],
    )

    def test_flint_and_pari_agree_on_row_hnf(self) -> None:
        for rows in self.CASES:
            request = {"rows": rows}
            self.assertEqual(
                flint_bench_driver._fmpz_mat_hnf(request),
                pari_bench_driver._hnf(request),
            )

    def test_pari_preserves_rectangular_shape(self) -> None:
        for rows in self.CASES:
            form = pari_bench_driver._hnf({"rows": rows})
            self.assertEqual(len(form), len(rows))
            self.assertTrue(all(len(row) == len(rows[0]) for row in form))

    def test_overhead_dispatch(self) -> None:
        self.assertEqual(
            flint_bench_driver._dispatch(
                {"family": "fmpz_mat", "op": "overhead"}
            ),
            0,
        )
        self.assertEqual(
            pari_bench_driver._dispatch(
                {"family": "fmpz_mat", "op": "overhead"}
            ),
            0,
        )


if __name__ == "__main__":
    unittest.main()
