#!/usr/bin/env python3
"""Regression tests for the FLINT rational row-reduction bench adapter."""

from __future__ import annotations

import unittest

from scripts.oracle import flint_bench_driver as driver


class RowReduceBenchDriverTests(unittest.TestCase):
    def test_rref_records_rank_pivots_and_canonical_rows(self) -> None:
        answer = driver._dispatch(
            {
                "family": "fmpq_mat",
                "op": "rref",
                "rows": [[2, 1, 2, 1], [1, 2, 1, 2], [2, 1, 2, 1], [1, 2, 1, 2]],
            }
        )
        self.assertEqual(answer["rank"], 2)
        self.assertEqual(answer["pivots"], [0, 1])
        self.assertEqual(
            answer["rows"],
            [
                [[1, 1], [0, 1], [1, 1], [0, 1]],
                [[0, 1], [1, 1], [0, 1], [1, 1]],
                [[0, 1], [0, 1], [0, 1], [0, 1]],
                [[0, 1], [0, 1], [0, 1], [0, 1]],
            ],
        )

    def test_nullspace_uses_free_variable_basis(self) -> None:
        answer = driver._dispatch(
            {
                "family": "fmpq_mat",
                "op": "nullspace",
                "rows": [[2, 1, 2, 1], [1, 2, 1, 2], [2, 1, 2, 1], [1, 2, 1, 2]],
            }
        )
        self.assertEqual(answer["rank"], 2)
        self.assertEqual(
            answer["basis"],
            [
                [[-1, 1], [0, 1], [1, 1], [0, 1]],
                [[0, 1], [-1, 1], [0, 1], [1, 1]],
            ],
        )

    def test_overhead_shape(self) -> None:
        self.assertEqual(
            driver._dispatch({"family": "fmpq_mat", "op": "overhead"}),
            {"rank": 0, "pivots": [], "rows": []},
        )


if __name__ == "__main__":
    unittest.main()
