#!/usr/bin/env python3
"""Unit tests for the persistent fmpq_mat rank benchmark endpoint."""

from __future__ import annotations

import unittest
from unittest.mock import patch

from scripts.oracle import flint_bench_driver as driver


class FakeMatrix:
    def __init__(self, rows: list[list[int]]) -> None:
        self.rows = [row[:] for row in rows]
        self.rref_calls = 0

    def rref(self):
        self.rref_calls += 1
        return self, len(self.rows)


class FakeFlint:
    def __init__(self) -> None:
        self.constructed: list[FakeMatrix] = []

    def fmpq_mat(self, rows: list[list[int]]) -> FakeMatrix:
        matrix = FakeMatrix(rows)
        self.constructed.append(matrix)
        return matrix


class FmpqBenchTests(unittest.TestCase):
    def setUp(self) -> None:
        driver._FMPQ_DENSE_CACHE.clear()

    def test_dense_rank_caches_input_and_returns_constant_result(self) -> None:
        fake = FakeFlint()
        with patch.object(driver, "flint", fake):
            self.assertEqual(driver._fmpq_mat_rank_dense({"n": 4}), 4)
            before = [row[:] for row in fake.constructed[0].rows]
            self.assertEqual(driver._fmpq_mat_rank_dense({"n": 4}), 4)
        self.assertEqual(len(fake.constructed), 1)
        self.assertEqual(fake.constructed[0].rows, before)
        self.assertEqual(fake.constructed[0].rref_calls, 2)

    def test_dense_rank_rejects_invalid_dimensions(self) -> None:
        for value in (-1, True, 2.5, "4"):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    driver._fmpq_mat_rank_dense({"n": value})


if __name__ == "__main__":
    unittest.main()
