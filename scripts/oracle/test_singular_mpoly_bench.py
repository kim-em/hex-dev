#!/usr/bin/env python3
"""Focused tests for the Singular multivariate GCD benchmark protocol."""

from __future__ import annotations

import unittest

from scripts.oracle import singular_bench_driver as driver


class _FakeSession:
    def __init__(self, answer: bool = True) -> None:
        self.answer = answer
        self.calls: list[tuple[int, str, str]] = []
        self.overhead_calls = 0

    def overhead(self) -> None:
        self.overhead_calls += 1

    def gcd_is_one(self, nvars: int, left: str, right: str) -> bool:
        self.calls.append((nvars, left, right))
        return self.answer


class SingularMpolyBenchTests(unittest.TestCase):
    def test_sparse_expression_and_dispatch(self) -> None:
        request = {
            "family": "integer_mpoly",
            "op": "gcd_is_one",
            "nvars": 2,
            "a": [[[2, 0], 1], [[1, 1], -3], [[0, 0], 2]],
            "b": [[[0, 3], -1], [[1, 0], 4]],
        }
        session = _FakeSession()
        self.assertTrue(driver._dispatch(request, session))
        self.assertEqual(
            session.calls,
            [(2, "x1^2-3*x1*x2+2", "-x2^3+4*x1")],
        )

    def test_overhead_uses_persistent_session(self) -> None:
        session = _FakeSession()
        self.assertTrue(
            driver._dispatch(
                {"family": "integer_mpoly", "op": "overhead"}, session
            )
        )
        self.assertEqual(session.overhead_calls, 1)

    def test_rejects_nonunit_gcd(self) -> None:
        session = _FakeSession(False)
        with self.assertRaisesRegex(ValueError, "nonunit GCD"):
            driver._dispatch(
                {
                    "family": "integer_mpoly",
                    "op": "gcd_is_one",
                    "nvars": 1,
                    "a": [[[1], 1]],
                    "b": [[[1], 1]],
                },
                session,
            )

    def test_rejects_duplicate_monomials(self) -> None:
        with self.assertRaisesRegex(ValueError, "repeats exponent vector"):
            driver._terms([[[1, 0], 2], [[1, 0], 3]], 2, "a")

    def test_rejects_negative_exponent(self) -> None:
        with self.assertRaisesRegex(ValueError, "negative exponent"):
            driver._terms([[[-1, 0], 2]], 2, "a")


if __name__ == "__main__":
    unittest.main()
