#!/usr/bin/env python3
"""Focused tests for the Singular multivariate GCD benchmark protocol."""

from __future__ import annotations

import unittest
from unittest import mock

from scripts.oracle import singular_bench_driver as driver


class _FakeSession:
    def __init__(self, answer: bool = True) -> None:
        self.answer = answer
        self.calls: list[tuple[int, str, str]] = []
        self.equal_calls: list[tuple[int, str, str, str]] = []
        self.div_calls: list[tuple[int, str, str, str]] = []
        self.squarefree_calls: list[tuple[int, str]] = []
        self.overhead_calls = 0

    def overhead(self) -> None:
        self.overhead_calls += 1

    def gcd_is_one(self, nvars: int, left: str, right: str) -> bool:
        self.calls.append((nvars, left, right))
        return self.answer

    def gcd_equals(self, nvars: int, left: str, right: str, expected: str) -> bool:
        self.equal_calls.append((nvars, left, right, expected))
        return self.answer

    def div_equals(self, nvars: int, left: str, right: str, expected: str) -> bool:
        self.div_calls.append((nvars, left, right, expected))
        return self.answer

    def squarefree_multiplicities(self, nvars: int, polynomial: str) -> list[int]:
        self.squarefree_calls.append((nvars, polynomial))
        return [3, 1, 2]


class SingularMpolyBenchTests(unittest.TestCase):
    def test_factorize_unit_is_not_a_squarefree_factor(self) -> None:
        self.assertEqual(driver._nonunit_multiplicities("1,1,2"), [1, 2])

    def test_persistent_session_switches_ring_arity(self) -> None:
        session = driver.SingularSession.__new__(driver.SingularSession)
        session._nvars = None
        session._serial = 0
        with mock.patch.object(session, "_request") as request:
            session._ensure_ring(2)
            session._ensure_ring(2)
            session._ensure_ring(4)
        self.assertEqual(request.call_count, 2)
        self.assertIn("ring hex_ring_1=0,(x1,x2),lp", request.call_args_list[0].args[0])
        self.assertIn(
            "ring hex_ring_2=0,(x1,x2,x3,x4),lp",
            request.call_args_list[1].args[0],
        )

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

    def test_rational_gcd_equality(self) -> None:
        request = {
            "family": "rational_mpoly",
            "op": "gcd_equals",
            "nvars": 2,
            "a": [[[1, 0], [1, 2]], [[0, 0], [-2, 3]]],
            "b": [[[0, 1], [3, 5]]],
            "expected": [[[1, 0], [1, 1]], [[0, 0], [2, 3]]],
        }
        session = _FakeSession()
        self.assertTrue(driver._dispatch(request, session))
        self.assertEqual(
            session.equal_calls,
            [(2, "(1/2)*x1-(2/3)", "(3/5)*x2", "x1+(2/3)")],
        )

    def test_exact_division_equality(self) -> None:
        request = {
            "family": "integer_mpoly",
            "op": "div_equals",
            "nvars": 1,
            "a": [[[2], 1], [[0], -1]],
            "b": [[[1], 1], [[0], -1]],
            "expected": [[[1], 1], [[0], 1]],
        }
        session = _FakeSession()
        self.assertTrue(driver._dispatch(request, session))
        self.assertEqual(session.div_calls, [(1, "x1^2-1", "x1-1", "x1+1")])

    def test_squarefree_returns_multiplicity_signature(self) -> None:
        request = {
            "family": "integer_mpoly",
            "op": "squarefree",
            "nvars": 1,
            "a": [[[3], 1], [[0], -1]],
        }
        session = _FakeSession()
        self.assertEqual(driver._dispatch(request, session), [3, 1, 2])
        self.assertEqual(session.squarefree_calls, [(1, "x1^3-1")])

    def test_rejects_duplicate_monomials(self) -> None:
        with self.assertRaisesRegex(ValueError, "repeats exponent vector"):
            driver._terms([[[1, 0], 2], [[1, 0], 3]], 2, "a")

    def test_rejects_negative_exponent(self) -> None:
        with self.assertRaisesRegex(ValueError, "negative exponent"):
            driver._terms([[[-1, 0], 2]], 2, "a")


if __name__ == "__main__":
    unittest.main()
