#!/usr/bin/env python3
"""Focused tests for the shared FLINT multivariate-polynomial protocol."""

from __future__ import annotations

import unittest
from unittest import mock
from fractions import Fraction

from scripts.oracle import flint_bench_driver as driver


class _FakePoly:
    def __init__(self, terms: dict[tuple[int, ...], int]) -> None:
        self._terms = terms

    def gcd(self, other: "_FakePoly") -> "_FakePoly":
        del other
        return _FakePoly({(1, 0): 1, (0, 1): 1, (0, 0): 1})

    def __eq__(self, other: object) -> bool:
        if other == 0:
            return not self._terms
        return isinstance(other, _FakePoly) and self._terms == other._terms

    def __divmod__(self, other: "_FakePoly") -> tuple["_FakePoly", "_FakePoly"]:
        del other
        return _FakePoly({(1, 0): 1, (0, 0): 2}), _FakePoly({})

    def factor_squarefree(self):
        return 1, [(_FakePoly({(1, 0): 1}), 3), (_FakePoly({(0, 1): 1}), 1)]

    def terms(self):
        return self._terms.items()


class _FakeContext:
    def __init__(self, arity: int) -> None:
        self._arity = arity

    def nvars(self) -> int:
        return self._arity

    def from_dict(self, terms: dict[tuple[int, ...], int]) -> _FakePoly:
        return _FakePoly(terms)


class _FakeContextFactory:
    calls: list[tuple[tuple[str, ...], str]] = []

    @classmethod
    def get(cls, names: tuple[str, ...], ordering: str) -> _FakeContext:
        cls.calls.append((names, ordering))
        return _FakeContext(len(names))


class _FakeFlint:
    fmpz_mpoly_ctx = _FakeContextFactory


class _FakeRational:
    def __init__(self, numerator: int, denominator: int = 1) -> None:
        value = Fraction(numerator, denominator)
        self.p = value.numerator
        self.q = value.denominator

    def __eq__(self, other: object) -> bool:
        if isinstance(other, _FakeRational):
            return (self.p, self.q) == (other.p, other.q)
        if isinstance(other, int):
            return self.p == other * self.q
        return False


class _FakeQPoly:
    def __init__(self, terms) -> None:
        self._terms = terms

    def gcd(self, other: "_FakeQPoly") -> "_FakeQPoly":
        del other
        return _FakeQPoly({(1, 0): _FakeRational(1), (0, 0): _FakeRational(2, 3)})

    def terms(self):
        return self._terms.items()


class _FakeQContext(_FakeContext):
    def from_dict(self, terms) -> _FakeQPoly:
        return _FakeQPoly(terms)


class _FakeQContextFactory:
    @classmethod
    def get(cls, names: tuple[str, ...], ordering: str) -> _FakeQContext:
        del ordering
        return _FakeQContext(len(names))


class _FakeFlintWithQ(_FakeFlint):
    fmpq = _FakeRational
    fmpq_mpoly_ctx = _FakeQContextFactory


class FlintMpolyBenchTests(unittest.TestCase):
    def setUp(self) -> None:
        _FakeContextFactory.calls.clear()

    def test_gcd_uses_lex_context_and_sparse_terms(self) -> None:
        request = {
            "family": "fmpz_mpoly",
            "op": "gcd",
            "nvars": 2,
            "a": [[[2, 0], 1], [[1, 0], 3], [[0, 0], 2]],
            "b": [[[1, 1], 1], [[0, 1], 4], [[0, 0], 3]],
        }
        with (
            mock.patch.object(driver, "_require_flint"),
            mock.patch.object(driver, "flint", _FakeFlint),
        ):
            answer = driver._dispatch(request)
        self.assertEqual(
            answer,
            [[[0, 0], 1], [[0, 1], 1], [[1, 0], 1]],
        )
        self.assertEqual(_FakeContextFactory.calls, [(('x0', 'x1'), 'lex')])

    def test_zero_coefficients_are_omitted(self) -> None:
        terms = driver._fmpz_mpoly_terms(
            [[[1, 0], 0], [[0, 1], -3]], 2, "a"
        )
        self.assertEqual(terms, {(0, 1): -3})

    def test_exact_division_and_squarefree_multiplicities(self) -> None:
        base = {
            "family": "fmpz_mpoly",
            "nvars": 2,
            "a": [[[2, 0], 1]],
            "b": [[[1, 0], 1]],
        }
        with (
            mock.patch.object(driver, "_require_flint"),
            mock.patch.object(driver, "flint", _FakeFlint),
        ):
            quotient = driver._dispatch({**base, "op": "divexact"})
            multiplicities = driver._dispatch({**base, "op": "squarefree"})
        self.assertEqual(quotient, [[[0, 0], 2], [[1, 0], 1]])
        self.assertEqual(multiplicities, [1, 3])

    def test_rational_gcd_round_trips_reduced_coefficients(self) -> None:
        request = {
            "family": "fmpq_mpoly",
            "op": "gcd",
            "nvars": 2,
            "a": [[[1, 0], [2, 4]], [[0, 0], [1, 3]]],
            "b": [[[1, 0], [3, 6]], [[0, 0], [2, 3]]],
        }
        with (
            mock.patch.object(driver, "_require_flint"),
            mock.patch.object(driver, "flint", _FakeFlintWithQ),
        ):
            answer = driver._dispatch(request)
        self.assertEqual(answer, [[[0, 0], [2, 3]], [[1, 0], [1, 1]]])

    def test_rejects_wrong_exponent_arity(self) -> None:
        with self.assertRaisesRegex(ValueError, "exponent length 1; expected 2"):
            driver._fmpz_mpoly_terms([[[1], 2]], 2, "a")

    def test_rejects_duplicate_monomials(self) -> None:
        with self.assertRaisesRegex(ValueError, "repeats exponent vector"):
            driver._fmpz_mpoly_terms(
                [[[1, 0], 2], [[1, 0], 3]], 2, "a"
            )

    def test_rejects_negative_exponents(self) -> None:
        with self.assertRaisesRegex(ValueError, "negative exponent"):
            driver._fmpz_mpoly_terms([[[-1, 0], 2]], 2, "a")


if __name__ == "__main__":
    unittest.main()
