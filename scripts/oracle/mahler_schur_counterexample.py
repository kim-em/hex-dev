#!/usr/bin/env python3
"""Check narrow Schur-route counterexamples.

This is a narrow regression artifact for failed routes toward the
Mahler/Boyd derivative bound.  It verifies that both the scaled endpoint
comparison and the direct Schur-reflection derivative-Mahler comparison from
issue #5303 are false without additional hypotheses, and that the degree-two
Schur-Szego one-exterior root-count exclusion is false.

Counterexample in ``C[X]`` with real coefficients:

    f = 2 X^3 + 2 X^2 - 3 X - 4
    alpha = -2

The script is intentionally stdlib-only.  Polynomial identities and the Schur
stability checks are exact integer/rational computations; decimal values are
printed only for readability.
"""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, getcontext
from fractions import Fraction


Poly = tuple[int, ...]  # ascending coefficient order


def trim(p: list[int]) -> Poly:
    while p and p[-1] == 0:
        p.pop()
    return tuple(p)


def mul(p: Poly, q: Poly) -> Poly:
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)


def deriv(p: Poly) -> Poly:
    return trim([i * c for i, c in enumerate(p)][1:])


def schur_transform_desc(coeffs: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    """One exact Schur transform step for a real polynomial.

    For ``p(z) = a_0 z^n + ... + a_n`` with ``a_0 > |a_n|``, Schur's
    recursion replaces ``p`` by

        (a_0 p(z) - a_n z^n p(1 / z)) / z,

    whose roots are in the open unit disk iff the roots of ``p`` are.
    The trailing zero after the subtraction is omitted.
    """
    a0 = coeffs[0]
    an = coeffs[-1]
    return tuple(a0 * coeffs[i] - an * coeffs[-1 - i] for i in range(len(coeffs) - 1))


def schur_stable_desc(coeffs: tuple[int, ...]) -> list[tuple[Fraction, ...]]:
    """Return the exact Schur recursion chain, asserting unit-disk roots."""
    chain: list[tuple[Fraction, ...]] = [tuple(Fraction(c) for c in coeffs)]
    cur = chain[0]
    while len(cur) > 1:
        if cur[0] <= 0:
            raise AssertionError(f"expected positive leading coefficient: {cur}")
        if abs(cur[-1]) >= cur[0]:
            raise AssertionError(f"Schur criterion failed at {cur}")
        cur = schur_transform_desc(cur)
        chain.append(cur)
    return chain


@dataclass(frozen=True)
class Counterexample:
    f: Poly = (-4, -3, 2, 2)
    alpha: int = -2

    @property
    def left_factor(self) -> Poly:
        # X - alpha = X + 2.
        return (-self.alpha, 1)

    @property
    def reflected_factor(self) -> Poly:
        # 1 - conj(alpha) X = 1 + 2 X for real alpha = -2.
        return (1, -self.alpha)


@dataclass(frozen=True)
class DegreeTwoSchurCounterexample:
    r: int = 1
    a: int = 1
    b: int = 4
    c: int = 1
    d: int = -1
    zeta1: int = 2
    zeta2: int = -2


def strict_exterior_count_real(values: tuple[int, ...], r: int) -> int:
    return sum(1 for value in values if r < abs(value))


def check_degree_two_schur_one_exterior_counterexample() -> None:
    case = DegreeTwoSchurCounterexample()

    if abs(case.c) > 1 or abs(case.d) > 1:
        raise AssertionError("Schur factor roots must lie in the closed unit disk")

    source_exterior = strict_exterior_count_real((case.a, case.b), case.r)
    schur_exterior = strict_exterior_count_real((case.zeta1, case.zeta2), case.r)
    if source_exterior != 1:
        raise AssertionError(f"source exterior count mismatch: {source_exterior}")
    if schur_exterior != 2:
        raise AssertionError(f"Schur exterior count mismatch: {schur_exterior}")

    # For f = (X - a) (X - b) and g = (X - c) (X - d), the degree-two
    # Schmeisser composition has coefficients
    #   X^2 + ((a + b) * (c + d) / 2) X + a * b * c * d.
    # Hence the exact Vieta orientation used by
    # Polynomial.schmeisserComposition_two_eq is:
    #   zeta1 + zeta2 = -((a + b) * (c + d) / 2)
    #   zeta1 * zeta2 = a * b * c * d.
    expected_sum = -Fraction((case.a + case.b) * (case.c + case.d), 2)
    expected_product = case.a * case.b * case.c * case.d
    if Fraction(case.zeta1 + case.zeta2) != expected_sum:
        raise AssertionError("degree-two Schur Vieta sum orientation mismatch")
    if case.zeta1 * case.zeta2 != expected_product:
        raise AssertionError("degree-two Schur Vieta product mismatch")

    if not (source_exterior < schur_exterior):
        raise AssertionError("expected strict exterior-card comparison to fail")


def main() -> int:
    getcontext().prec = 50
    case = Counterexample()

    left_derivative = deriv(mul(case.f, case.left_factor))
    right_derivative = deriv(mul(case.f, case.reflected_factor))

    expected_left = (-10, 2, 18, 8)
    expected_right = (-11, -8, 18, 16)
    if left_derivative != expected_left:
        raise AssertionError(f"left derivative mismatch: {left_derivative}")
    if right_derivative != expected_right:
        raise AssertionError(f"right derivative mismatch: {right_derivative}")

    # left_derivative = 2 * (4 X + 5) * (X^2 + X - 1).
    # Its exterior roots are -5/4 and -(1 + sqrt(5)) / 2, so
    # M(left_derivative) = 8 * 5/4 * (1 + sqrt(5)) / 2.
    left_measure_formula = "5 * (1 + sqrt(5))"
    # Exact proof that 5 * (1 + sqrt(5)) > 16:
    # equivalent to sqrt(5) > 11/5; both sides are positive, and
    # 5 > (11/5)^2.
    if Fraction(5, 1) <= Fraction(121, 25):
        raise AssertionError("exact sqrt(5) lower-bound check failed")

    # The reflected derivative is 16 X^3 + 18 X^2 - 8 X - 11.
    # Exact Schur recursion certifies all roots have modulus < 1, hence its
    # Mahler measure is the absolute leading coefficient, 16.
    schur_chain = schur_stable_desc((16, 18, -8, -11))
    right_measure = 16

    sqrt5 = Decimal(5).sqrt()
    left_decimal = Decimal(5) * (Decimal(1) + sqrt5)
    if not (left_decimal > Decimal(right_measure)):
        raise AssertionError("decimal sanity check failed")

    print("counterexample: f = 2*X^3 + 2*X^2 - 3*X - 4, alpha = -2")
    print(f"left derivative coefficients: {left_derivative}")
    print(f"right derivative coefficients: {right_derivative}")
    print(f"left Mahler measure: {left_measure_formula} = {left_decimal}")
    print(f"right Schur chain: {schur_chain}")
    print(f"right Mahler measure: {right_measure}")
    print(
        "failure: direct endpoint inequality would require "
        f"{left_measure_formula} <= {right_measure}"
    )
    print(
        "failure: scaled endpoint inequality would require "
        f"{left_measure_formula} <= {right_measure}"
    )

    check_degree_two_schur_one_exterior_counterexample()
    degree_two_case = DegreeTwoSchurCounterexample()
    print(
        "counterexample: degree-two Schur one-exterior count with "
        f"r = {degree_two_case.r}, "
        f"(a, b) = ({degree_two_case.a}, {degree_two_case.b}), "
        f"(c, d) = ({degree_two_case.c}, {degree_two_case.d}), "
        f"(zeta1, zeta2) = ({degree_two_case.zeta1}, {degree_two_case.zeta2})"
    )
    print("failure: source exterior count is 1 while Schur exterior count is 2")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
