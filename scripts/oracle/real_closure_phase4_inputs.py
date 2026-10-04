#!/usr/bin/env python3
"""Check the exact printed Phase 4 inputs independently of Hex."""
import argparse
import hashlib
import json
from pathlib import Path

import flint
import z3

COEFFICIENTS = [592704, 402192, 90972, 3266731, -931392, -193914,
                -5792221, 756756, 140742, 3046158, -259308, -42336,
                -520884, 31752, 4536, 216]
PAPER_SHA256 = "4caf52449ebb030fcc9341b864c08b307a944dd0d0fc7fb801413486396d7a19"


def sturm_chain(p):
    chain = [p, p.derivative()]
    while chain[-1]:
        remainder = -(chain[-2] % chain[-1])
        if not remainder:
            break
        chain.append(remainder)
    return chain


def variations(chain, point):
    signs = [1 if value > 0 else -1 for q in chain if (value := q(point))]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def check(paper):
    paper_hash = hashlib.sha256(paper.read_bytes()).hexdigest()
    if paper_hash != PAPER_SHA256:
        raise ValueError("paper PDF differs from the recorded transcription source")
    if flint.__version__ != "0.9.0" or z3.get_version_string() != "4.15.4":
        raise ValueError("expected python-flint0.9.0 and Z34.15.4")
    p = flint.fmpq_poly(COEFFICIENTS)
    unit, factors = p.factor()
    assert len(factors) == 1 and factors[0][0].degree() == 15 and factors[0][1] == 1
    assert p.gcd(p.derivative()) == 1
    chain = sturm_chain(p)
    # Cauchy's bound: every root has |x| < 1 + max |a_i / a_n| < 30000.
    bound = flint.fmpq(30000)
    assert all(1 + abs(flint.fmpq(a, COEFFICIENTS[-1])) < bound
               for a in COEFFICIENTS[:-1])
    lower, upper = -bound, bound
    count = lambda lo, hi: variations(chain, lo) - variations(chain, hi)
    total = count(lower, upper)
    assert total == 3
    while count(lower, upper) != 1 or upper - lower >= flint.fmpq(1, 2):
        midpoint = (lower + upper) / 2
        assert p(midpoint) != 0
        if count(lower, midpoint):
            upper = midpoint
        else:
            lower = midpoint
    assert lower == flint.fmpq(-1875, 2048) and upper == flint.fmpq(-1875, 4096)
    assert p(lower) != 0 and p(upper) != 0 and count(-bound, lower) == 0
    x, epsilon = z3.Reals("x epsilon")
    printed = x**4 - 2*epsilon*x**3 + (epsilon**2-4)*x**2 + 4*epsilon*x + 8-2*epsilon**2
    identity = (x*x-epsilon*x-2)**2 + 4-2*epsilon**2
    identity_check = z3.Solver()
    identity_check.add(printed != identity)
    assert identity_check.check() == z3.unsat
    no_root = z3.Solver()
    no_root.add(epsilon > 0, epsilon < 1, printed <= 0)
    result = no_root.check()
    assert result == z3.unsat
    return {
        "metitarski_coefficients_ascending": COEFFICIENTS,
        "meti_factorization": str((unit, factors)),
        "meti_gcd_derivative": str(p.gcd(p.derivative())),
        "meti_real_root_count": total,
        "least_root_interval": [[int(lower.numerator), int(lower.denominator)],
                                [int(upper.numerator), int(upper.denominator)]],
        "roots_before_interval": count(-bound, lower),
        "roots_in_interval": count(lower, upper),
        "cauchy_bound": 30000,
        "printed_tower8_no_root_below_one": str(result),
        "printed_quartic_identity": "P(x,e) = (x^2-e*x-2)^2 + 4-2*e^2",
        "z3_query": no_root.sexpr(),
        "z3_version": z3.get_version_string(),
        "python_flint_version": flint.__version__,
        "paper_sha256": paper_hash,
        "transcription": {"method": "manually checked against the PDF",
                          "section": 4, "pdf_page": 14,
                          "metitarski": "degree15 followed by y^3+x^3+1",
                          "tower8_constant": "4-2*epsilon^2+4"},
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.paper), indent=2))
