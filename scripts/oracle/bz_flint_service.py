#!/usr/bin/env python3
"""FLINT warm factorization service for the cross-system benchmark suite.

Factors integer polynomials with python-flint's ``fmpz_poly.factor`` and speaks
the suite line protocol (see ``factor_service_common.py``). FLINT is the
C-implementation performance ceiling in the comparison.

Run: ``python3 scripts/oracle/bz_flint_service.py`` (reads requests on stdin).
"""

from __future__ import annotations

import flint

from factor_service_common import serve


def factor_fn(coeffs):
    poly = flint.fmpz_poly(coeffs)
    content, factors = poly.factor()
    return int(content), [([int(c) for c in list(g)], int(e)) for g, e in factors]


if __name__ == "__main__":
    serve(factor_fn)
