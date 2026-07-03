#!/usr/bin/env python3
"""PARI/GP warm factorization service for the cross-system benchmark suite.

Factors integer polynomials with PARI (via cypari2, precedent
``scripts/oracle/hensel_pari.py``) and speaks the suite line protocol (see
``factor_service_common.py``).

``Polrev`` reads an ascending coefficient vector; ``Vecrev`` returns one. PARI's
``factor`` yields the primitive irreducible factors over Q; the integer content
(with sign) is recovered as ``poly / prod(factor^mult)``.

Run: ``python3 scripts/oracle/bz_pari_service.py`` (reads requests on stdin).
"""

from __future__ import annotations

import cypari2

from factor_service_common import serve

_pari = cypari2.Pari()


def factor_fn(coeffs):
    poly = _pari.Polrev(list(coeffs))
    fac = poly.factor()
    reconstruction = _pari(1)
    factors = []
    for g, exponent in zip(fac[0], fac[1]):
        exponent = int(exponent)
        gcoeffs = [int(c) for c in _pari.Vecrev(g)]
        factors.append((gcoeffs, exponent))
        reconstruction = reconstruction * g ** exponent
    scalar = int(poly / reconstruction) if factors else int(poly)
    return scalar, factors


if __name__ == "__main__":
    serve(factor_fn)
