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

# PARI's default 8 MB stack overflows on the largest corpus instances (e.g. the
# degree-630 hoeij_F630, which factors in under a second with more headroom).
# Start at 64 MiB and let PARI grow the stack lazily up to a 2 GiB ceiling, so
# the comparison measures PARI's factoring, not an artificial memory limit. A
# genuine over-cutoff instance is still killed by the orchestrator as a timeout.
_pari = cypari2.Pari(size=1 << 26, sizemax=1 << 31)


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
