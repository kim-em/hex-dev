#!/usr/bin/env python3
"""Check fixed Hilbert polynomials by independent analytic CM computation.

Requires mpmath 1.3.0. No PARI calls and no native ECPP production.
The j-function is E4(q)^3 / (q*product(1-q^k)^24).
"""
from __future__ import annotations
import argparse
import json
import math
from pathlib import Path
import re
import mpmath as mp

ROOT = Path(__file__).resolve().parents[2]

def forms(d):
    out = []
    for a in range(1, math.isqrt(d // 3) + 1):
        for b in range(-a, a + 1):
            if (b*b+d) % (4*a):
                continue
            c = (b*b+d)//(4*a)
            if a > c or ((abs(b) == a or a == c) and b < 0):
                continue
            if math.gcd(a, math.gcd(b, c)) == 1:
                out.append((a, b, c))
    return out

def analytic(d, precision):
    with mp.workdps(precision):
        polynomial = [mp.mpc(1)]
        for a, b, _ in forms(d):
            q = mp.exp(mp.pi * (-mp.sqrt(d) - mp.j*b)/a)
            e4, delta, power = mp.mpc(1), q, mp.mpc(1)
            # Reduced forms give |q| <= exp(-pi*sqrt(3)); 2*precision
            # terms leave a large margin even after coefficient products.
            for k in range(1, 2*precision + 1):
                power *= q
                sigma = sum(t**3 for t in range(1, k+1) if k % t == 0)
                e4 += 240*sigma*power
                delta *= (1-power)**24
            j = e4**3/delta
            product = [mp.mpc(0)]*(len(polynomial)+1)
            for i, coefficient in enumerate(polynomial):
                product[i] -= j*coefficient
                product[i+1] += coefficient
            polynomial = product
        rounded = []
        for x in polynomial:
            integer = int(mp.nint(x.real))
            assert abs(x.real-integer) < mp.mpf('1e-100') and abs(x.imag) < mp.mpf('1e-100'), (d, x)
            rounded.append(integer)
        return rounded

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    source = (ROOT/'HexECPP/CM/ClassPolynomials.lean').read_text()
    entries = [(int(d), json.loads('['+cs+']')) for d, cs in
               re.findall(r'⟨(\d+), \[([^\]]+)\]⟩', source)]
    expected = [d for d in range(3, 501) if d % 4 in (0, 3)
                and len(forms(d)) in (1, 2) and d not in (3,4,7,8,11,19,43,67,163)]
    assert [d for d, _ in entries] == expected and len(entries) == 33
    result = []
    for d, coefficients in entries:
        assert analytic(d, 160) == coefficients == analytic(d, 240), d
        result.append(dict(d=d, coefficients=coefficients, reduced_forms=forms(d)))
    if args.output:
        assert not args.output.exists(), 'retain previous checks'
        args.output.write_text(json.dumps(dict(method='primitive reduced forms; E4 cubed divided by Delta',
            mpmath=mp.__version__, precisions=[160,240], absolute_rounding_tolerance='1e-100', entries=result), indent=2)+'\n')
    print('independent Hilbert polynomial checks passed: 33 entries')

if __name__ == '__main__':
    main()
