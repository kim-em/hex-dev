#!/usr/bin/env python3
"""Validate rational-trace subjects with FLINT and exact selected-root comparisons.

Operation counts and bit maxima are native observations, not independently
recomputed here. No runtime scaling model is asserted.
"""
from fractions import Fraction
import json
from pathlib import Path
import sys
from flint import fmpq, fmpq_poly
# Support direct invocation from the repository root.
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.sign_det_trace_archive import check_retained


def polynomial(pairs):
    if not isinstance(pairs, list):
        raise ValueError('invalid polynomial')
    return fmpq_poly([fmpq(endpoint(pair).numerator, endpoint(pair).denominator) for pair in pairs])


def endpoint(pair):
    if len(pair) != 2 or any(type(x) is not int for x in pair) or pair[1] <= 0:
        raise ValueError('invalid rational endpoint')
    return Fraction(*pair)


def positive_sqrt_interval(bounds):
    lo, hi = map(endpoint, bounds)
    # Also excludes the negative square root and endpoint roots.
    if not (0 <= lo < hi and lo*lo < 2 < hi*hi):
        raise ValueError('interval does not select positive sqrt(2)')


def monic(p):
    if not p:
        raise ValueError('zero common factor or head')
    return p * (fmpq(1) / p[p.degree()])


def validate(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if [r['result']['extraFactors'] for r in rows] != [1, 2, 3]:
        raise ValueError('missing or reordered cases')
    for row in rows:
        result = row['result']
        n = result['extraFactors']
        p = fmpq_poly([-2, 0, 1])
        q = p
        for k in range(3, n+3):
            q *= fmpq_poly([-k, 1])
        if polynomial(result['left']) != p or polynomial(result['right']) != q:
            raise ValueError('wrong source polynomial')
        for factor_key, head_key in [('factor','commonHead'), ('strictFactor','strictCommonHead')]:
            factor, head = polynomial(result[factor_key]), polynomial(result[head_key])
            if monic(factor) != monic(p.gcd(q)) or factor * head != p*q:
                raise ValueError('wrong common factor or head')
        positive_sqrt_interval(result['leftInterval'])
        positive_sqrt_interval(result['sameInterval'])
        lo, hi = map(endpoint, result['sameInterval'])
        if any(lo <= k <= hi for k in range(3, n+3)):
            raise ValueError('Q interval contains an extra integer root')
        lo, hi = map(endpoint, result['lastInterval'])
        if not (2 < lo < n+2 < hi) or any(lo <= k <= hi for k in range(3, n+2)):
            raise ValueError('interval does not uniquely select the last integer root')
        if result['equalOrder'] != 'eq' or result['strictOrder'] != 'lt':
            raise ValueError('wrong root order')
        if result['context'] != 10377+n or result['standardReplayAccepted'] is not True:
            raise ValueError('wrong context or failed ordinary replay')
        calls, bits = row['coefficientCalls'], row['maxNormalizedBits']
        if type(calls) is not int or calls <= 0 or type(bits) is not int or bits <= 0:
            raise ValueError('missing arithmetic observations')
        ops = row['operationCalls']
        if len(ops) != 8 or any(type(v) is not int or v <= 0 for v in ops) or sum(ops) != calls:
            raise ValueError('missing per-operation coverage')
        if row['temporaryBitBound'] != 2*bits+1:
            raise ValueError('wrong binary rational-operation bound')
    return rows


if __name__ == '__main__':
    validate(sys.argv[1])
    if '--retained' in sys.argv[2:]:
        check_retained(sys.argv[1])
    print('3/3 exact polynomial, common-root, selected-root/order and trace schema checks pass')
