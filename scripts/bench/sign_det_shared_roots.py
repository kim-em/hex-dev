#!/usr/bin/env python3
"""Validate the bounded shared-root inventory independently with FLINT.

P=X²−2, Q=P times the distinct linear factors X−3,...,X−(n+2).
The polynomial identities are checked independently. Interval and order fields
are expected literals in the archived inspector, so their consistency checks
do not independently verify the actual root selection or comparison.
Recorded query/matrix counts are observations, not independently derived here.
"""
import json
from pathlib import Path
import sys
from flint import fmpq, fmpq_poly


def polynomial(coefficients):
    if not isinstance(coefficients, list):
        raise ValueError('polynomial coefficients must be a list')
    for pair in coefficients:
        if not isinstance(pair, list) or len(pair) != 2 or any(type(x) is not int for x in pair) or pair[1] <= 0:
            raise ValueError('invalid rational coefficient')
    return fmpq_poly([fmpq(a, b) for a, b in coefficients])


def validate(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if [r['extraFactors'] for r in rows] != [1, 2, 3]:
        raise ValueError('missing, repeated or reordered input')
    p = fmpq_poly([-2, 0, 1])
    for row, n in zip(rows, [1, 2, 3], strict=True):
        q = p
        for k in range(3, n + 3):
            q *= fmpq_poly([-k, 1])
        if polynomial(row['left']) != p or polynomial(row['right']) != q:
            raise ValueError('wrong source polynomial')
        if polynomial(row['factor']) != p.gcd(q) or polynomial(row['commonHead']) != q:
            raise ValueError('wrong gcd or common polynomial')
        if row['sourceInterval'] != [0, 2] or row['lastIntervalTwice'] != [2*n+3, 2*n+5]:
            raise ValueError('changed root selection')
        if row['equalOrder'] != 'eq' or row['strictOrder'] != 'lt':
            raise ValueError('wrong selected-root order')
        # P has one root in (0,2). Q has that same root and distinct integer
        # roots >=3. The half-integer interval isolates its largest root n+2.
        if row['commonProductGcdCalls'] != 2:
            raise ValueError('wrong common-product constructor call count')
        for key in ['jointMomentCounts', 'maxMatrixWidths']:
            if len(row[key]) != 4 or any(type(v) is not int or v <= 0 for v in row[key]):
                raise ValueError('invalid recorded query or matrix count')
        if type(row['resultHash']) is not int or not 0 <= row['resultHash'] < 2**64:
            raise ValueError('invalid callback digest')
    return rows


if __name__ == '__main__':
    validate(sys.argv[1])
    print('3/3 shared-root polynomial inventories agree with independent FLINT arithmetic; expected interval/order literals match')
