#!/usr/bin/env python3
"""Independently check actual selected intervals/orders in the small work inventory.

Polynomial arithmetic uses FLINT. Root comparisons use exact rational squares
against 2 and the explicit linear-factor roots. Table counts and literal bit
maxima are native observations; this validator only checks their schema.
"""
from fractions import Fraction
import json
from pathlib import Path
import sys
from flint import fmpq
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.sign_det_shared_roots import polynomial


def sign(x):
    return (x > 0) - (x < 0)


def rational(pair):
    if not isinstance(pair, list) or len(pair) != 2 or any(type(v) is not int for v in pair) or pair[1] <= 0:
        raise ValueError('invalid rational endpoint')
    return Fraction(*pair)


def monic(p):
    if not p:
        raise ValueError('zero common polynomial or factor')
    return p * (fmpq(1) / p[p.degree()])


def compare_bound(root, bound):
    kind, value = root
    if kind == 'int':
        return sign(Fraction(value) - bound)
    if value == -1:
        return -compare_bound(('sqrt', 1), -bound)
    return 1 if bound < 0 else sign(Fraction(2) - bound * bound)


def selected(roots, endpoints):
    if not isinstance(endpoints, list) or len(endpoints) != 2:
        raise ValueError('invalid interval')
    lo, hi = map(rational, endpoints)
    found = [r for r in roots if compare_bound(r, lo) > 0 and compare_bound(r, hi) < 0]
    if lo >= hi or len(found) != 1:
        raise ValueError('interval does not select exactly one root')
    return found[0]


def compare_roots(left, right):
    if right[0] == 'int':
        return compare_bound(left, Fraction(right[1]))
    if left[0] == 'int':
        return -compare_bound(right, Fraction(left[1]))
    return sign(left[1] - right[1])


def validate(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if [r['extraFactors'] for r in rows] != [1, 2, 3]:
        raise ValueError('missing, repeated or reordered case')
    for row in rows:
        n = row['extraFactors']
        p = polynomial([[-2, 1], [0, 1], [1, 1]])
        q = p
        for k in range(3, n + 3):
            q *= polynomial([[-k, 1], [1, 1]])
        if polynomial(row['left']) != p or polynomial(row['right']) != q:
            raise ValueError('wrong source polynomial')
        factor, head = polynomial(row['factor']), polynomial(row['commonHead'])
        if monic(factor) != monic(p.gcd(q)) or monic(head) != monic(q) or factor * head != p * q:
            raise ValueError('wrong common factor/product')
        irrational = [('sqrt', -1), ('sqrt', 1)]
        roots = irrational + [('int', k) for k in range(3, n + 3)]
        left = selected(irrational, row['leftInterval'])
        same = selected(roots, row['sameInterval'])
        last = selected(roots, row['lastInterval'])
        orders = {-1: 'lt', 0: 'eq', 1: 'gt'}
        if row['equalOrder'] != orders[compare_roots(left, same)] or row['strictOrder'] != orders[compare_roots(left, last)]:
            raise ValueError('wrong selected-root order')
        if left != ('sqrt', 1) or same != left or last != ('int', n + 2):
            raise ValueError('changed selected roots')
        counts = row['tableMomentCounts']
        if len(counts) != 11 or counts[:3] != [1, 1, 1] or any(type(v) is not int or v <= 0 for v in counts):
            raise ValueError('invalid eleven-table inventory')
        if row['totalTableMoments'] != sum(counts):
            raise ValueError('wrong moment sum')
        if type(row['maxLiteralCoefficientBits']) is not int or row['maxLiteralCoefficientBits'] < 1:
            raise ValueError('invalid literal bit maximum')
        if type(row['resultHash']) is not int or not 0 <= row['resultHash'] < 2**64:
            raise ValueError('invalid callback digest')
    return rows


if __name__ == '__main__':
    validate(sys.argv[1])
    print('3/3 work inventories: independent polynomial/gcd and exact selected-root/order checks pass; native count schema valid')
