#!/usr/bin/env python3
"""Independent exact conformance; requires python-flint, takes JSONL on stdin."""
import json
import sys
from fractions import Fraction as Q
from flint import fmpq_poly, fmpq

MIN = fmpq_poly([-2, 0, 1])
DEF = MIN * fmpq_poly([-3, 0, 1])
ZERO = (Q(0), Q(0))
ONE = (Q(1), Q(0))

def poly(xs):
    return fmpq_poly([fmpq(x) for x in xs])

def value(xs):
    r = poly(xs) % MIN
    return Q(str(r[0])), Q(str(r[1]))

def add(a, b):
    return a[0]+b[0], a[1]+b[1]

def neg(a):
    return -a[0], -a[1]

def mul(a, b):
    return a[0]*b[0]+2*a[1]*b[1], a[0]*b[1]+a[1]*b[0]

def inv(a):
    den = a[0]**2-2*a[1]**2
    return (a[0]/den, -a[1]/den) if den else ZERO

def trim(a):
    while a and a[-1] == ZERO:
        a.pop()
    return a

def padd(a, b):
    return trim([add(a[i] if i < len(a) else ZERO, b[i] if i < len(b) else ZERO)
                 for i in range(max(len(a),len(b)))])

def pmul(a, b):
    out = [ZERO] * max(0, len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = add(out[i+j], mul(x,y))
    return trim(out)

def pdiv(a, b):
    a = a.copy()
    if not b:
        return [], a
    q = [ZERO] * max(0,len(a)-len(b)+1)
    while a and len(a) >= len(b):
        k = len(a)-len(b)
        c = mul(a[-1], inv(b[-1]))
        q[k] = c
        a = padd(a, [ZERO]*k + [neg(mul(c,x)) for x in b])
    return trim(q), a

def monic(a):
    return [mul(x,inv(a[-1])) for x in a] if a else []

def gcd(a,b):
    while b:
        a,b = b,pdiv(a,b)[1]
    return monic(a)

def sign(a):
    # Independent method: exact rational bisection enclosing sqrt(2), not the
    # squared-magnitude sign formula used by the Lean implementation.
    x,y = a
    if a == ZERO: return 0
    lo,hi=Q(1),Q(2)
    while True:
        endpoints=[x+y*lo,x+y*hi]
        if min(endpoints)>0: return 1
        if max(endpoints)<0: return -1
        mid=(lo+hi)/2
        if mid*mid<2: lo=mid
        else: hi=mid

counts = dict(scalar=0,poly=0,cost=0)
for line in sys.stdin:
    row = json.loads(line)
    kind = row['kind']
    counts[kind] += 1
    if kind == 'scalar':
        q = poly(row['q'])
        v = value(row['q'])
        assert row['zero'] == (v == ZERO), row
        assert value(row['inverse']) == inv(v), row
        assert row['sign'] == sign(v), row
        if v != ZERO:
            h,g = poly(row['factor']),poly(row['discarded'])
            assert g == q.gcd(DEF), row
            assert h*g == DEF and h % MIN == 0 and g.gcd(MIN).degree() == 0, row
            assert q.gcd(h).degree() == 0, row
            assert (q*poly(row['inverse'])) % h == 1, row
            assert row['split'] == (g.degree() > 0), row
    elif kind == 'poly':
        r = {k: trim([value(x) for x in v]) for k,v in row.items() if k != 'kind'}
        assert pdiv(r['a'],r['b']) == (r['quot'],r['rem']), row
        assert gcd(r['a'],r['b']) == r['gcd'] == monic(r['xgcd']), row
        assert padd(pmul(r['left'],r['a']),pmul(r['right'],r['b'])) == r['xgcd'], row
        assert pmul(r['a'],r['b']) == r['mul'] == r['batch'], row
    else:
        n=row['n']
        assert row['each'][0] == 2*n*n and row['batch'][0] == 2*n-1, row
        if row['shared']:
            assert row['each'][2] > 0 and row['batch'][2] > 0, row
assert counts == dict(scalar=48,poly=17,cost=6), counts
print(json.dumps({'passed':counts,'oracle':'python-flint + exact quadratic-pair arithmetic'},indent=2))
