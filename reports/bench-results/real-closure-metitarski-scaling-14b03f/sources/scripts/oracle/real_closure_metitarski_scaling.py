#!/usr/bin/env python3
"""Exact FLINT checks for the native MetiTarski odd-degree ladder."""
from fractions import Fraction
from functools import cmp_to_key
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.real_algebraic_qqbar import QQBar
# CADE2013 section4; the existing real_closure_phase4_inputs.py independently
# verifies this transcription against paper SHA4caf5244...d7a19.
COEFFICIENTS = [592704,402192,90972,3266731,-931392,-193914,-5792221,
                756756,140742,3046158,-259308,-42336,-520884,31752,4536,216]

DEGREES = (3,5,7,9)


def require(test, message):
    if not test:
        raise ValueError(message)


def check(row):
    degree = row.get('degree')
    require(row.get('schema') == 1 and row.get('workload') == 'metitarski-degree-ladder'
            and type(degree) is int and degree in DEGREES, 'wrong scaling input')
    require(row.get('first_coefficients') == [[c,1] for c in COEFFICIENTS],
            'wrong degree15 predecessor')
    require(row.get('root_count') == 1 and type(row.get('root_count')) is int
            and row.get('multiplicity') == 1 and type(row.get('multiplicity')) is int
            and row.get('equation_sign') == 0 and type(row.get('equation_sign')) is int
            and row.get('first_replay') is True and row.get('root_replay') is True,
            'native functional checks failed')
    with QQBar() as q:
        zero, one = q.number(0), q.number(1)
        add = lambda a,b: q.binary('add',a,b)
        mul = lambda a,b: q.binary('mul',a,b)
        sign = lambda a: (q.compare(a,zero)>0) - (q.compare(a,zero)<0)
        def evaluate(poly,x):
            value = zero
            for c in reversed(poly):
                value = add(c,mul(value,x))
            return value
        def rational(raw):
            require(isinstance(raw,list) and len(raw) == 3 and raw[0] == 0
                    and all(type(i) is int for i in raw) and raw[2] > 0,
                    'invalid base rational')
            value = Fraction(raw[1],raw[2])
            require(raw == [0,value.numerator,value.denominator], 'noncanonical rational')
            return q.number(value)
        first_roots = q.roots([q.number(c,q.integer) for c in COEFFICIENTS], integer=True)
        first_roots.sort(key=cmp_to_key(lambda a,b: q.compare(a[0],b[0])))
        require(len(first_roots) == 3 and all(m == 1 for _,m in first_roots),
                'wrong predecessor roots')
        alpha = first_roots[0][0]
        require(q.compare(q.number(Fraction(-1875,2048)),alpha) < 0
                and q.compare(alpha,q.number(Fraction(-1875,4096))) < 0,
                'wrong least-root interval')
        def coordinate(raw):
            require(isinstance(raw,list), 'invalid algebraic coordinate')
            if raw == []:
                return zero
            require(len(raw) == 2 and isinstance(raw[0],list) and type(raw[1]) is int,
                    'invalid stored algebraic value')
            value = evaluate([rational(c) for c in raw[0]],alpha)
            require(raw[1] == sign(value) and raw[1] != 0, 'wrong cached coefficient sign')
            return value
        constant = add(mul(mul(alpha,alpha),alpha),one)
        require(sign(constant) == 1, 'expected positive odd-root constant')
        positive = q.to_real(q.nth_root(constant,degree))
        require(positive is not None, 'positive principal root is nonreal')
        beta = q.unary('neg',positive)
        expected = [constant] + [zero]*(degree-1) + [one]
        def equal_poly(a,b):
            return len(a) == len(b) and all(q.compare(x,y) == 0 for x,y in zip(a,b))
        head = [coordinate(c) for c in row['head']]
        require(equal_poly(head,expected),
                'wrong exact second polynomial')
        def descriptor(raw,convert,roots,expected_head,derivative_sign=None):
            require(isinstance(raw,list) and len(raw) == 7, 'wrong descriptor shape')
            polynomial = [convert(c) for c in raw[1]]
            require(equal_poly(polynomial,expected_head), 'wrong descriptor polynomial')
            def within(root,bound,lower):
                require(isinstance(bound,list), 'invalid endpoint')
                if bound == [0]: return lower
                if bound == [2]: return not lower
                require(len(bound) == 2 and bound[0] == 1, 'invalid finite endpoint')
                order = q.compare(convert(bound[1]),root)
                return order < 0 if lower else order > 0
            indices, signs = raw[4],raw[5]
            require(isinstance(indices,list) and all(type(i) is int for i in indices)
                    and indices == sorted(set(indices)) and all(0 < i < len(polynomial) for i in indices)
                    and isinstance(signs,list) and len(indices) == len(signs)
                    and all(type(s) is int and s in (-1,0,1) for s in signs), 'wrong Thom word')
            derivatives, current = [],polynomial
            while len(current)>1:
                current = [mul(q.number(i),current[i]) for i in range(1,len(current))]
                derivatives.append(current)
            hits = [r for r in roots if within(r,raw[2],True) and within(r,raw[3],False)
                    and all((derivative_sign(i) if derivative_sign else
                             sign(evaluate(derivatives[i-1],r))) == s for i,s in zip(indices,signs))]
            require(len(hits) == 1, 'descriptor does not select a unique root')
            return hits[0]
        require(row['first'][0] == [0], 'wrong predecessor context binding')
        first = descriptor(row['first'],rational,[r for r,_ in first_roots],
                           [q.number(Fraction(c,COEFFICIENTS[-1])) for c in COEFFICIENTS])
        require(q.compare(first,alpha) == 0, 'descriptor changes predecessor embedding')
        # Y^n+c has exactly one real root for odd n, and the nonzero derivative
        # n*beta^(n-1) makes its multiplicity one. FLINT constructs that root.
        require(row['root'][0] == [0], 'wrong second context binding')
        root = descriptor(row['root'],coordinate,[beta],expected,
                          lambda i: 1 if (degree-i)%2 == 0 else -1)
        require(q.compare(root,beta) == 0, 'descriptor changes second root')
        # c>0 gives beta<0, so n*beta^(n-1) is positive for odd n.
        # The exact radical constructor already gives beta^n=-c; avoid
        # repeating global minimal-polynomial arithmetic for its powers.
        require(sign(beta) == -1, 'second radical is not negative')
    return dict(oracle='FLINT qqbar',degree=degree,real_roots=1,multiplicity=1,
                head_bytes=len(json.dumps(row['head'],separators=(',',':')).encode()),
                descriptor_bytes=len(json.dumps(row['root'],separators=(',',':')).encode()))


if __name__ == '__main__':
    rows = Path(sys.argv[1]).read_text().splitlines() if len(sys.argv) == 2 else sys.stdin
    rows = [json.loads(line) for line in rows if line.strip()]
    require(len(rows) in (1,4), 'incomplete functional input inventory')
    if len(rows) == 4:
        require([r.get('degree') for r in rows] == list(DEGREES), 'wrong functional degree schedule')
    for row in rows:
        print(json.dumps(check(row),sort_keys=True))
