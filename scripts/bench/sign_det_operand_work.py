#!/usr/bin/env python3
"""Independent fixed-family checks for rational joint and interacting-field traces.

Counts and operand maxima are observations, not independently derived counts.
"""
import json
import math
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.sign_det_z3 import RCF, check_version


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer_subject(value):
    if type(value) is int:
        return True
    if isinstance(value, list):
        return all(integer_subject(c) for c in value)
    if isinstance(value, dict):
        return all(integer_subject(c) for c in value.values())
    return False


def coefficient_size(value):
    if isinstance(value, list):
        return max(abs(value[0]).bit_length(), value[1].bit_length()), 1
    parts = [coefficient_size(c) for c in value['num']+value['den']]
    return max([1]+[p[0] for p in parts]), sum(p[1] for p in parts)


def counters(row, bits, slots=None):
    calls = row['operationCalls']
    require(isinstance(calls, list) and len(calls) == 8 and
            all(type(c) is int and c >= 0 for c in calls), 'invalid operation counts')
    require(type(row['coefficientCalls']) is int and row['coefficientCalls'] > 0 and
            sum(calls) == row['coefficientCalls'], 'inconsistent operation total')
    require(type(row[bits]) is int and row[bits] > 0, 'invalid bit maximum')
    if slots:
        require(type(row[slots]) is int and row[slots] > 0, 'invalid coordinate maximum')


def validate_joint(path):
    from flint import fmpq, fmpq_poly
    rows = [json.loads(s) for s in Path(path).read_text().splitlines()]
    require([r['result']['degree'] for r in rows] == [3, 7, 15], 'wrong degree schedule')
    def polynomial(cs):
        require(isinstance(cs, list) and all(isinstance(c, list) and len(c) == 2 and
                all(type(z) is int for z in c) and c[1] > 0 for c in cs), 'invalid coefficient')
        return fmpq_poly([fmpq(a,b) for a,b in cs])
    for row in rows:
        counters(row, 'maxNormalizedBits')
        r = row['result']; n = r['degree']
        require(all(integer_subject(r[k]) for k in
                    ('degree','context','leftSigns','rightSigns')), 'invalid integer subject')
        require(type(n) is int and r['context'] == 10377+n, 'wrong context')
        x = fmpq_poly([0,1])
        p,q,f,h = [polynomial(r[k]) for k in ('left','right','factor','commonHead')]
        require(p == x**n-1 and q == x**n+1 and f == -2 and
                h == (1-x**(2*n))/2 and h*f == p*q, 'wrong joint subjects')
        require(p.gcd(q) == f/f[f.degree()] and p(1)==0 and q(-1)==0,
                'wrong common factor or selected roots')
        left=[]; right=[]; derivative=h
        for _ in range(2*n):
            derivative=derivative.derivative()
            left.append((derivative(1)>0)-(derivative(1)<0))
            right.append((derivative(-1)>0)-(derivative(-1)<0))
        require(r['leftSigns'] == left and r['rightSigns'] == right,
                'wrong derivative identities at roots 1 and -1')
        require(r['order'] == 'gt' and r['standardReplayAccepted'] is True, 'wrong root order')
        require(row['maxNormalizedBits'] >= (math.factorial(2*n)//2).bit_length(),
                'maximum omits the highest common-head derivative')
        require(type(row['temporaryBitBound']) is int and
                row['temporaryBitBound'] == 2*row['maxNormalizedBits']+1, 'wrong derived bound')
    return rows


def validate_interacting(path):
    check_version()
    rows = [json.loads(s) for s in Path(path).read_text().splitlines()]
    require([(r['result']['depth'], r['result']['mode']) for r in rows] ==
            [(d,m) for d in (1,2,3) for m in ('reduced','direct','reference')], 'wrong depth/arm schedule')
    for row in rows:
        counters(row, 'maxNormalizedRatBits', 'maxRationalSlots')
        r = row['result']; depth = r['depth']
        require(all(integer_subject(r[k]) for k in
                    ('depth','queries','context','generator','anchor','head','queryPolynomials','entries')),
                'invalid integer subject')
        require(type(depth) is int and r['queries'] == 2 and r['context'] == 10377+10*depth+2,
                'wrong literal context')
        # Native context binding is checked above; the existing oracle uses
        # its own fixed identifier for the same ordered infinitesimal field.
        oracle = RCF({'id':10377, 'levels':[f'epsilon{i+1}' for i in range(depth)],
                      'order':'each-new-level-smaller-than-positive-base-elements'}, maximum_depth=3)
        g = oracle.levels[0] - oracle.levels[0]*oracle.levels[0]
        a = oracle.levels[0]
        for e in oracle.levels[1:]:
            a,g = g,g-e
        require(oracle.coeff(r['generator']) == g and oracle.coeff(r['anchor']) == a,
                'wrong interacting coefficients')
        require(oracle.poly(r['head']) == [-g*g,oracle.zero,oracle.one] and
                [oracle.poly(q) for q in r['queryPolynomials']] == [[-g,oracle.one],[-a,oracle.one]],
                'wrong polynomial/query subjects')
        require(r['lower'] == 'negInf' and r['upper'] == 'posInf', 'wrong interval')
        expected = oracle.table({'head':r['head'], 'queries':r['queryPolynomials'],
                                 'lower':'-inf', 'upper':'+inf'})
        require(expected is not None and r['entries'] == [[t['signs'],t['count']] for t in expected],
                'wrong complete root/sign table')
        require(r['standardReplayAccepted'] is True, 'ordinary replay failed')
        sizes = [coefficient_size(c) for c in
                 [r['generator'],r['anchor'],*r['head'],
                  *[c for q in r['queryPolynomials'] for c in q]]]
        require(row['maxNormalizedRatBits'] >= max(s[0] for s in sizes) and
                row['maxRationalSlots'] >= max(s[1] for s in sizes),
                'maximum omits an observed input operand')
    return rows


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ('joint','interacting'):
        raise SystemExit('usage: sign_det_operand_work.py joint|interacting observations.jsonl')
    f = validate_joint if sys.argv[1] == 'joint' else validate_interacting
    print(f'{len(f(sys.argv[2]))} actual subject/root/order checks pass')
