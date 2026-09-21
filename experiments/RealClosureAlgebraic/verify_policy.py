#!/usr/bin/env python3
"""Independent quotient-field arithmetic via FLINT; no reuse of Lean sign/gcd code."""
import argparse
import json
from pathlib import Path
from flint import fmpq_poly, fmpq

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--results',type=Path,default=HERE/'results'/'policy')
OUT=parser.parse_args().results
MIN=fmpq_poly([-2,0,0,0,1])
X=fmpq_poly([0,1])
ZERO=fmpq_poly([])
ONE=fmpq_poly([1])
assert MIN.factor()[1] == [(MIN,1)]  # Eisenstein at 2; also checked by FLINT.
assert fmpq_poly([-2,0,1]).factor()[1] == [(fmpq_poly([-2,0,1]),1)]

def base(xs):
    return fmpq_poly([fmpq(xs[0]) if xs else 0,0,fmpq(xs[1]) if len(xs)>1 else 0])
def upper(xs):
    return ((base(xs[0]) if xs else ZERO)+X*(base(xs[1]) if len(xs)>1 else ZERO))%MIN

def trim(a):
    while a and a[-1]==ZERO: a.pop()
    return a

def inv(a):
    if a==ZERO: return ZERO
    g,s,_=a.xgcd(MIN)
    assert g==ONE
    return s%MIN

def add(a,b):
    return trim([((a[i] if i<len(a) else ZERO)+(b[i] if i<len(b) else ZERO))%MIN
                 for i in range(max(len(a),len(b)))])

def mul(a,b):
    out=[ZERO for _ in range(max(0,len(a)+len(b)-1))]
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]=(out[i+j]+x*y)%MIN
    return trim(out)

def divmod_poly(a,b):
    a=a.copy()
    if not b: return [],a
    q=[ZERO for _ in range(max(0,len(a)-len(b)+1))]
    while a and len(a)>=len(b):
        k=len(a)-len(b); c=(a[-1]*inv(b[-1]))%MIN
        q[k]=c
        a=add(a,[ZERO]*k+[-(c*x)%MIN for x in b])
    return trim(q),a

def monic(a):
    return [(x*inv(a[-1]))%MIN for x in a] if a else []
def gcd(a,b):
    while b: a,b=b,divmod_poly(a,b)[1]
    return monic(a)

rows=list(map(json.loads,(OUT/'checks.jsonl').read_text().splitlines()))
counts={'base':0,'nested':0,'growth':0}
for row in rows:
    kind=row['kind']; counts[kind]+=1
    if kind=='growth':
        assert base(row['value']) == pow(X,2*(2**row['step']))%MIN
        if row['mode']!=0: assert row['storedDegree'] < (4 if row['mode']==1 else 2)
        continue
    decode=base if kind=='base' else upper
    r={k:trim([decode(v) for v in row[k]]) for k in ['a','b','q','r','g']}
    assert divmod_poly(r['a'],r['b']) == (r['q'],r['r']),row
    assert gcd(r['a'],r['b']) == r['g'],row
    assert add(mul(r['q'],r['b']),r['r']) == r['a'],row
assert counts=={'base':12,'nested':8,'growth':28},counts
transport=list(map(json.loads,(OUT/'refinement.jsonl').read_text().splitlines()))
expected=[X,X*X,X+X*X,X*X*X,inv(X+X*X)]
assert len(transport)==len(expected)
for row,value in zip(transport,expected):
    assert upper(row['before'])==upper(row['after'])==value
    assert row['oldStillValid'] and row['staleRejected']
print(json.dumps({'passed':counts,'transport_values':len(transport),
                  'oracle':'FLINT Q[X]/(X^4-2), exact polynomial long division'},indent=2))
