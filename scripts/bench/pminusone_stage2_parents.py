#!/usr/bin/env python3
"""Exact prime parents for construction measurements of the small stage-2 family.

N = 2*k*(p*r)+1 makes the committed semiprime a predecessor obligation.
The two prime factors p,r have product F with F^2>N; separate Pocklington
witnesses for both certify N. No claimed primality relies on a probable test.
"""
import argparse
import json
from math import gcd
import pminusone_stage2_fixtures as f

PATH = f.ROOT / 'conformance-fixtures/HexPrimality/pminusone-stage2-parents.jsonl'
LEAN = f.ROOT / 'bench/HexPrimality/PMinusOneParents.lean'


def witness(n, q):
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if pow(a,n-1,n) != 1:
            return None
        if gcd(pow(a,(n-1)//q,n)-1,n)==1:
            return a
    return None


def generate(inputs):
    result=[]
    for index,row in enumerate(inputs):
        for k in range(1,100000):
            n=2*k*row['n']+1
            if any(n%p==0 for p in f.SMALL):
                continue
            wp=witness(n,row['p'])
            if wp is None:
                continue
            wr=witness(n,row['r'])
            if wr is not None:
                result.append({'index':index,'bits':row['bits'],'q':row['q'],
                               'n':n,'k':k,'wp':wp,'wr':wr})
                break
        else:
            raise RuntimeError('parent search exhausted')
    return result


def verify(rows, inputs):
    assert len(rows)==len(inputs)==40
    for index,(row,i) in enumerate(zip(rows,inputs)):
        assert row['index']==index and (row['bits'],row['q'])==(i['bits'],i['q'])
        n=row['n']
        assert n==2*row['k']*i['n']+1 and i['n']**2>n
        for name,q in [('wp',i['p']),('wr',i['r'])]:
            a=row[name]
            assert pow(a,n-1,n)==1 and gcd(pow(a,(n-1)//q,n)-1,n)==1


def render(rows):
    values=',\n'.join(f"  ({r['n']}, parent {r['n']} {r['wp']} {r['wr']} inputs[{r['index']}]!)" for r in rows)
    return '''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.PMinusOneFixtures

/-! Generated exact prime parents for the shared construction family. -/
namespace Hex.PrimalityBench.Stage2
open Hex.Nat

def parent (n wp wr : Nat) (i : Input) : PrimeCert :=
  .pock n (if i.p < i.r then [(wp, 0, i.certP), (wr, 0, i.certR)]
    else [(wr, 0, i.certR), (wp, 0, i.certP)])

def parents : Array (Nat × PrimeCert) := #[
'''+values+''']

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
#guard parents.all fun (n,c) => c.subject == n && checkPrime c

end Hex.PrimalityBench.Stage2
'''


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    inputs=[json.loads(l) for l in f.FIXTURES.read_text().splitlines()]
    f.verify(inputs)
    inputs=[r for r in inputs if r['family']=='primitive']
    rows=generate(inputs) if args.write else [json.loads(l) for l in PATH.read_text().splitlines()]
    verify(rows,inputs)
    if args.write:
        PATH.write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
        LEAN.write_text(render(rows))
    else:
        assert LEAN.read_text()==render(rows)
    print(f'Verified {len(rows)} prime parents')

if __name__=='__main__':
    main()
