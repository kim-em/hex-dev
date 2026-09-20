#!/usr/bin/env python3
"""Check retained primitive measurements against independent modular powers.

Repeated deterministic records are checked once, without discarding their
associated timing samples. The cap control uses gcd(2^a-1,2^b-1)=2^gcd(a,b)-1 to validate
a full miss without 252,557 redundant modular powers.
"""
import argparse
from functools import cache
import gzip
import json
from math import gcd, lcm
from pathlib import Path
import pminusone_stage2_fixtures as fixtures


@cache
def interval(lower, upper):
    return [p for p in fixtures.primes(upper) if p > lower]


def verify(row):
    command=row['command']
    n,x,b1,b2=map(int,command[2:6])
    result=row['result']
    if row['phase']=='prepared-stage1':
        exponent=lcm(*range(1,b1+1))
        assert x==pow(2,exponent,n)
        assert result['value']==gcd((x+n-1)%n,n)
        return
    if row['phase']=='preparation':
        checksum=0
        if n<2**64 and n%2:
            checksum=(-pow(n,-1,2**64))%(2**64)+(2**128)%n
        assert result['value']==2%n+gcd(2,n)+len(fixtures.primes(b1))+len(interval(b1,b2))+checksum
        return
    continuation=[e for e in result['events'] if e.get('effectiveB2') is not None]
    assert len(continuation)==1
    e=continuation[0]
    qs=interval(b1,b2)
    length=e['candidates']
    assert 0<=length<=len(qs)
    executed=qs[:length]
    advances=executed[-1]//210-executed[0]//210 if executed else 0
    initial=executed[0]//210 if executed else 0
    cost=(210+initial.bit_length()+initial.bit_count()+advances+2*length) if length else 0
    assert e['giantAdvances']==advances and e['multiplications']==cost
    assert e['batchGcds']==(length+31)//32
    assert e['setupGcds']==(0 if row['phase']=='prepared' else 2)
    assert result['attempts']==(2 if row['phase']=='total' else 1)
    assert result['rand']=='{ state := 0 }'
    if row.get('trace') is False:
        assert not e['batches']
        return
    assert len(e['batches'])==e['batchGcds']
    offset=0
    recovery_count=0
    for batch in e['batches']:
        ps=executed[offset:offset+batch['length']]
        assert ps and len(ps)<=32 and ps[0]==batch['first'] and ps[-1]==batch['last']
        if n==2**521-1:
            # gcd(2^p-1,2^521-1)=2^gcd(p,521)-1=1. This checks unit
            # terms without assuming that the Mersenne modulus is prime.
            assert x==2 and all(gcd(p,521)==1 for p in ps)
            assert batch['gcd']==1 and batch['recovery']==[]
        else:
            leaves=[(pow(x,p,n)-1)%n for p in ps]
            product=1
            for term in leaves:
                product=product*term%n
            assert gcd(product,n)==batch['gcd']
            recovery=[]
            if batch['gcd']==n:
                for term in leaves:
                    d=gcd(term,n)
                    recovery.append(d)
                    if 1<d<n:
                        break
            assert recovery==batch['recovery']
        offset+=len(ps)
        recovery_count+=len(batch['recovery'])
    assert offset==length and recovery_count==e['recoveryGcds']
    if result['outcome']=='factor':
        d=result['value']
        assert 1<d<n and n%d==0
    if result['outcome']=='noFactor':
        assert length==len(qs)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files',nargs='+',type=Path)
    args=parser.parse_args()
    seen=set()
    samples=0
    for path in args.files:
        raw=path.read_bytes()
        data=gzip.decompress(raw) if path.suffix=='.gz' else raw
        rows=[json.loads(l) for l in data.splitlines()]
        assert rows[-1]['type']=='complete',f'incomplete collection: {path}'
        for row in rows:
            if row['type']!='sample' or row.get('phase') not in (
                    'prepared','continuation','total','preparation','prepared-stage1'):
                continue
            samples+=1
            key=json.dumps([row['command'][:6],row['result']],sort_keys=True)
            if key not in seen:
                verify(row)
                seen.add(key)
    print(f'Checked {samples} retained samples, {len(seen)} distinct deterministic executions')

if __name__=='__main__':
    main()
