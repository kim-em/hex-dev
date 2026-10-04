#!/usr/bin/env python3
"""Independently validate mixed arithmetic, prime bases and ECPP transcripts."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/oracle'))
from ecpp_pari import check_step, pari_group_check, pari_isprime

STEP = re.compile(r'Hex\.ECPP\.Cert\.step\s+' + r'\s+'.join([r'(\d+)']*6) + r'\s+\[([\d,\s]*)\]')
PRIME = re.compile(r'Hex\.Nat\.PrimeCert\.(?:small|pock3Sieve|pock3|pock)\s+(\d+)')
POWER = re.compile(r'⟨(\d+), (\d+), \(Hex\.Nat\.Mixed\.Evidence\.(legacy|ecpp)')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('preserve completed observations')
    plan = json.loads((ROOT / 'reports/intfactor/mixed/acceptance-v1.json').read_text())
    report = dict(oracle='Python exact arithmetic and affine replay; PARI isprime and ellmul', cases=[])
    primes = {}
    for case in plan['cases']:
        file = {'a':'CaseA', 'b':'CaseB', 'partial':'Partial'}[case['id']]
        source = (ROOT / f'HexIntFactor/Mixed/Frozen/{file}.lean').read_text()
        subject = int(re.search(r'\n  ⟨(\d+), \[', source)[1])
        factors = [(int(p), int(e), kind) for p, e, kind in POWER.findall(source)]
        residual = 1 if case['expected'] == 'complete' else int(re.search(r'\], (\d+)⟩', source)[1])
        assert subject == case['subject']
        assert factors == sorted(factors) and len(set(p for p, _, _ in factors)) == len(factors)
        assert all(p >= 2 and e > 0 for p, e, _ in factors)
        assert math.prod(p**e for p, e, _ in factors) * residual == subject
        terminal = list(map(int, PRIME.findall(source)))
        matches = list(STEP.finditer(source))
        rows = []
        for i, match in enumerate(matches):
            fields = dict(zip('n a b x y d'.split(), map(int, match.groups()[:6])))
            child = int(matches[i+1].group(1)) if i+1 < len(matches) else int(PRIME.search(source, match.end())[1])
            fields.update(kind='step', q=child, witnesses=json.loads('['+match.group(7)+']'), accepted=True)
            assert check_step(fields), (case['id'], i)
            rows.append(fields)
        for n in set(terminal + [p for p, _, _ in factors] + [r['n'] for r in rows]):
            if n not in primes:
                primes[n] = pari_isprime(n)
            assert primes[n], n
        pari_group_check(rows)
        entry = dict(case=case['id'], source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                     subject=str(subject), factors=[[str(p), e, k] for p, e, k in factors],
                     residual=str(residual), steps=len(rows), checked_prime_subjects=[str(n) for n in sorted(primes)])
        report['cases'].append(entry)
        args.output.write_text(json.dumps(report, indent=2)+'\n')
        print(case['id'], 'arithmetic, primality and', len(rows), 'elliptic rows passed', flush=True)


if __name__ == '__main__':
    main()
