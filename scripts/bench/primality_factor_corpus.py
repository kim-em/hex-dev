#!/usr/bin/env python3
"""Freeze independent prime subjects before any factor-policy measurement.

Hash-derived odd candidates are tested by rejection sampling, not by rounding
up to the next prime. PARI's unconditional isprime verifies each accepted
subject. Neither predecessor factors nor search results select a subject.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

DOMAIN = 'hex-pocklington-corpus/v1'


def candidate(bits, index, counter, domain=DOMAIN):
    material = f'{domain}/{bits}/{index}/{counter}'
    n = int.from_bytes(hashlib.shake_256(material.encode()).digest((bits + 7) // 8), 'big')
    return (n & ((1 << bits) - 1)) | (1 << (bits - 1)) | 1


def composite_witness(n, a):
    """A failed strong probable-prime test is an exact compositeness witness."""
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(a, d, n)
    if x in [1, n - 1]:
        return False
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return False
    return True


def validate(report):
    """Check the frozen subjects, identities and split without running a search."""
    assert report['schema'] in [DOMAIN, 'hex-pocklington-corpus/v2'] and report['complete'] is True
    count = report['count_per_size']
    assert isinstance(count, int) and count >= 4
    expected = {(bits, i) for bits in [128, 256, 384, 512] for i in range(count)}
    assert len(report['cases']) == len(expected)
    seen = set()
    for case in report['cases']:
        bits, index, counter = case['bits'], case['index'], case['counter']
        assert (bits, index) in expected and (bits, index) not in seen
        seen.add((bits, index))
        assert isinstance(counter, int) and counter >= 0
        split = 'tuning' if index < count // 4 else 'validation'
        assert case['split'] == split and case['id'] == f'{split}-{bits}-{index}'
        assert case['subject'] == candidate(bits, index, counter, report['schema'])
        assert case['pari_isprime'] is True
        bases = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
        assert not any(composite_witness(case['subject'], a) for a in bases)
        # A recorded counter cannot skip an earlier prime to improve a policy's
        # coverage: every preceding candidate must have an exact witness.
        for k in range(counter):
            n = candidate(bits, index, k, report['schema'])
            assert any(composite_witness(n, a) for a in bases)
    assert len({x['subject'] for x in report['cases']}) == len(expected)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path)
    p.add_argument('--check', type=Path, help='check identities and split of an existing corpus')
    p.add_argument('--gp', default=shutil.which('gp'))
    p.add_argument('--domain', choices=[DOMAIN, 'hex-pocklington-corpus/v2'], default=DOMAIN)
    p.add_argument('--count', type=int, default=100, help='subjects per bit size')
    args = p.parse_args()
    if args.check:
        validate(json.loads(args.check.read_text()))
        print('Frozen corpus identities and split checked')
        return
    if not args.output:
        p.error('--output is required for generation')
    if not args.gp or args.count < 4 or args.output.exists():
        p.error('require GP, count >= 4 and a new output path')
    version = subprocess.check_output([args.gp, '--version'], stderr=subprocess.STDOUT, text=True)
    report = {'schema': args.domain, 'generator_source': Path(__file__).read_text(),
              'gp_version': version.strip(), 'count_per_size': args.count,
              'generation': 'SHAKE256/domain/bits/index/counter; mask to exact bits; set top and odd bits; '
                            'first passing ispseudoprime candidate, verified with unconditional isprime',
              'split': 'first floor(count/4) indices per size tuning; remaining validation',
              'cases': [], 'complete': False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    seen = set()
    for bits in [128, 256, 384, 512]:
        for index in range(args.count):
            counter = 0
            while True:
                ns = [candidate(bits, index, k, args.domain) for k in range(counter, counter + 64)]
                code = f'V={ns};print(select(i->ispseudoprime(V[i]),vector(#V,i,i)));quit\n'
                r = subprocess.run([args.gp, '-q', '-f'], input=code, capture_output=True,
                                   text=True, check=True)
                if r.stderr:
                    raise RuntimeError(r.stderr)
                selected = json.loads(r.stdout)
                if selected:
                    counter += selected[0] - 1
                    n = candidate(bits, index, counter, args.domain)
                    proof = subprocess.run([args.gp, '-q', '-f'], input=f'print(isprime({n}));quit\n',
                                           text=True, capture_output=True, check=True)
                    if proof.stderr or proof.stdout.strip() != '1':
                        raise RuntimeError(f'PARI did not prove candidate {n}: {proof}')
                    assert n not in seen and n.bit_length() == bits
                    seen.add(n)
                    split = 'tuning' if index < args.count // 4 else 'validation'
                    report['cases'].append({'id': f'{split}-{bits}-{index}', 'split': split,
                                            'bits': bits, 'index': index, 'counter': counter,
                                            'subject': n, 'pari_isprime': True})
                    args.output.write_text(json.dumps(report, indent=2) + '\n')
                    print(bits, index, counter, flush=True)
                    break
                counter += 64
    report['complete'] = True
    validate(report)
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
