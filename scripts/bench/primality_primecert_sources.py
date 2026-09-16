#!/usr/bin/env python3
"""Translate selected Hex factors to supplied PrimeCert benchmark proofs.

This is offline, untrusted benchmark preparation, not Hex certificate search.
The direct-kernel runner builds and checks the emitted proofs with PrimeCert.
"""
from pathlib import Path
import argparse
import re, json, math
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('hex_record', type=Path)
parser.add_argument('output_dir', type=Path)
parser.add_argument('--no-sieve', action='store_true',
                    help='reproduce the earlier comparator using Pocklington for larger leaves')
parser.add_argument('--interval', action='store_true',
                    help='emit interval witnesses for PrimeCert #170 and later')
args = parser.parse_args()
record = json.loads(args.hex_record.read_text())
out = args.output_dir
out.mkdir(exist_ok=True, parents=True)
small_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
for case in record['cases']:
    row = next((r for r in record['rows'] if r['case'] == case['name'] and r['system'] == 'hex'))
    literal = row['source'].split('def certificate : Hex.Nat.PrimeCert :=', 1)[1].split('\ntheorem', 1)[0]
    tokens = re.findall('Hex\\.Nat\\.PrimeCert\\.(?:pock3Sieve|pock3|pock|small)|\\d+|[()\\[\\],]', literal)
    i = 0

    def take(t=None):
        global i
        a = tokens[i]
        i += 1
        if t is not None:
            assert a == t, (a, t, i)
        return a

    def parse():
        kind = take().split('.')[-1]
        n = int(take())
        node = dict(kind=kind, n=n, fs=[])
        if kind == 'small':
            return node
        if kind in ('pock3', 'pock3Sieve'):
            node['r'], node['s'], node['w'] = [int(take()) for _ in range(3)]
            node['m'] = int(take()) if kind == 'pock3Sieve' else 1
        take('[')
        while tokens[i] != ']':
            take('(')
            a = int(take())
            take(',')
            e = int(take()) + 1
            take(',')
            c = parse()
            take(')')
            node['fs'].append((a, e, c))
            if tokens[i] == ',':
                take(',')
            else:
                break
        take(']')
        return node
    root = parse()
    assert i == len(tokens), (case['name'], tokens[i:])
    nodes = {}
    small = set()
    sieved = set()
    steps = []

    def emit(node):
        n = node['n']
        if n in nodes:
            return
        nodes[n] = node
        if node['kind'] == 'small':
            if n <= 997:
                small.add(n)
                return
            assert n < 100000
            if not args.no_sieve:
                sieved.add(n)
                return
            residual = n - 1
            fs = []
            for q in range(2, math.isqrt(n - 1) + 1):
                e = 0
                while residual % q == 0:
                    e += 1
                    residual //= q
                if e:
                    fs.append((q, e))
            if residual > 1:
                fs.append((residual, 1))
            choices = [[f for i, f in enumerate(fs) if mask >> i & 1] for mask in range(1, 1 << len(fs))]
            chosen = min((f for f in choices if math.prod((q ** e for q, e in f)) ** 2 > n), key=lambda f: (len(f), sum((q > 997 for q, e in f)), f))
            node = dict(kind='pock', n=n, fs=[(0, e, dict(kind='small', n=q, fs=[])) for q, e in chosen])
            nodes[n] = node
        for _, _, c in node['fs']:
            emit(c)
        a = next((a for a in [2, *small_primes] if pow(a, n - 1, n) == 1 and all((math.gcd(pow(a, (n - 1) // c['n'], n) - 1, n) == 1 for _, _, c in node['fs']))))
        factors = ' * '.join((str(c['n']) + (f' ^ {e}' if e > 1 else '') for _, e, c in node['fs']))
        if node['kind'] == 'pock':
            steps.append(f'pock ({n}, {a}, {factors})')
        else:
            d = node['r'] ** 2 - 8 * node['s']
            if node['s'] == 0:
                mode = '0'
            elif d < 0:
                mode = '<'
            elif not args.interval:
                p = next((p for p in small_primes if pow(d % p, (p - 1) // 2, p) == p - 1))
                small.add(p)
                mode = str(p)
            else:
                mode = f"interval {node['w']}"
            steps.append(f'pock3 ({n}, {a}, {node["m"]}, {mode}, {factors})')
    emit(root)
    original = case['primecert']
    goal = re.search('theorem result : (.*?)\\s*:=\\s*prime_cert%', original, re.S)[1]
    ns = '.'.join(re.findall('^namespace (\\S+)', original, re.M))
    source = '/-\nCopyright (c) 2026 Lean FRO, LLC. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Kim Morrison\n-/\n\nmodule\npublic import PrimeCert\npublic section\nset_option maxRecDepth 65536\nset_option exponentiation.threshold 512\n'
    if sieved:
        source = source.replace('public import PrimeCert\n',
            'public import PrimeCert\npublic import PrimeCert.SieveBase\n'
            'public meta import PrimeCert.Meta.SieveLookup\n')
        steps.insert(0, 'sieve {' + '; '.join(map(str, sorted(sieved))) + '}')
    if ns:
        source += f'namespace {ns}\n'
    source += f'theorem result : {goal} := prime_cert%\n  [small {{' + '; '.join(map(str, sorted(small))) + '},\n   ' + ',\n   '.join(steps) + ']\n'
    if ns:
        source += f'end {ns}\n'
    (out / (case['name'] + '.lean')).write_text(source)
    print(case['name'], len(nodes), len(small), len(steps))
