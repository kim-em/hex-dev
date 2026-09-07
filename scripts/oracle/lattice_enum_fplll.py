#!/usr/bin/env python3
"""Informational, pinned fplll 5.5.0 SVP/CVP comparison against Hex exact minima.

Input JSONL comes from `hexlatticeenum_bench comparisons`. The C++ subprocess
uses proved search modes and checks the exact LLL prerequisites before search.
Rational CVP scales B and t by their target denominator q, then rescales norms
by q². Both lattice inclusions and candidate membership are checked exactly.
Timings exclude process startup, serialization and Python validation.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from math import lcm
from pathlib import Path
from statistics import median
import subprocess
import sys

from lattice_enum import left_inverse


def coordinates(b: list[list[int]], v: list[int]) -> list[Fraction]:
    left = left_inverse(b, len(v))
    return [sum(a*x for a, x in zip(row, v)) for row in left]


def compare(case: dict, binary: Path, repeats: int) -> dict:
    b = case['original_basis']
    n = len(b)
    if not 1 <= n <= 32 or any(len(row) != n for row in b):
        raise ValueError('comparator supports square independent bases of rank 1..32')
    op = case['operation']
    if op not in ('shortest', 'closest'):
        raise ValueError('unsupported operation')
    target = [Fraction(x) for x in case['target']]
    if len(target) != n or (op == 'shortest' and any(target)):
        raise ValueError('invalid target')
    q = lcm(*(x.denominator for x in target))
    scaled = [[q*x for x in row] for row in b]
    integer_target = [int(q*x) for x in target]
    request = ' '.join([op, str(n), *(str(x) for row in scaled for x in row),
                        *(str(x) for x in integer_target)]) + '\n'
    process = subprocess.run([str(binary)], input=request*(repeats+1), text=True,
                             capture_output=True, check=True, timeout=120)
    results = [json.loads(line) for line in process.stdout.splitlines()]
    if len(results) != repeats+1:
        raise ValueError('missing comparator responses')
    for result in results:
        if result['lll_status'] != 0 or result['search_status'] != 0:
            raise ValueError(f"fplll failed: {result}")
        reduced = [[int(x) for x in row] for row in result['basis']]
        # Both inclusions rule out a spurious sublattice or superlattice result.
        for source, dest in [(scaled, reduced), (reduced, scaled)]:
            for row in dest:
                if any(z.denominator != 1 for z in coordinates(source, row)):
                    raise ValueError('LLL changed the lattice')
        z = [int(x) for x in result['coefficients']]
        if len(z) != n:
            raise ValueError('wrong candidate rank')
        v = [sum(z[i]*reduced[i][j] for i in range(n)) for j in range(n)]
        if any(c.denominator != 1 for c in coordinates(scaled, v)):
            raise ValueError('candidate outside original lattice')
        if op == 'shortest' and not any(v):
            raise ValueError('zero SVP candidate')
        d = Fraction(sum((x-t)**2 for x,t in zip(v, integer_target)), q*q)
        if d != Fraction(case['distanceSq']):
            raise ValueError(f"minimum mismatch: {case['name']}: {d} != {case['distanceSq']}")
    samples = results[1:]
    return {'name': case['name'], 'operation': op, 'version': '5.5.0',
            'class': 'informational', 'method': samples[0]['method'],
            'lll_parameters': {'delta': '.999', 'eta': '.501', 'method': 'LM_WRAPPER'},
            'checked_prerequisite': {'delta': '99/100', 'eta': '51/100'},
            'lll_status': 0, 'search_status': 0, 'target_denominator': str(q),
            'distanceSq': str(Fraction(case['distanceSq'])), 'repeats': repeats,
            **{key: case[key] for key in ['hex_lll_ns', 'hex_preprocessed', 'hex_prepare_ns', 'hex_seed_ns', 'hex_search_ns']},
            **{key: median(r[key] for r in samples)
               for key in ['lll_ns', 'prerequisite_ns', 'search_ns']}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=5)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('--repeats must be positive')
    for line in sys.stdin:
        if line.strip():
            print(json.dumps(compare(json.loads(line), args.binary, args.repeats)), flush=True)

if __name__ == '__main__':
    main()
