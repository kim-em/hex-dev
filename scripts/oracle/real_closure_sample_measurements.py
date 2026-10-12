#!/usr/bin/env python3
"""Exact Z3 RCF and FLINT checks of matched positive quadratic sample gaps."""
from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import flint
from scripts.oracle.real_closure_samples import Reader
from scripts.oracle.real_closure_isolation import parse_record, sign
from scripts.oracle.sign_det_common import require
from scripts.oracle.sign_det_z3 import check_version

GAPS = (0, 4, 8, 12)
METHODS = ('midpoint', 'dyadic', 'infinitesimal')
FIELDS = {'gap', 'method', 'polynomials', 'context', 'value', 'signs', 'value_sign', 'dyadic_cuts'}


def dyadic(gap):
    lower, upper = flint.fmpq(1), flint.fmpq(2)
    threshold = flint.fmpq(2) + flint.fmpq(1, 2**gap)
    for cuts in range(1, 513):
        middle = (lower + upper) / 2
        above, below = middle**2 > 2, middle**2 < threshold
        if above and below:
            return middle, cuts
        if above:
            upper = middle
        else:
            lower = middle
    raise ValueError('independent dyadic search exhausted its bound')


def verify(rows):
    check_version()
    require(flint.__version__ == '0.9.0', 'expected python-flint0.9.0')
    require([(row.get('gap'), row.get('method')) for row in rows] ==
            [(gap, method) for gap in GAPS for method in METHODS],
            'missing, reordered or duplicate sample arm')
    results = []
    for row in rows:
        require(set(row) == FIELDS, 'malformed sample measurement record')
        require(type(row['value_sign']) is int and type(row['signs']) is list and
                all(type(value) is int for value in row['signs']), 'noninteger sample signs')
        gap, method = row['gap'], row['method']
        require(type(gap) is int and type(row['dyadic_cuts']) is int,
                'noninteger sample parameters')
        depth = int(method == 'infinitesimal')
        reader = Reader(depth)
        r = reader.rcf
        original = row['polynomials']
        expected = [[[0, -2, 1], [0, 0, 1], [0, 1, 1]],
                    [[0, -(2 * 2**gap + 1), 2**gap], [0, 0, 1], [0, 1, 1]]]
        # gap zero's second rational is already reduced; all other inputs
        # have odd numerator and power-of-two denominator.
        require(original == expected, 'changed original sample polynomial')
        roots = reader.context(row['context'])
        require(len(roots) == {'midpoint': 2, 'dyadic': 0, 'infinitesimal': 1}[method],
                'sample retained unrelated algebraic owners')
        point = reader.value(row['value'], roots)
        polynomials = [[reader.base(c, 0) for c in p] for p in original]
        observed = [sign(r.eval(p, point)) for p in polynomials]
        require(observed == [1, -1] and row['signs'] == observed,
                'sample did not preserve the original sign condition')
        require(sign(point) == 1 and row['value_sign'] == 1,
                'sample selected the negative sector')
        if method == 'midpoint':
            require(roots[0] > 0 and roots[0]**2 == 2 * r.one and
                    roots[1] > roots[0] and r.eval(polynomials[1], roots[1]) == 0,
                    'midpoint changed its positive boundary roots')
            require(point == (roots[0] + roots[1]).__div__(2 * r.one),
                    'sample is not the original midpoint')
        elif method == 'infinitesimal':
            require(roots[0] > 0 and roots[0]**2 == 2 * r.one,
                    'infinitesimal sample changed its retained lower root')
            require(point == roots[0] + r.levels[0],
                    'sample is not the retained lower root plus the new infinitesimal')
        else:
            expected_point, cuts = dyadic(gap)
            require(point == r.coeff([int(expected_point.numerator), int(expected_point.denominator)], 0)
                    and row['dyadic_cuts'] == cuts, 'dyadic point or cut count changed')
        if method != 'dyadic':
            require(row['dyadic_cuts'] == 0, 'non-dyadic arm claimed cut work')
        compact = lambda value: json.dumps(value, separators=(',', ':')).encode()
        results.append(dict(gap=gap, method=method, signs=observed,
                            dyadic_cuts=row['dyadic_cuts'],
                            base_depth=depth, algebraic_depth=len(roots),
                            value_bytes=len(compact(row['value'])),
                            context_bytes=len(compact(row['context']))))
    return results


if __name__ == '__main__':
    rows = [parse_record(line) for line in Path(sys.argv[1]).read_text().splitlines() if line.strip()]
    results = verify(rows)
    print(json.dumps({'verified_arms': len(results), 'python_flint_version': flint.__version__,
                      'results': results}, indent=2))
