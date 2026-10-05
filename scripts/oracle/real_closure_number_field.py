#!/usr/bin/env python3
"""Exact FLINT root/multiplicity/sign checks over the selected cubic field."""
from fractions import Fraction
from functools import cmp_to_key
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.real_algebraic_qqbar import QQBar

CASES = {'cubic-field zero', 'cubic-field repeated roots', 'cubic-field nonmonic roots', 'middle cubic embedding'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check(rows):
    require(len(rows) == 4 and {r.get('case') for r in rows} == CASES, 'missing or duplicate case')
    with QQBar() as q:
        zero, one, two = [q.number(i) for i in (0, 1, 2)]
        neg = lambda x: q.unary('neg', x)
        add = lambda x, y: q.binary('add', x, y)
        mul = lambda x, y: q.binary('mul', x, y)
        sign = lambda x: (q.compare(x, zero) > 0) - (q.compare(x, zero) < 0)

        def evaluate(poly, x):
            out = zero
            for c in reversed(poly):
                out = add(c, mul(out, x))
            return out

        def number(raw):
            require(isinstance(raw, list) and len(raw) == 2 and all(type(v) is int for v in raw)
                    and raw[1] > 0, 'invalid rational coordinate')
            f = Fraction(*raw)
            require([f.numerator, f.denominator] == raw, 'noncanonical rational coordinate')
            return q.number(f)

        def coordinate(raw):
            require(isinstance(raw, list) and len(raw) <= 3, 'invalid cubic-field coordinates')
            return evaluate([number(c) for c in raw], alpha)

        def polynomial(raw):
            require(isinstance(raw, list), 'invalid polynomial')
            return [coordinate(c) for c in raw]

        def equal_poly(a, b):
            return all(q.compare(a[i] if i < len(a) else zero,
                                 b[i] if i < len(b) else zero) == 0
                       for i in range(max(len(a), len(b))))

        def product(a, b):
            if not a or not b:
                return []
            out = [zero] * (len(a) + len(b) - 1)
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    out[i+j] = add(out[i+j], mul(x, y))
            return out

        def derivative(p):
            return [mul(q.number(i), p[i]) for i in range(1, len(p))]

        def in_interval(root, lower, upper):
            def bound(raw, is_lower):
                require(isinstance(raw, list), 'invalid endpoint')
                if raw == [0]: return is_lower
                if raw == [2]: return not is_lower
                require(len(raw) == 2 and type(raw[0]) is int and raw[0] == 1, 'invalid finite endpoint')
                order = q.compare(coordinate(raw[1]), root)
                return order < 0 if is_lower else order > 0
            return bound(lower, True) and bound(upper, False)

        for row in rows:
            name = row['case']
            middle = name == 'middle cubic embedding'
            defining = [1,-3,0,1] if middle else [-2,0,0,1]
            require(row.get('context') == 10378 and row.get('generator_head') == defining
                    and type(row.get('generator_sign')) is int and row['generator_sign'] == 1,
                    'wrong selected cubic generator or context')
            lower, upper = number(row['generator_lower']), number(row['generator_upper'])
            expected_lower, expected_upper = (zero,one) if middle else (one,two)
            require(q.compare(expected_lower, lower) < 0 and q.compare(lower, upper) < 0
                    and q.compare(upper, expected_upper) < 0, 'wrong generator isolating interval')
            generator_roots = q.roots([q.number(c,q.integer) for c in defining], integer=True)
            hits = [r for r,m in generator_roots if m == 1 and q.compare(lower,r) < 0 and q.compare(r,upper) < 0]
            require(len(hits) == 1, 'generator interval does not select a unique simple root')
            alpha = hits[0]
            quadratic = [neg(alpha), zero, one]
            repeated = product(product(quadratic, quadratic), [neg(one), one])
            expected_queries = [[zero,one], [neg(one),one], quadratic, [neg(alpha),one]]
            head = polynomial(row['head'])
            expected = [] if name == 'cubic-field zero' else repeated
            if name == 'cubic-field nonmonic roots':
                expected = [mul(neg(two), c) for c in expected]
            require(equal_poly(head, expected), 'wrong original number-field polynomial')
            queries = [polynomial(raw) for raw in row['queries']]
            require(len(queries) == 4 and all(equal_poly(a,b) for a,b in zip(queries, expected_queries)),
                    'wrong original query family')
            output = row['output']
            if name == 'cubic-field zero':
                require(output == {'kind': 'all'}, 'zero lost all-roots case')
                continue
            require(output.get('kind') == 'finite' and isinstance(output.get('entries'), list),
                    'nonzero input lost finite roots')
            expected_roots = q.roots(head)
            expected_roots.sort(key=cmp_to_key(lambda a,b: q.compare(a[0], b[0])))
            require(len(expected_roots) == 3 and len(output['entries']) == 3, 'missing or duplicate root')
            for entry, (root, multiplicity) in zip(output['entries'], expected_roots):
                require(type(entry.get('multiplicity')) is int and entry['multiplicity'] == multiplicity,
                        'wrong original multiplicity')
                raw = entry['root']
                if raw.get('kind') == 'point':
                    require(q.compare(coordinate(raw['value']), root) == 0, 'wrong point root or ordering')
                else:
                    require(raw.get('kind') == 'selected' and raw.get('context') == 10378,
                            'wrong selected-root context')
                    p = polynomial(raw['head'])
                    require(len(p) >= 2 and q.compare(p[-1], zero) != 0, 'invalid selected defining head')
                    indices, signs = raw['indices'], raw['signs']
                    require(isinstance(indices,list) and all(type(i) is int for i in indices)
                            and indices == sorted(set(indices)) and all(0 < i < len(p) for i in indices),
                            'invalid derivative slots')
                    require(isinstance(signs,list) and len(signs) == len(indices)
                            and all(type(s) is int and s in (-1,0,1) for s in signs), 'invalid Thom signs')
                    derivatives, current = [], p
                    while len(current) > 1:
                        current = derivative(current)
                        derivatives.append(current)
                    hits = [r for r,m in q.roots(p) if m == 1 and in_interval(r, raw['lower'], raw['upper'])
                            and all(sign(evaluate(derivatives[i-1], r)) == s for i,s in zip(indices, signs))]
                    require(len(hits) == 1 and q.compare(hits[0], root) == 0,
                            'descriptor changes selected root or order')
                    require(raw.get('generator_sign') == sign(root), 'wrong selected generator sign')
                    inverse = q.unary('inv', add(root, q.number(-3)))
                    require(raw.get('inverse_sign') == sign(inverse) and raw.get('inverse_identity_sign') == 0,
                            'selected number-field inverse changes value')
                expected_signs = [sign(evaluate(query, root)) for query in queries]
                require(entry.get('query_signs') == expected_signs
                        and all(type(s) is int for s in entry['query_signs']), 'wrong selected query signs')
    return {'oracle': 'FLINT qqbar', 'cases': len(rows), 'selected_fields': 'recorded cubic isolating intervals',
            'root_counts': [0 if r['case'] == 'cubic-field zero' else 3 for r in rows]}


if __name__ == '__main__':
    source = Path(sys.argv[1]).open() if len(sys.argv) == 2 else sys.stdin
    try:
        print(json.dumps(check([json.loads(line) for line in source if line.strip()]), sort_keys=True))
    finally:
        if source is not sys.stdin: source.close()
