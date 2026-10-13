#!/usr/bin/env python3
"""Exact FLINT checks of both complete rational root routes and Yun labels."""
import json
from fractions import Fraction
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from flint import fmpq, fmpq_poly
from scripts.oracle.real_closure_trivial import TrivialChecker
from scripts.oracle.real_algebraic_qqbar import QQBar, VERSION
from scripts.oracle.sign_det_common import require
from scripts.oracle.real_closure_isolation import parse_record

METHODS = ('generic', 'canonical')


def rational(value):
    require(type(value) is list and len(value) == 2 and all(type(v) is int for v in value)
            and value[1] > 0, 'malformed rational coefficient')
    result = Fraction(*value)
    require([result.numerator, result.denominator] == value, 'noncanonical rational coefficient')
    return result


def verify(rows):
    require([(row.get('index'), row.get('method')) for row in rows] ==
            [(index, method) for index in range(6) for method in METHODS],
            'missing, duplicate or reordered trivial route')
    results = []
    with QQBar() as q:
        checker = TrivialChecker(q)
        zero, two = q.number(0), q.number(2)
        upper = q.unary('sqrt', two)
        expected_roots = [q.unary('neg', upper), upper]
        for row in rows:
            require(set(row) == {'index', 'method', 'coefficients', 'multiplicity', 'roots'},
                    'malformed trivial measurement record')
            index = row['index']
            require(type(index) is int and type(row['multiplicity']) is int,
                    'noninteger trivial parameter')
            multiplicity = 0 if index < 2 else 2**(index-2)
            require(row['multiplicity'] == multiplicity, 'changed input multiplicity')
            actual = [rational(value) for value in row['coefficients']]
            polynomial = fmpq_poly([fmpq(value.numerator, value.denominator) for value in actual])
            expected = fmpq_poly([]) if index == 0 else fmpq_poly([5]) if index == 1 else fmpq_poly([-2, 0, 1])**multiplicity
            require(polynomial == expected and len(actual) == len(list(expected)),
                    'changed or noncanonical original rational polynomial')
            roots = row['roots']
            if index == 0:
                require(roots is None, 'zero polynomial lost its complete all result')
            elif index == 1:
                require(roots == [], 'nonzero constant gained a root')
            else:
                _, factors = polynomial.factor()
                require(len(factors) == 1 and factors[0][0] == fmpq_poly([-2, 0, 1])
                        and factors[0][1] == multiplicity, 'independent Yun factor label differs')
                require(type(roots) is list and len(roots) == 2, 'incomplete distinct real root set')
                for entry, expected_root, expected_sign in zip(roots, expected_roots, (-1, 1)):
                    require(set(entry) == {'polynomial', 're', 'im', 'precision', 'sign', 'multiplicity'}
                            and type(entry['multiplicity']) is int and entry['multiplicity'] == multiplicity
                            and type(entry['sign']) is int and entry['sign'] == expected_sign,
                            'root multiplicity, sign or schema differs')
                    value = checker.value({'poly': entry['polynomial'], 're': entry['re'],
                                           'im': entry['im'], 'prec': entry['precision']})
                    require(q.compare(value, expected_root) == 0 and q.compare(value, zero) == expected_sign,
                            'ordered selected root differs from exact FLINT square root')
            results.append(dict(index=index, method=row['method'], degree=max(0,len(actual)-1),
                                multiplicity=multiplicity,
                                all=roots is None, distinct_roots=None if roots is None else len(roots)))
    return results


if __name__ == '__main__':
    text = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    rows = [parse_record(line) for line in text.splitlines() if line.strip()]
    results = verify(rows)
    print(json.dumps({'verified_arms': len(results), 'oracle': VERSION, 'results': results}, indent=2))
