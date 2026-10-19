#!/usr/bin/env python3
"""Exact independent checks for the clean/eager matched arithmetic trace."""
from __future__ import annotations
import argparse
from importlib.metadata import version
import json
import math
import sys
from pathlib import Path


def rational(value):
    from flint import fmpq
    if (not isinstance(value, list) or len(value) != 2 or
        any(type(c) is not int for c in value) or value[1] <= 0 or
        math.gcd(value[0], value[1]) != 1):
        raise ValueError("noncanonical rational coefficient")
    return fmpq(*value)


def polynomial(values):
    from flint import fmpq_poly
    if not isinstance(values, list) or (values and values[-1][0] == 0):
        raise ValueError("malformed polynomial coefficient array")
    return fmpq_poly([rational(q) for q in values])


def verify(row):
    from flint import fmpq_poly
    import z3
    from z3 import z3rcf
    if version('python-flint') != '0.9.0' or z3.get_version()[:4] != (4, 15, 4, 0):
        raise ValueError("pinned python-flint0.9.0 and Z34.15.4 are required")
    degree, steps = row['degree'], row['steps']
    if type(degree) is not int or degree not in (2, 4, 8, 16) or steps != 2 * degree:
        raise ValueError("wrong trace parameter")
    x = fmpq_poly([0, 1])
    head = polynomial(row['head'])
    working = polynomial(row['working_head'])
    expected = (x + 1) ** steps
    clean = polynomial(row['clean']['coefficients'])
    eager = polynomial(row['eager']['coefficients'])
    if head != 2 * x ** degree - 1 or working * 2 != head:
        raise ValueError("different defining polynomial or monic working head")
    if clean != expected or eager != expected % head:
        raise ValueError("stored polynomial does not match its arithmetic trace")
    if row['clean']['clean'] is not True or row['eager']['clean'] is not False:
        raise ValueError("storage arms did not exercise distinct normalization policies")
    if row['clean']['degree'] != clean.degree() or row['eager']['degree'] != eager.degree():
        raise ValueError("wrong stored degree")
    prefixes = row['prefixes']
    if not isinstance(prefixes, list) or len(prefixes) != steps + 1:
        raise ValueError("missing arithmetic prefixes")
    for step, prefix in enumerate(prefixes):
        clean_prefix = polynomial(prefix['clean']['coefficients'])
        eager_prefix = polynomial(prefix['eager']['coefficients'])
        if prefix['step'] != step or clean_prefix != (x + 1) ** step or eager_prefix != (x + 1) ** step % head:
            raise ValueError("stored prefix does not match its arithmetic trace")
        if (polynomial(prefix['clean']['query_coefficients']) !=
                (2 ** max(step - degree + 1, 0)) * ((x + 1) ** step % head) or
                polynomial(prefix['eager']['query_coefficients']) != eager_prefix):
            raise ValueError("wrong actual query polynomial")
        for arm, poly in [('clean', clean_prefix), ('eager', eager_prefix)]:
            stored = prefix[arm]
            if (stored['degree'] != poly.degree() or stored['sign'] != 1 or
                stored['clean'] is not all(d == 1 for _, d in stored['coefficients'])):
                raise ValueError("wrong prefix representation metadata")
    if any(abs(n).bit_length() >= 63 for arm in ('clean', 'eager')
           for prefix in prefixes for n, _ in prefix[arm]['coefficients']):
        raise ValueError("stored coefficient exceeds hash truncation bound")
    context = z3.Context()
    def coefficients(values):
        return [z3rcf.RCFNum(f'{n}/{d}', context) for n, d in values]
    roots = z3rcf.MkRoots(coefficients(row['head']), context)
    selected = [r for r in roots if 0 < r < 1]
    if len(selected) != 1:
        raise ValueError("positive root is not uniquely selected")
    def evaluate(values):
        result = z3rcf.RCFNum(0, context)
        for coefficient in reversed(coefficients(values)):
            result = result * selected[0] + coefficient
        return result
    a, b = evaluate(row['clean']['coefficients']), evaluate(row['eager']['coefficients'])
    if not (a == b and a > 0 and row['equal_at_root'] is True and
            type(row['clean']['sign']) is int and type(row['eager']['sign']) is int and
            row['clean']['sign'] == row['eager']['sign'] == 1):
        raise ValueError("selected values or signs disagree")
    def growth(values):
        return dict(max_numerator_bits=max(abs(n).bit_length() for n, _ in values),
                    max_denominator_bits=max(d.bit_length() for _, d in values),
                    total_coefficient_bits=sum(abs(n).bit_length()+d.bit_length() for n,d in values),
                    serialized_bytes=len(json.dumps(values,separators=(',',':')).encode()))
    return dict(degree=degree, steps=steps, checked=True,
                clean=growth(row['clean']['coefficients']), eager=growth(row['eager']['coefficients']),
                prefixes=[dict(step=p['step'], clean=growth(p['clean']['coefficients']),
                               eager=growth(p['eager']['coefficients']),
                               clean_query=growth(p['clean']['query_coefficients']),
                               eager_query=growth(p['eager']['query_coefficients'])) for p in prefixes])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('fixtures', nargs='*', type=Path)
    args = parser.parse_args()
    for contents in ([path.read_text() for path in args.fixtures] if args.fixtures else [sys.stdin.read()]):
        for line in contents.splitlines():
            print(json.dumps(verify(json.loads(line)), sort_keys=True))


if __name__ == '__main__':
    main()
