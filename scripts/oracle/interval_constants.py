#!/usr/bin/env python3
"""Independent exact π/e point oracle (stdlib only, mode always).

Rebuild each source formula with Fraction, factorial and direct powers rather
than the Lean recurrences. Check exact grid rounding and requested width.
Independently enclose π with 4*(atan(1/2)+atan(1/3)), using alternating-series
bounds, and e with a longer factorial sum and one-sided geometric tail.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import sys

from common import read_fixtures, write_failure


def atan(q: int, n: int) -> Q:
    return sum((Q((-1) ** i, (2 * i + 1) * q ** (2 * i + 1))
                for i in range(n)), Q())


def atan_bounds(q: int, n: int) -> tuple[Q, Q]:
    center = atan(q, n)
    next_sum = center + Q((-1) ** n, (2 * n + 1) * q ** (2 * n + 1))
    return min(center, next_sum), max(center, next_sum)


def validate(record: dict) -> None:
    source, k, n = record['source'], record['bits'], record['order']
    if source == 'pi-machin-v1':
        center = 16 * atan(5, n) - 4 * atan(239, n)
        radius = sum(Q(a * q * q, q ** (2 * n + 1) * (q * q - 1))
                     for a, q in [(16, 5), (4, 239)])
        a, b = atan_bounds(2, 2 * k + 32), atan_bounds(3, 2 * k + 32)
        oracle_lo, oracle_hi = 4 * (a[0] + b[0]), 4 * (a[1] + b[1])
    elif source == 'exp-one-taylor-v1':
        center = sum((Q(1, factorial(i)) for i in range(n)), Q())
        radius = Q(n + 1, factorial(n) * n)
        m = k + 16
        oracle_lo = sum((Q(1, factorial(i)) for i in range(m)), Q())
        oracle_hi = oracle_lo + Q(2, factorial(m))
    else:
        raise ValueError(f'unknown source: {source}')
    assert Q(*record['center']) == center, 'wrong source sum'
    assert Q(*record['radius']) == radius, 'wrong remainder'
    lo, hi = Q(*record['lower']), Q(*record['upper'])
    scale = 2 ** (k + 2)
    exact_lo = Q((center - radius) * scale // 1, scale)
    exact_hi = -Q(-(center + radius) * scale // 1, scale)
    assert (lo, hi) == (exact_lo, exact_hi), 'wrong outward grid cuts'
    assert 0 < hi - lo <= Q(1, 2 ** k), 'wrong final width'
    assert lo <= oracle_lo <= oracle_hi <= hi, 'independent constant enclosure escaped cuts'
    assert record['accepted'] is True, 'compiled replay rejected'


def main() -> None:
    # Exact 1000-bit source witnesses have denominators above 4300 decimal digits.
    sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('fixtures', nargs='?', type=Path)
    args = parser.parse_args()
    count = 0
    for record in read_fixtures(args.fixtures):
        try:
            validate(record)
        except (AssertionError, ValueError) as error:
            path = write_failure('conformance-failures', library='HexInterval',
                                 profile='ci', seed=0, case_id=record['case'],
                                 kind=record['kind'], input_record=record,
                                 lean_output=record, oracle_output=None,
                                 oracle_name='python-fractions-second-machin',
                                 oracle_version=sys.version.split()[0], diff=str(error))
            raise AssertionError(f'{record["case"]}: {error}; replay: {path}') from error
        count += 1
    assert count, 'no constant fixtures'
    print(f'interval constants: {count} exact source and independent enclosure cases passed')


if __name__ == '__main__':
    main()
