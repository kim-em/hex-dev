#!/usr/bin/env python3
"""Pinned qqbar comparison endpoints for the real-algebraic compiled bench.

One JSON request/reply per line. Inputs are constructed once per persistent
process; timed requests include JSON transport and comparison, not input setup.
The protocol control has the same framing and returns the same ordering code.
"""
import json
import sys
from fractions import Fraction
from real_algebraic_qqbar import QQBar


def main():
    with QQBar() as oracle:
        a = oracle.unary('sqrt', oracle.number(2))
        b = oracle.unary('sqrt', oracle.number(3))
        close = oracle.binary('add', a, oracle.number(Fraction(1, 2**50)))
        cases = {'separated': (a, b), 'close': (a, close)}
        for line in sys.stdin:
            try:
                request = json.loads(line)
                case = request['case']
                value = -1 if case == 'protocol' else oracle.compare(*cases[case])
                reply = {'ok': True, 'result': 0 if value < 0 else 1 if value == 0 else 2}
            except (KeyError, ValueError, ArithmeticError) as error:
                reply = {'ok': False, 'error': str(error)}
            print(json.dumps(reply), flush=True)


if __name__ == '__main__':
    main()
