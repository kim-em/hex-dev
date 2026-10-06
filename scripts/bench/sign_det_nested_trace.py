#!/usr/bin/env python3
"""Check actual infinitesimal inputs and their elementary root/sign table.

Counters and maximum operand sizes are native observations. They are checked
for shape, not independently reconstructed by this mathematical oracle.
"""
import json
from pathlib import Path
import sys


def constant(depth, value):
    if depth == 0:
        return [value, 1]
    return {'num': [] if value == 0 else [constant(depth-1, value)],
            'den': [constant(depth-1, 1)]}


def epsilon(depth):
    return {'num': [constant(depth-1, 0), constant(depth-1, 1)],
            'den': [constant(depth-1, 1)]}


def validate(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if [(r['result']['depth'], r['result']['queries']) for r in rows] != [(1,4),(1,8),(2,4),(2,8)]:
        raise ValueError('missing or reordered case')
    for row in rows:
        r = row['result']
        depth, count = r['depth'], r['queries']
        e = epsilon(depth)
        if r['coefficient'] != e or r['head'] != [constant(depth,0), constant(depth,1)]:
            raise ValueError('wrong infinitesimal or defining polynomial')
        if r['queryPolynomials'] != [[e]]*count:
            raise ValueError('wrong query subjects')
        # P=X has the unique root 0. Every query is the positive newest
        # infinitesimal, so its full sign condition has count one.
        if r['entries'] != [[[1]*count,1]]:
            raise ValueError('wrong complete sign table')
        if r['context'] != 10377+depth*10+count or r['standardReplayAccepted'] is not True:
            raise ValueError('wrong context or failed ordinary replay')
        for key in ('coefficientCalls', 'maxNormalizedRatBits', 'maxRationalSlots'):
            if type(row[key]) is not int or row[key] <= 0:
                raise ValueError('missing coefficient-size observation')
    return rows


if __name__ == '__main__':
    validate(sys.argv[1])
    print('4/4 actual nested-field polynomial/query subjects and complete root/sign answers pass; size schema valid')
