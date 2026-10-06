#!/usr/bin/env python3
"""Check actual infinitesimal inputs and their elementary root/sign table.

Counters and maximum operand sizes are native observations. They are checked
for shape, not independently reconstructed by this mathematical oracle.
"""
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.sign_det_trace_archive import check_retained


def constant(depth, value):
    if depth == 0:
        return [value, 1]
    return {'num': [] if value == 0 else [constant(depth-1, value)],
            'den': [constant(depth-1, 1)]}


def epsilon(depth):
    return {'num': [constant(depth-1, 0), constant(depth-1, 1)],
            'den': [constant(depth-1, 1)]}


def integer_tree(value):
    if type(value) is int:
        return True
    if isinstance(value, list):
        return all(map(integer_tree, value))
    if isinstance(value, dict):
        return all(map(integer_tree, value.values()))
    return False


def size(value):
    if isinstance(value, list):
        return max(abs(value[0]).bit_length(), value[1].bit_length()), 1
    parts = [size(c) for c in value['num'] + value['den']]
    return max([1] + [p[0] for p in parts]), sum(p[1] for p in parts)


def validate(path):
    rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if [(r['result']['depth'], r['result']['queries']) for r in rows] != [(1,4),(1,8),(2,4),(2,8)]:
        raise ValueError('missing or reordered case')
    for row in rows:
        r = row['result']
        for key in ('depth', 'queries', 'context', 'coefficient', 'head', 'queryPolynomials', 'entries'):
            if not integer_tree(r[key]):
                raise ValueError('invalid numeric subject')
        depth, count = r['depth'], r['queries']
        e = epsilon(depth)
        if r['coefficient'] != e or r['head'] != [constant(depth,0), constant(depth,1)]:
            raise ValueError('wrong infinitesimal or defining polynomial')
        if r['queryPolynomials'] != [[e]]*count:
            raise ValueError('wrong query subjects')
        if r['lower'] != 'negInf' or r['upper'] != 'posInf':
            raise ValueError('wrong prepared interval')
        # P=X has the unique root 0. Every query is the positive newest
        # infinitesimal, so its full sign condition has count one.
        if r['entries'] != [[[1]*count,1]]:
            raise ValueError('wrong complete sign table')
        if r['context'] != 10377+depth*10+count or r['standardReplayAccepted'] is not True:
            raise ValueError('wrong context or failed ordinary replay')
        for key in ('coefficientCalls', 'maxNormalizedRatBits', 'maxRationalSlots'):
            if type(row[key]) is not int or row[key] <= 0:
                raise ValueError('missing coefficient-size observation')
        input_bits, input_slots = size(r['coefficient'])
        if row['maxNormalizedRatBits'] < input_bits or row['maxRationalSlots'] < input_slots:
            raise ValueError('recorded maximum omits the observed infinitesimal')
    return rows


if __name__ == '__main__':
    validate(sys.argv[1])
    if "--retained" in sys.argv[2:]:
        check_retained(sys.argv[1])
    print('4/4 actual nested-field polynomial/query subjects and complete root/sign answers pass; size schema valid')
