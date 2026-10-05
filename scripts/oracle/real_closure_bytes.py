#!/usr/bin/env python3
"""Independently parse actual printed tower packets with Python's JSON parser.

Check printed/structured packet agreement, top-level signature and frame field
structure, stage/frame counts, and specified rational, Unicode and defining-head literals. Algebraic
payload values and replay graphs are not independently established here.
Field arithmetic is covered by the existing algebraic conformance oracles;
native readers exercise reconstruction/rejection and have exact roundtrip proofs.
"""
import json
from pathlib import Path
import sys

CASES = ['rational bytes','reducible inverse bytes','nested root bytes',
         'successive infinitesimal bytes','Unicode provider binding']


def require(test, message):
    if not test:
        raise ValueError(message)


def parse(text):
    def pairs(entries):
        result = {}
        for key,value in entries:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def noninteger(_):
        raise ValueError('noninteger JSON number')
    return json.loads(text, object_pairs_hook=pairs,parse_float=noninteger,parse_constant=noninteger)


def same_json(a,b):
    if type(a) is not type(b):
        return False
    if isinstance(a,list):
        return len(a) == len(b) and all(same_json(x,y) for x,y in zip(a,b))
    if isinstance(a,dict):
        return list(a) == list(b) and all(same_json(a[k],b[k]) for k in a)
    return a == b


def integer_tree(value):
    if type(value) is int:
        return
    require(type(value) is list, 'noninteger packet leaf')
    for entry in value:
        integer_tree(entry)


def packet(text, expected, *, text_payload=False):
    actual = parse(text)
    require(same_json(actual,expected), 'printed binding or payload differs')
    require(isinstance(actual,list) and len(actual) == 2, 'wrong packet field count')
    signature = actual[0]
    require(isinstance(signature,list) and len(signature) == 3 and
            isinstance(signature[0],list) and type(signature[1]) is int and signature[1] >= 0 and
            isinstance(signature[2],list), 'wrong full signature')
    for provider in signature[0]:
        require(type(provider) is list and len(provider) == 2 and
                type(provider[0]) is str and type(provider[1]) is int and provider[1] >= 0,
                'wrong provider registration')
    for frame in signature[2]:
        integer_tree(frame)
        require(isinstance(frame,list) and len(frame) == 7 and same_json(frame[0],[0]) and
                all(isinstance(frame[i],list) for i in range(1,7)), 'incomplete root frame')
    if text_payload:
        require(type(actual[1]) is str, 'wrong text payload')
    else:
        integer_tree(actual[1])
    return signature


def verify(rows):
    require([r.get('case') for r in rows] == CASES, 'missing or reordered byte cases')
    for i,row in enumerate(rows):
        signature = packet(row['value_text'],row['value_json'],text_payload=(i == 4))
        if i == 4:
            require(set(row) == {'case','value_text','value_json','unknown_rejected'}, 'wrong Unicode record')
            require(same_json(signature,[[['α\n"\\λ',17]],2,[]]) and
                    same_json(row['value_json'][1],'\x00\nλ𐐷"\\') and row['unknown_rejected'] is True,
                    'Unicode or provider version changed')
            continue
        require(set(row) == {'case','value_text','value_json','polynomial_text','polynomial_json',
                            'sign','roundtrip','reconstructed','rejections'}, 'wrong byte record')
        polynomial_binding = packet(row['polynomial_text'],row['polynomial_json'])
        require(same_json(polynomial_binding,signature), 'polynomial context differs')
        require(signature[0] == [] and signature[1] == [0,0,0,2][i] and
                len(signature[2]) == [0,1,2,0][i], 'lost context stage or root')
        require(type(row['sign']) is int and row['sign'] == [1,-1,1,1][i], 'wrong native sign')
        require(row['roundtrip'] is True and row['reconstructed'] is True and
                type(row['rejections']) is int and row['rejections'] == 8, 'native reader check failed')
        if i == 0:
            require(same_json(row['value_json'][1],[0,1,3]) and
                    same_json(row['polynomial_json'][1],[[0,-2,1],[0,0,1],[0,1,1]]),
                    'wrong rational example')
        elif i in (1,2):
            require(same_json(signature[2][0][1],[[0,6,1],[0,-2,1],[0,-3,1],[0,1,1]]),
                    'reducible selected predecessor changed')
    return len(rows)


if __name__ == '__main__':
    text = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    print(f'verified {verify([parse(line) for line in text.splitlines() if line.strip()])} '
          'printed tower packets with independent JSON parsing')
