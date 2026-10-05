#!/usr/bin/env python3
"""Exact FLINT checks of full root packets and fresh predecessor semantics.

The native reader validates replay graphs. This independent oracle reconstructs
selected embeddings from polynomial roots, endpoints and Thom signs, then checks
root kinds, literal order, multiplicities and the prescribed fixture values.
"""
from fractions import Fraction
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_closure_number_field_samples import Reader, require
from scripts.oracle.real_algebraic_qqbar import QQBar, VERSION

CASES = ['universal roots', 'empty finite roots', 'literal point order',
         'selected reducible root', 'fresh algebraic predecessor', 'complete repeated roots']
ERRORS = {
    'universal roots': [
        ('unknown root kind', 'unknown root kind'),
        ('unknown root-set kind', 'unknown root-set kind'),
        ('nonempty universal roots', 'nonempty universal root payload'),
        ('zero multiplicity', 'nonpositive root multiplicity'),
        ('malformed point', 'invalid base payload'),
        ('stale root predecessor', 'root predecessor mismatch'),
        ('stale root-set predecessor', 'root-set predecessor mismatch'),
        ('invalid root UTF-8', 'invalid certificate JSON or UTF-8'),
        ('root byte limit', 'certificate byte limit exceeded'),
        ('root-set nesting limit', 'certificate nesting limit exceeded'),
        ('root-set truncation', 'truncated certificate syntax'),
        ('unknown validated provider', 'unknown validated base')],
    'selected reducible root': [
        ('changed head', 'graph context or domain mismatch'),
        ('changed lower endpoint', 'graph context or domain mismatch'),
        ('changed Thom indices', 'root descriptor replay rejected'),
        ('changed Thom signs', 'root descriptor replay rejected'),
        ('missing replay graph', 'wrong field count')],
}


def parse_record(text):
    def pairs(entries):
        result = {}
        for key, value in entries:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def invalid(_):
        raise ValueError('noninteger JSON number')
    return json.loads(text, object_pairs_hook=pairs, parse_float=invalid, parse_constant=invalid)


def integers(raw):
    if type(raw) is int:
        return
    require(type(raw) is list, 'noninteger root packet leaf')
    for value in raw:
        integers(value)


def root(reader, binding, raw):
    require(type(raw) is list and len(raw) == 2, 'wrong root fields')
    predecessors = reader.context(binding)
    if raw[0] == 0:
        return reader.value(raw[1], predecessors)
    require(raw[0] == 1, 'unknown root kind')
    child = reader.context([binding[0], binding[1], binding[2] + [raw[1]]])
    return child[-1]


def verify(rows):
    require([row.get('case') for row in rows] == CASES, 'missing or reordered root cases')
    with QQBar() as q:
        r = Reader(q)
        alpha = q.unary('sqrt', q.number(2))
        expected = [[], [], [q.number(2), q.number(Fraction(1, 3))], [alpha],
                    [q.unary('sqrt', alpha), q.unary('inv', q.binary('sub', alpha, q.number(3)))],
                    [q.unary('neg', alpha), q.number(0), alpha, q.number(3)]]
        multiplicities = [[], [], [3, 2], [2], [3, 1], [3, 2, 3, 4]]
        for i, row in enumerate(rows):
            require(set(row) == {'case', 'packet', 'packet_text', 'root_texts', 'reconstructed', 'rejections'}, 'wrong root record')
            printed = parse_record(row['packet_text'])
            integers(printed)
            require(printed == row['packet'], 'printed root-set packet differs')
            integers(row['packet'])
            integers(row['reconstructed'])
            require(row['packet'] == row['reconstructed'], 'fresh packet changed')
            require(type(row['packet']) is list and len(row['packet']) == 2, 'wrong packet fields')
            binding, payload = row['packet']
            predecessors = r.context(binding)
            require(len(predecessors) == (1 if i == 4 else 0), 'wrong predecessor depth')
            if i == 4:
                require(r.same(predecessors[0], alpha), 'wrong predecessor embedding')
            require(type(payload) is list and len(payload) == 2 and
                    payload[0] == (0 if i == 0 else 1) and type(payload[1]) is list,
                    'wrong root-set kind')
            entries = payload[1]
            require(len(entries) == len(expected[i]), 'missing or extra root entry')
            require(type(row['root_texts']) is list and len(row['root_texts']) == len(entries),
                    'missing individual root packets')
            for entry, value, count, text in zip(entries, expected[i], multiplicities[i], row['root_texts']):
                individual = parse_record(text)
                integers(individual)
                require(individual == [binding, entry[0]], 'individual root packet differs')
                require(type(entry) is list and len(entry) == 2 and type(entry[1]) is int and
                        entry[1] == count, 'wrong root multiplicity')
                require(r.same(root(r, binding, entry[0]), value), 'wrong selected root or literal order')
            checks = [{'case': name, 'message': message} for name, message in ERRORS.get(row['case'], [])]
            require(row['rejections'] == checks, 'missing or changed native rejection')
    return len(rows)


if __name__ == '__main__':
    text = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    count = verify([parse_record(line) for line in text.splitlines() if line.strip()])
    print(f'verified {count} full root packets with {VERSION}')
