#!/usr/bin/env python3
"""Check the original CADE-24 Rioboo inputs and native common-field arithmetic."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_closure_basic import Reader, parse_record
from scripts.oracle.real_closure_number_field_samples import require
from scripts.oracle.real_closure_isolation import sign
from scripts.oracle.sign_det_z3 import check_version
from scripts.oracle.real_closure_cade24_sources import require_source_hashes

SOURCES = [
    '51dee2d698ebe39a267d642b35d2197936739517234cd0be7039fe2ee2c5eba7',
    '2c13ac14e1c8783d1aaf88e56ee6ee5d40ebc730f19759b2b17321a722a70936',
]


def originals(reader, head, frames, multiplicities):
    require(type(frames) is list and len(frames) == len(multiplicities) and
            all(type(value) is int and value == 1 for value in multiplicities),
            'wrong original multiplicities')
    field = reader.rcf
    polynomial = [field.one * coefficient for coefficient in head]
    require(field.squarefree(polynomial), 'original polynomial is not squarefree')
    expected = field.api.MkRoots(polynomial, field.context)
    for frame in frames:
        require(type(frame) is list and len(frame) == 7 and type(frame[1]) is list and
                [reader.value(coefficient, [], 0) for coefficient in frame[1]] == polynomial,
                'original defining polynomial differs')
    roots = [reader.selected(frame, [], 0) for frame in frames]
    require(roots == expected, 'original root list or order differs')
    return roots


def common_values(reader, row, expected, max_depth):
    signature = row['context']
    require(type(signature) is list and len(signature) == 3 and
            type(signature[2]) is list and 0 < len(signature[2]) <= max_depth,
            'wrong shared algebraic depth')
    roots = reader.context(signature, 0, len(signature[2]))
    values = [reader.value(value, roots, 0) for value in row['values']]
    require(values == expected, 'computed values or selected embeddings differ')
    require(row['signs'] == [sign(value) for value in expected] and
            all(type(value) is int for value in row['signs']), 'computed signs differ')
    return len(values)


def verify(rows):
    check_version()
    require_source_hashes(['rioboo1.py', 'rioboo2.py'], SOURCES)
    require(type(rows) is list and len(rows) == 2 and
            [row.get('case') for row in rows] == ['cade24 rioboo1', 'cade24 rioboo2'],
            'missing or reordered original Rioboo cases')
    require([row.get('source') for row in rows] == SOURCES, 'wrong original source identity')
    reader = Reader()
    first, second = rows
    require(set(first) == {'case', 'source', 'head', 'roots', 'multiplicities',
                           'selected_indices', 'context', 'values', 'signs'}, 'wrong quartic schema')
    require(first['head'] == [1, 0, -10, 0, 1] and
            all(type(value) is int for value in first['head']) and
            first['selected_indices'] == [2, 3] and
            all(type(value) is int for value in first['selected_indices']),
            'wrong original quartic or selections')
    roots = originals(reader, first['head'], first['roots'], first['multiplicities'])
    require(len(roots) == 4, 'wrong original quartic root count')
    a, b = roots[2], roots[3]
    half = (a + b).__div__(2)
    square = half * half
    require(a > 0 and b > a and square == 3, 'independent Rioboo identity failed')
    count = common_values(reader, first, [a, b, half, square, square - 3], 2)

    require(set(second) == {'case', 'source', 'inputs', 'context', 'values', 'signs'},
            'wrong radical schema')
    require(type(second['inputs']) is list and len(second['inputs']) == 5,
            'wrong original radical input count')
    selected = []
    for constant, data in zip([28, 82, 33, 74, 28], second['inputs']):
        require(set(data) == {'constant', 'roots', 'multiplicities', 'selected_index'} and
                type(data['constant']) is int and data['constant'] == constant and
                type(data['selected_index']) is int and data['selected_index'] == 1,
                'wrong original radical or selection')
        roots = originals(reader, [-constant, 0, 1], data['roots'], data['multiplicities'])
        require(len(roots) == 2 and roots[1] > 0, 'wrong square-root count or positivity')
        selected.append(roots[1])
    a, b, c, d, repeated = selected
    left, right = a + b, c + d
    require(left < right and repeated == a and repeated * repeated == 28,
            'independent radical comparison failed')
    count += common_values(reader, second,
                           [a, b, c, d, left, right, left - right,
                            repeated, repeated * repeated, repeated * repeated - 28], 4)
    return count


if __name__ == '__main__':
    text = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    print(f'verified {verify([parse_record(line) for line in text.splitlines() if line.strip()])} '
          'original Rioboo values with Z3 4.15.4')
