#!/usr/bin/env python3
"""Check the four real Strzeboński inputs from the original CADE-24 scripts."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_closure_basic import Reader, parse_record
from scripts.oracle.real_closure_rioboo import originals
from scripts.oracle.real_closure_number_field_samples import require
from scripts.oracle.sign_det_z3 import check_version
from scripts.oracle.real_closure_cade24_sources import require_source_hashes

SOURCE = '4d26847955ecacaff4cadd0dce4550f125a726ea3f4e768d7aedd48ebcdaa7c4'
CONSTANTS = {2: [2, 3], 3: [7], 4: [], 6: [2, 3, 6]}


def positive_roots(reader, row):
    constants = CONSTANTS[row['case']]
    require(type(row['inputs']) is list and len(row['inputs']) == len(constants),
            'wrong source radical inventory')
    result = []
    for constant, data in zip(constants, row['inputs']):
        require(set(data) == {'constant', 'roots', 'multiplicities', 'selected_index'} and
                type(data['constant']) is int and data['constant'] == constant and
                type(data['selected_index']) is int and data['selected_index'] == 1,
                'wrong original radical or selection')
        roots = originals(reader, [-constant, 0, 1], data['roots'], data['multiplicities'])
        require(len(roots) == 2 and roots[1] > 0, 'wrong positive square-root selection')
        result.append(roots[1])
    return result


def expected_head(reader, row):
    q = reader.rcf
    one, zero = q.one, q.zero
    radical = positive_roots(reader, row)
    if row['case'] != 4:
        require(row['source_roots'] == [], 'unexpected non-radical source roots')
    if row['case'] == 2:
        a, b = radical
        return [-one, a + 7, (a + b)**3, zero, zero, one]
    if row['case'] == 3:
        a, = radical
        return [-11 + 3*a, zero, zero, a + 5, zero, zero, zero, zero, zero, zero, one]
    if row['case'] == 4:
        roots = originals(reader, [-5, -7, 0, 1], row['source_roots'], [1, 1, 1])
        require(len(roots) == 3, 'wrong source cubic root count')
        a, b = roots[1], roots[2]
        return [b, a, zero, one]
    a, b, c = radical
    # The original executed coefficient is sqrt6, despite the sqrt(5) label.
    return [-10*a - 8*b, 38 + 16*c, -(29*a - 24*b), 23 + 8*c, -(5*a - 2*b), one]


def verify_case(row):
    require_source_hashes(['strz.py'], [SOURCE])
    require(type(row) is dict and set(row) ==
            {'case', 'source', 'inputs', 'source_roots', 'context', 'head', 'results'},
            'wrong Strzeboński record schema')
    require(type(row['case']) is int and row['case'] in CONSTANTS and row['source'] == SOURCE,
            'wrong original case or source identity')
    reader = Reader()
    q = reader.rcf
    head = expected_head(reader, row)
    signature = row['context']
    require(type(signature) is list and len(signature) == 3 and type(signature[2]) is list
            and 0 < len(signature[2]) <= (2 if row['case'] == 4 else len(CONSTANTS[row['case']])),
            'wrong original coefficient owner depth')
    owners = reader.context(signature, 0, len(signature[2]))
    require(type(row['head']) is list and
            [reader.value(value, owners, 0) for value in row['head']] == head,
            'executed original polynomial differs')
    require(type(row['results']) is list, 'wrong complete-root result')
    expected = q.api.MkRoots(head, q.context)
    require(len(row['results']) == len(expected), 'wrong complete root count')
    actual = []
    for entry in row['results']:
        require(type(entry) is dict and set(entry) == {'root', 'multiplicity'} and
                type(entry['multiplicity']) is int and entry['multiplicity'] > 0,
                'wrong root multiplicity record')
        root = entry['root']
        require(type(root) is dict, 'wrong root representation')
        if root.get('kind') == 'point':
            require(set(root) == {'kind', 'value'}, 'wrong point schema')
            value = reader.value(root['value'], owners, 0)
        else:
            require(root.get('kind') == 'selected' and set(root) == {'kind', 'descriptor'},
                    'wrong selected-root schema')
            value = reader.selected(root['descriptor'], owners, 0)
        require(q.eval(head, value) == 0, 'returned value is not an original root')
        polynomial, multiplicity = head, 0
        while polynomial and q.eval(polynomial, value) == 0:
            multiplicity += 1
            polynomial = q.derivative(polynomial)
        require(multiplicity == entry['multiplicity'], 'exact Yun multiplicity differs')
        actual.append(value)
    require(actual == expected, 'root order, completeness or selected embedding differs')
    return len(actual)


def verify(rows):
    check_version()
    require(type(rows) is list and [row.get('case') for row in rows] == [2, 3, 4, 6],
            'missing or reordered original Strzeboński cases')
    return sum(verify_case(row) for row in rows)


if __name__ == '__main__':
    text = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    rows = [parse_record(line) for line in text.splitlines() if line.strip()]
    if len(rows) == 1:
        check_version()
        count = verify_case(rows[0])
    else:
        count = verify(rows)
    print(f'verified {count} original Strzeboński roots with exact Z3 multiplicities')
