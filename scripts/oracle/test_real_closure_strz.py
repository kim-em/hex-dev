"""Independent checks of the original real Strzeboński inputs and outputs."""
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch
import unittest

from scripts.oracle.common import OracleMismatch
from scripts.oracle.real_closure_strz import parse_record, verify

FIXTURE = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/strz.jsonl'


def change_rational(data, before, after):
    """Change a scalar's literal rational coefficient while retaining its shape."""
    if not isinstance(data, list):
        return 0
    if len(data) == 3 and data == [0, before, 1]:
        data[1] = after
        return 1
    return sum(change_rational(child, before, after) for child in data)


def wrong_head_constant(rows):
    assert change_rational(rows[0]['head'][0], -1, -2) == 1


def wrong_case3_coefficient(rows):
    assert change_rational(rows[1]['head'][3], 5, 6) == 1


def sqrt5_target(rows):
    # The source still requests sqrt6. Interpret the actual target coefficient
    # 23 + 8*generator using sqrt5 instead, with its valid positive interval.
    assert change_rational(rows[3]['context'][2][2][1][0], -6, -5) == 1


class StrzTests(unittest.TestCase):
    def setUp(self):
        self.rows = [parse_record(line) for line in FIXTURE.read_text().splitlines() if line.strip()]

    def test_retained_native_outputs(self):
        self.assertEqual(verify(self.rows), 7)

    def test_source_manifest_binding(self):
        rows = deepcopy(self.rows)
        rows[0]['source'] = 'wrong'
        with patch('scripts.oracle.real_closure_strz.SOURCE', 'wrong'):
            with self.assertRaisesRegex(ValueError, 'source manifest differs'):
                verify(rows)

    def test_changed_original_input_or_complete_roots(self):
        changes = [
            lambda rows: rows.reverse(),
            lambda rows: rows.pop(),
            lambda rows: rows[0].update(source='wrong'),
            lambda rows: rows[0].update(case=True),
            lambda rows: rows[0]['inputs'][0].update(constant=3),
            lambda rows: rows[0]['inputs'][0].update(selected_index=0),
            lambda rows: rows[0]['inputs'][0]['multiplicities'].__setitem__(0, True),
            lambda rows: rows[0]['head'].pop(),
            lambda rows: rows[0]['results'].reverse(),
            lambda rows: rows[0]['results'].pop(),
            lambda rows: rows[0]['results'][0].update(multiplicity=2),
            lambda rows: rows[0]['results'][0].update(multiplicity=True),
            lambda rows: rows[0]['results'][0].update(root={
                'kind': 'point', 'value': rows[0]['head'][-1]}),
            lambda rows: rows[1]['source_roots'].append(rows[2]['source_roots'][0]),
            lambda rows: rows[2]['source_roots'].reverse(),
            lambda rows: rows[2]['source_roots'][0].__setitem__(2, [2]),
            lambda rows: rows[3]['inputs'][2].update(constant=5),
            wrong_head_constant,
            wrong_case3_coefficient,
            lambda rows: rows[1]['results'][0].update(root=deepcopy(rows[1]['results'][1]['root'])),
            lambda rows: rows[2]['context'][2].__setitem__(0, deepcopy(rows[2]['source_roots'][0])),
            sqrt5_target,
        ]
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                rows = deepcopy(self.rows)
                change(rows)
                with self.assertRaises((ValueError, OracleMismatch)):
                    verify(rows)


if __name__ == '__main__':
    unittest.main()
