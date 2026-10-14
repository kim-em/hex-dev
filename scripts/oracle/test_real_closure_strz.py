"""Independent checks of the original real Strzeboński inputs and outputs."""
from copy import deepcopy
from pathlib import Path
import unittest

from scripts.oracle.common import OracleMismatch
from scripts.oracle.real_closure_strz import parse_record, verify

FIXTURE = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/strz.jsonl'


class StrzTests(unittest.TestCase):
    def setUp(self):
        self.rows = [parse_record(line) for line in FIXTURE.read_text().splitlines() if line.strip()]

    def test_actual_native_outputs(self):
        self.assertEqual(verify(self.rows), 7)

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
        ]
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                rows = deepcopy(self.rows)
                change(rows)
                with self.assertRaises((ValueError, OracleMismatch)):
                    verify(rows)


if __name__ == '__main__':
    unittest.main()
