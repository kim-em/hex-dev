"""Independent checks of the retained original Rioboo fixtures and mutations."""
from copy import deepcopy
from pathlib import Path
import unittest

from scripts.oracle.real_closure_rioboo import parse_record, verify
from scripts.oracle.common import OracleMismatch

FIXTURE = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/rioboo.jsonl'


class RiobooTests(unittest.TestCase):
    def setUp(self):
        self.rows = [parse_record(line) for line in FIXTURE.read_text().splitlines() if line.strip()]

    def test_actual_native_outputs(self):
        self.assertEqual(verify(self.rows), 15)

    def test_changed_source_root_input_or_arithmetic(self):
        changes = [
            lambda rows: rows.reverse(),
            lambda rows: rows.pop(),
            lambda rows: rows[0].update(source='wrong'),
            lambda rows: rows[0]['head'].__setitem__(2, -9),
            lambda rows: rows[0]['selected_indices'].__setitem__(0, 1),
            lambda rows: rows[0]['multiplicities'].__setitem__(0, 2),
            lambda rows: rows[0]['roots'].reverse(),
            lambda rows: rows[0]['roots'][0].__setitem__(2, [2]),
            lambda rows: rows[0]['values'].__setitem__(0, rows[0]['values'][1]),
            lambda rows: rows[0]['signs'].__setitem__(-1, 1),
            lambda rows: rows[1]['inputs'][0].update(constant=27),
            lambda rows: rows[1]['inputs'][0].update(selected_index=0),
            lambda rows: rows[1]['inputs'].pop(),
            lambda rows: rows[1]['values'].__setitem__(-2, rows[1]['values'][0]),
            lambda rows: rows[1]['values'][0].__setitem__(1, -1),
            lambda rows: rows[1]['signs'].__setitem__(6, 1),
        ]
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                rows = deepcopy(self.rows)
                change(rows)
                with self.assertRaises((ValueError, OracleMismatch)):
                    verify(rows)


if __name__ == '__main__':
    unittest.main()
