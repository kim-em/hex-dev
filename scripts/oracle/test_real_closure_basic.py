"""The recorded paper operations must retain their exact source semantics."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_closure_basic import parse_record, verify
from scripts.oracle.common import OracleMismatch


class BasicTests(unittest.TestCase):
    def setUp(self):
        path = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/basic.jsonl'
        self.rows = [parse_record(line) for line in path.read_text().splitlines() if line.strip()]

    def reject(self, change):
        rows = copy.deepcopy(self.rows)
        change(rows)
        with self.assertRaises((ValueError, OracleMismatch)):
            verify(rows)

    def test_actual_source_operations(self):
        self.assertEqual(verify(self.rows), 9)

    def test_root_order_and_multiplicity(self):
        self.reject(lambda rows: rows[0]['roots'].reverse())
        self.reject(lambda rows: rows[0]['multiplicities'].__setitem__(1, 2))
        self.reject(lambda rows: rows[1].__setitem__('multiplicity', 2))
        self.reject(lambda rows: rows[1].__setitem__('multiplicity', True))

    def test_coupled_selected_embedding(self):
        def change(rows):
            # Change both the root descriptor and its owning context.
            rows[0]['roots'][1][1][0][1] = -3
            rows[0]['context'][2][0] = copy.deepcopy(rows[0]['roots'][1])
        self.reject(change)
        self.reject(lambda rows: rows[1]['context'].__setitem__(1, 0))
        self.reject(lambda rows: rows[1]['parent'][2].clear())

    def test_arithmetic_and_signs(self):
        self.reject(lambda rows: rows[0]['values'].reverse())
        self.reject(lambda rows: rows[1]['signs'].__setitem__(2, -1))
        self.reject(lambda rows: rows[1]['values'].__setitem__(2, []))
        self.reject(lambda rows: rows[1]['bound'].__setitem__(1, -1))

    def test_literals_and_source_noncoverage(self):
        for value in [True, None, '0', {}]:
            self.reject(lambda rows, value=value: rows[0]['context'].__setitem__(1, value))
        self.reject(lambda rows: rows[2]['cases'].pop())
        self.reject(lambda rows: rows[0]['signs'].__setitem__(0, True))
        for text in ['{"x":1,"x":2}', '[1.0]', '[NaN]']:
            with self.assertRaises(ValueError):
                parse_record(text)


if __name__ == '__main__':
    unittest.main()
