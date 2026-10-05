"""Reject coupled changes to printed expressions and their reconstruction data."""
import copy
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_closure_repr import argument, lean_checks, parse_record, verify


class ReprTests(unittest.TestCase):
    def setUp(self):
        path = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/repr.jsonl'
        self.rows = [parse_record(line) for line in path.read_text().splitlines() if line.strip()]

    def reject_coupled(self, index, change):
        rows = copy.deepcopy(self.rows)
        row = rows[index]
        packet = argument(row)
        change(packet)
        row['packet_text'] = json.dumps(packet)
        row['representation'] = '(Hex.RealClosure.Tower.' + row['reader'] + (' parent ' if row['reader'].startswith('Context.') else ' catalog ') + \
            json.dumps(row['packet_text']) + ')'
        with self.assertRaises(ValueError):
            verify(rows)

    def test_actual_code_and_values(self):
        self.assertEqual(verify(self.rows), 11)
        generated = lean_checks(self.rows)
        source = Path(__file__).resolve().parents[2] / 'conformance/HexRealClosure/ReprChecks.lean'
        self.assertEqual(generated, source.read_text())

    def test_expression_and_quoting(self):
        for change in [lambda row: row.__setitem__('reader', 'Catalog.restorePolynomialText!' ),
                       lambda row: row.__setitem__('representation', row['representation'][1:-1]),
                       lambda row: row.__setitem__('representation', row['representation'].replace(' catalog ', ' parent ')),
                       lambda row: row.__setitem__('packet_text', '[]')]:
            rows = copy.deepcopy(self.rows)
            change(rows[0])
            with self.assertRaises(ValueError):
                verify(rows)
        for text in ['{"x":1,"x":2}', '[1.0]', '[NaN]']:
            with self.assertRaises(ValueError):
                parse_record(text)

    def test_rational_and_selected_semantics(self):
        self.reject_coupled(0, lambda p: p[1].__setitem__(1, 2))
        self.reject_coupled(1, lambda p: p[1][0].__setitem__(1, -3))
        self.reject_coupled(4, lambda p: p[1][1][1][0].__setitem__(1, 7))
        self.reject_coupled(5, lambda p: p[0][2].clear())
        self.reject_coupled(5, lambda p: p[1].__setitem__(1, 1))
        self.reject_coupled(8, lambda p: p[1][1][0].__setitem__(1, 2))

    def test_infinitesimal_order_and_arithmetic(self):
        self.reject_coupled(9, lambda p: p[0].__setitem__(1, 1))
        # Change the constant numerator of epsilon2^-1 from one to two.
        self.reject_coupled(9, lambda p: p[1][1][0][1][0].__setitem__(1, 2))
        self.reject_coupled(10, lambda p: p[1].__setitem__(0, 1))

    def test_escaped_literals_and_provider_names(self):
        rows = copy.deepcopy(self.rows)
        rows[-1]['literals'][0]['codepoints'][0] = 92
        with self.assertRaises(ValueError):
            verify(rows)
        rows = copy.deepcopy(self.rows)
        entry = rows[-2]['rejections'][3]
        entry['expression'] = entry['expression'].replace('17', '18')
        with self.assertRaises(ValueError):
            verify(rows)
        rows = copy.deepcopy(self.rows)
        rows[-2]['rejections'][0]['expression'] = '(Except.error "wrong reconstruction expression")'
        with self.assertRaises(ValueError):
            verify(rows)

    def test_strict_leaves_and_required_rejections(self):
        for value in [True, None, '1', {}]:
            self.reject_coupled(0, lambda p, value=value: p[1].__setitem__(1, value))
        rows = copy.deepcopy(self.rows)
        rows[-2]['rejections'].pop()
        with self.assertRaises(ValueError):
            verify(rows)


if __name__ == '__main__':
    unittest.main()
