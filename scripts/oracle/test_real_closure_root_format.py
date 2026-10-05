"""Coupled packet mutations must not hide changes in root semantics."""
import copy
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_closure_root_format import parse_record, verify


class RootFormatTests(unittest.TestCase):
    def setUp(self):
        path = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/root-format.jsonl'
        self.rows = [parse_record(line) for line in path.read_text().splitlines() if line.strip()]

    def reject_coupled(self, index, mutate):
        rows = copy.deepcopy(self.rows)
        mutate(rows[index]['packet'])
        rows[index]['reconstructed'] = copy.deepcopy(rows[index]['packet'])
        rows[index]['packet_text'] = json.dumps(rows[index]['packet'])
        binding, payload = rows[index]['packet']
        rows[index]['root_texts'] = [json.dumps([binding, entry[0]]) for entry in payload[1]]
        with self.assertRaises(ValueError):
            verify(rows)

    def test_actual_roots(self):
        self.assertEqual(verify(self.rows), 6)

    def test_multiplicity_and_literal_order(self):
        self.reject_coupled(5, lambda p: p[1][1][0].__setitem__(1, 2))
        self.reject_coupled(2, lambda p: p[1][1].reverse())
        self.reject_coupled(5, lambda p: p[1][1].pop())
        self.reject_coupled(0, lambda p: p[1].__setitem__(0, 1))

    def test_selected_embedding_and_predecessor(self):
        # Both fresh and original packets are changed together.
        self.reject_coupled(3, lambda p: p[1][1][0][0][1][1][0].__setitem__(1, 7))
        self.reject_coupled(4, lambda p: p[0][2].clear())
        self.reject_coupled(4, lambda p: p[1][1][0][0][1][3][1][0][0].__setitem__(1, 1))
        self.reject_coupled(2, lambda p: p[1][1][0][0][1].__setitem__(1, 3))

    def test_strict_literals_and_actual_rejections(self):
        for leaf in [True, None, '1', {}]:
            self.reject_coupled(5, lambda p, leaf=leaf: p[1][1][0].__setitem__(1, leaf))
        rows = copy.deepcopy(self.rows)
        rows[0]['rejections'].pop()
        with self.assertRaises(ValueError):
            verify(rows)
        for text in ['{"x":1,"x":2}', '[1.0]', '[NaN]']:
            with self.assertRaises(ValueError):
                parse_record(text)


if __name__ == '__main__':
    unittest.main()
