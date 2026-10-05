"""Check both raw storage policies and reject changed field values or graphs."""
import copy
import json
from pathlib import Path
import unittest
from scripts.oracle.real_closure_nested_normalization import verify


class ExactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixture = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/nested-normalization.jsonl'
        cls.rows = [json.loads(line) for line in fixture.read_text().splitlines()]

    def test_matched_exact_values(self):
        checked = [verify(row) for row in self.rows]
        self.assertEqual(checked[0]['field_residue'], checked[1]['field_residue'])
        for result in checked:
            self.assertTrue(result['exact_value_checked'])
            self.assertTrue(result['selected_root_sign_checked'])
            self.assertFalse(result['query']['mathematical_replay_checked'])

    def test_changed_inputs(self):
        for source in self.rows:
            for change in ['value', 'head', 'fraction', 'sign', 'steps', 'nodes', 'children']:
                with self.subTest(eager=source['eager'], change=change):
                    row = copy.deepcopy(source)
                    if change == 'value':
                        row['value'][0][0][0] += row['value'][0][0][1]
                    elif change == 'head': row['heads'][0][0] = [4, 1]
                    elif change == 'fraction': row['value'][0][0] = [2, 2]
                    elif change == 'sign': row['sign'] = True
                    elif change == 'steps': row['steps'] = -1
                    elif change == 'nodes': row['query'][1] += 1
                    elif change == 'children': row['query'][2][2][0][1] = [[0, 0]]
                    with self.assertRaises(ValueError): verify(row)


if __name__ == '__main__':
    unittest.main()
