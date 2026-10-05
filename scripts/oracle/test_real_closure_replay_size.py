"""Reject changed inputs, graph references and reported size claims."""
import copy
import json
from pathlib import Path
import unittest
from scripts.oracle.real_closure_replay_size import check_rows, verify


class Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/replay-size.jsonl'
        cls.rows = [json.loads(line) for line in path.read_text().splitlines()]

    def test_full_family(self):
        results = check_rows(self.rows)['rows']
        for r in results:
            n = r['queries_count']
            self.assertEqual(r['tree_occurrences'], 2 * n - 1)
            self.assertEqual(r['dag_nodes'], n.bit_length() if r['repeated'] else 2 * n - 1)
            self.assertEqual(r['dag_edges'], 2 * (n.bit_length() - 1) if r['repeated'] else 2 * n - 2)

    def test_changed_inputs(self):
        for original in self.rows:
            for kind in ['head', 'query', 'sign', 'nodes', 'edges', 'occurrences', 'unchecked']:
                row = copy.deepcopy(original)
                if kind == 'head': row['head'] = []
                elif kind == 'query': row['queries'][0] = []
                elif kind == 'sign': row['signs'][0] *= -1
                elif kind == 'unchecked': row['replayed'] = False
                else:
                    key = {'nodes': 'dag_nodes', 'edges': 'dag_edges', 'occurrences': 'tree_occurrences'}[kind]
                    row[key] += 1
                with self.subTest(depth=original['depth'], n=original['queries_count'], kind=kind):
                    with self.assertRaises(ValueError): verify(row)

    def test_changed_graph(self):
        original = next(r for r in self.rows if r['queries_count'] == 4 and r['repeated'])
        for kind in ['cycle', 'binding', 'slice', 'unreachable', 'context']:
            row = copy.deepcopy(original)
            root, entries = row['graph'][1:]
            if kind == 'cycle': entries[root][1] = [[root, root]]
            elif kind == 'binding': entries[0][0][1] = []
            elif kind == 'slice': entries[root][0][4][0] = []
            elif kind == 'context':
                for entry in entries: entry[0][0] = [1]
            else: entries.append(copy.deepcopy(entries[0])); row['dag_nodes'] += 1
            with self.subTest(kind=kind):
                with self.assertRaises(ValueError): verify(row)

    def test_input_cached_sign(self):
        for original in self.rows:
            if original['depth'] == 2:
                row = copy.deepcopy(original)
                row['queries'][0][1][1] *= -1
                with self.assertRaises(ValueError): verify(row)

    def test_family_coverage(self):
        for rows in [self.rows[:-1], self.rows + self.rows[:1]]:
            with self.assertRaises(ValueError): check_rows(rows)


if __name__ == '__main__':
    unittest.main()
