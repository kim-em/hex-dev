"""Independent exact checks reject wrong roots, embeddings and multiplicities."""
import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.real_closure_number_field import check


class NumberFieldTests(unittest.TestCase):
    def rows(self):
        return [json.loads(line) for line in
                (ROOT / 'conformance-fixtures/HexRealClosure/number-field.jsonl').read_text().splitlines()]

    def test_original_and_case_inventory(self):
        rows = self.rows()
        self.assertEqual(check(rows)['cases'], 5)
        for changed in [rows[:-1], rows+[rows[1]], [rows[0], rows[1], rows[1]]]:
            with self.assertRaises(ValueError): check(changed)

    def test_semantic_mutations(self):
        mutations = [
            lambda rs: rs[1]['output']['entries'].pop(),
            lambda rs: rs[1]['output']['entries'].reverse(),
            lambda rs: rs[1]['output']['entries'][0].__setitem__('multiplicity', 1),
            lambda rs: rs[1]['output']['entries'][0]['query_signs'].__setitem__(0, 1),
            lambda rs: rs[1].__setitem__('generator_sign', -1),
            lambda rs: rs[1].__setitem__('generator_head', [-3,0,0,1]),
            lambda rs: rs[0].__setitem__('output', {'kind':'finite','entries':[]}),
        ]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                rows = copy.deepcopy(self.rows()); mutate(rows)
                with self.assertRaises(ValueError): check(rows)

    def test_selected_embedding_and_original_inputs(self):
        rows = self.rows()
        middle = next(r for r in rows if r['case'] == 'middle cubic embedding')
        # Both the selected middle root and the largest conjugate are positive.
        # Changing only the real isolating interval must still be rejected.
        middle['generator_lower'], middle['generator_upper'] = [3,2], [8,5]
        with self.assertRaisesRegex(ValueError, 'generator isolating interval'): check(rows)
        rows = self.rows()
        middle = next(r for r in rows if r['case'] == 'middle cubic embedding')
        middle['output'] = copy.deepcopy(rows[1]['output'])
        with self.assertRaises(ValueError): check(rows)
        for field in ('head','queries'):
            rows = self.rows()
            if field == 'head': rows[2][field] = []
            else: rows[2][field][0] = []
            with self.assertRaises(ValueError): check(rows)

    def test_descriptor_and_arithmetic_mutations(self):
        mutations = [
            lambda r: r.__setitem__('context', 7),
            lambda r: r.__setitem__('lower', [2]),
            lambda r: r.__setitem__('indices', [0]),
            lambda r: r.__setitem__('signs', [3]),
            lambda r: r.__setitem__('head', []),
            lambda r: r.__setitem__('inverse_sign', 1),
            lambda r: r.__setitem__('inverse_identity_sign', 1),
            lambda r: r.__setitem__('inverse_shift_sign', 0),
        ]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                rows = self.rows()
                root = next(e['root'] for e in rows[1]['output']['entries'] if e['root']['kind']=='selected')
                mutate(root)
                with self.assertRaises(ValueError): check(rows)

    def test_common_field_inputs_and_point_branch(self):
        mutations = [
            lambda r: r['inputs'][0].__setitem__('head', [-3,0,1]),
            lambda r: r['inputs'][1].__setitem__('lower', [-2,1]),
            lambda r: r['coordinates'].reverse(),
            lambda r: r['coordinates'][0].clear(),
            lambda r: r['output']['entries'][1].__setitem__('multiplicity', 2),
            lambda r: r['output']['entries'][1]['root'].__setitem__('value', [[1,1]]),
        ]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                rows = self.rows()
                row = next(r for r in rows if r['case'] == 'common quadratic fields with zero root')
                mutate(row)
                with self.assertRaises(ValueError): check(rows)


if __name__ == '__main__': unittest.main()
