"""Exact root-oracle and malformed-inventory checks for the untimed supplement."""
import copy
from fractions import Fraction
import json
from pathlib import Path
import tempfile
import unittest
from scripts.bench.sign_det_shared_root_work import compare_bound, selected, validate

FIXTURE = Path(__file__).resolve().parents[2] / 'reports/data/sign-det-shared-root-work/validated/inputs.log'


class SharedRootWorkTests(unittest.TestCase):
    def setUp(self):
        self.rows = [json.loads(s) for s in FIXTURE.read_text().splitlines()]

    def check_rows(self, rows):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / 'inputs.log'
            path.write_text(''.join(json.dumps(r) + '\n' for r in rows))
            return validate(path)

    def test_native_inventory(self):
        self.assertEqual(len(self.check_rows(self.rows)), 3)

    def test_wrong_order(self):
        self.rows[0]['strictOrder'] = 'gt'
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_ambiguous_interval(self):
        self.rows[0]['leftInterval'] = [[-2, 1], [2, 1]]
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_empty_interval(self):
        self.rows[0]['leftInterval'] = [[0, 1], [1, 1]]
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_root_endpoint(self):
        self.rows[0]['lastInterval'] = [[3, 1], [4, 1]]
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_changed_selected_root(self):
        self.rows[0]['leftInterval'] = [[-2, 1], [0, 1]]
        self.rows[0]['sameInterval'] = [[-2, 1], [0, 1]]
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_boolean_endpoint(self):
        self.rows[0]['leftInterval'][0][0] = False
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_wrong_moment_sum(self):
        self.rows[0]['totalTableMoments'] += 1
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_wrong_product_identity(self):
        self.rows[0]['factor'][0][0] *= 2
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_scalar_gcd_normalization(self):
        rows = copy.deepcopy(self.rows)
        for r in rows:
            for factor_key, head_key in [('factor','commonHead'), ('strictFactor','strictCommonHead')]:
                r[factor_key] = [[2*a,b] for a,b in r[factor_key]]
                r[head_key] = [[a,2*b] for a,b in r[head_key]]
        self.assertEqual(len(self.check_rows(rows)), 3)

    def test_endpoint_root_with_one_interior_root(self):
        self.rows[1]['lastInterval'] = [[3, 1], [5, 1]]
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_wrong_last_head(self):
        self.rows[0]['lastHead'] = self.rows[0]['left']
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_wrong_strict_common_product(self):
        self.rows[0]['strictFactor'][0][0] *= 2
        with self.assertRaises(ValueError): self.check_rows(self.rows)

    def test_negative_sqrt_bounds(self):
        self.assertEqual(compare_bound(('sqrt', -1), Fraction(-3,2)), 1)
        self.assertEqual(compare_bound(('sqrt', -1), Fraction(-1)), -1)
        self.assertEqual(selected([('sqrt', -1), ('sqrt', 1)], [[-3,2],[-1,1]]), ('sqrt', -1))

    def test_close_positive_sqrt_bounds(self):
        self.assertEqual(selected([('sqrt', -1), ('sqrt', 1)], [[7,5],[3,2]]), ('sqrt', 1))


if __name__ == '__main__':
    unittest.main()
