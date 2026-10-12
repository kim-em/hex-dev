"""Reject wrong matched sample inputs, sector choices and method bindings."""
import copy
import json
from pathlib import Path
import unittest

from scripts.oracle.real_closure_sample_measurements import verify

FIXTURE = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/sample-measurements.jsonl'


class SampleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = [json.loads(line) for line in FIXTURE.read_text().splitlines()]

    def reject(self, mutate):
        rows = copy.deepcopy(self.rows)
        mutate(rows)
        with self.assertRaises((ValueError, AssertionError, TypeError)):
            verify(rows)

    def test_exact_all_arms(self):
        self.assertEqual(len(verify(self.rows)), 12)

    def test_changed_input(self):
        self.reject(lambda rows: rows[0]['polynomials'][0][0].__setitem__(1, -3))

    def test_false_signs(self):
        self.reject(lambda rows: rows[0].__setitem__('signs', [-1, 1]))

    def test_negative_sector(self):
        def negative(rows):
            rows[1]['value'][1] *= -1
            rows[1]['value_sign'] = -1
        self.reject(negative)

    def test_wrong_dyadic_work(self):
        self.reject(lambda rows: rows[4].__setitem__('dyadic_cuts', 1))

    def test_missing_infinitesimal(self):
        self.reject(lambda rows: rows[2]['value'][0].__setitem__(0, [1, [], [[0, 1, 1]]]))

    def test_wrong_context_depth(self):
        self.reject(lambda rows: rows[2]['context'].__setitem__(1, 0))

    def test_reordered_arms(self):
        self.reject(lambda rows: rows.reverse())

    def test_missing_arm(self):
        self.reject(lambda rows: rows.pop())

    def test_boolean_sign(self):
        self.reject(lambda rows: rows[0].__setitem__('value_sign', True))


if __name__ == '__main__':
    unittest.main()
