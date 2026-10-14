"""Reject incomplete root sets, wrong multiplicities and forged exact presentations."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import unittest

from scripts.oracle.real_closure_trivial_measurements import verify

FIXTURE = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/trivial-measurements.jsonl'


class TrivialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = [json.loads(line) for line in FIXTURE.read_text().splitlines()]

    def reject(self, mutate):
        rows = copy.deepcopy(self.rows)
        mutate(rows)
        with self.assertRaises((ValueError, AssertionError, TypeError)):
            verify(rows)

    def test_exact_all_routes(self):
        self.assertEqual(len(verify(self.rows)), 12)

    def test_cli_stdin_matches_file(self):
        script = Path(__file__).with_name('real_closure_trivial_measurements.py')
        command = [sys.executable, str(script)]
        piped = subprocess.run(command, input=FIXTURE.read_text(), text=True,
                               capture_output=True, check=True)
        named = subprocess.run(command + [str(FIXTURE)], text=True,
                               capture_output=True, check=True)
        self.assertEqual(piped.stdout, named.stdout)
        self.assertEqual(json.loads(piped.stdout)['verified_arms'], 12)

    def test_lost_all(self):
        self.reject(lambda rows: rows[0].__setitem__('roots', []))

    def test_constant_all(self):
        self.reject(lambda rows: rows[2].__setitem__('roots', None))

    def test_missing_root(self):
        self.reject(lambda rows: rows[4]['roots'].pop())

    def test_wrong_order(self):
        self.reject(lambda rows: rows[4]['roots'].reverse())

    def test_wrong_multiplicity(self):
        self.reject(lambda rows: rows[10]['roots'][0].__setitem__('multiplicity', 1))

    def test_forged_polynomial(self):
        self.reject(lambda rows: rows[4]['roots'][0].__setitem__('polynomial', [-3, 0, 1]))

    def test_changed_input(self):
        self.reject(lambda rows: rows[4]['coefficients'][0].__setitem__(0, -3))

    def test_missing_route(self):
        self.reject(lambda rows: rows.pop())

    def test_boolean_label(self):
        self.reject(lambda rows: rows[4]['roots'][0].__setitem__('multiplicity', True))


class DistinctTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixture = FIXTURE.with_name('trivial-distinct.jsonl')
        cls.rows = [json.loads(line) for line in fixture.read_text().splitlines()]

    def reject(self, mutate):
        rows = copy.deepcopy(self.rows)
        mutate(rows)
        with self.assertRaises((ValueError, AssertionError, TypeError)):
            verify(rows, "distinct")

    def test_exact_growing_families(self):
        results = verify(self.rows, "distinct")
        self.assertEqual(len(results), 16)
        self.assertEqual([row['distinct_roots'] for row in results[::2]], [2, 4, 6, 8]*2)
        self.assertEqual({row['family'] for row in results}, {'rational', 'quadratic'})

    def test_missing_route(self):
        self.reject(lambda rows: rows.pop())

    def test_changed_family(self):
        self.reject(lambda rows: rows[0].__setitem__('family', 'quadratic'))

    def test_changed_count(self):
        self.reject(lambda rows: rows[0].__setitem__('root_count', 4))

    def test_changed_input(self):
        self.reject(lambda rows: rows[0]['coefficients'][0].__setitem__(0, 3))

    def test_trailing_zero(self):
        self.reject(lambda rows: rows[0]['coefficients'].append([0, 1]))

    def test_wrong_order(self):
        self.reject(lambda rows: rows[14]['roots'].reverse())

    def test_missing_root(self):
        self.reject(lambda rows: rows[14]['roots'].pop())

    def test_wrong_multiplicity(self):
        self.reject(lambda rows: rows[14]['roots'][0].__setitem__('multiplicity', 2))

    def test_forged_polynomial(self):
        self.reject(lambda rows: rows[8]['roots'][0].__setitem__('polynomial', [-3, 0, 1]))

    def test_canonical_forged_root(self):
        self.reject(lambda rows: rows[9]['roots'][0].__setitem__('polynomial', [-3, 0, 1]))

    def test_canonical_wrong_sign(self):
        self.reject(lambda rows: rows[9]['roots'][0].__setitem__('sign', 1))

    def test_wrong_explicit_suite(self):
        with self.assertRaises(AssertionError):
            verify(self.rows, 'multiplicity')

    def test_distinct_cli(self):
        script = Path(__file__).with_name('real_closure_trivial_measurements.py')
        result = subprocess.run([sys.executable, str(script), '--suite', 'distinct'],
            input='\n'.join(json.dumps(row) for row in self.rows), text=True,
            capture_output=True, check=True)
        self.assertEqual(json.loads(result.stdout)['verified_arms'], 16)

    def test_irrational_point(self):
        def mutate(rows):
            rows[8].update(generic_points=1, generic_selected=1)
        self.reject(mutate)

    def test_paired_native_counts(self):
        self.reject(lambda rows: rows[1].update(generic_points=2, generic_selected=0))

    def test_boolean_count(self):
        self.reject(lambda rows: rows[0].__setitem__('generic_points', True))


if __name__ == '__main__':
    unittest.main()
