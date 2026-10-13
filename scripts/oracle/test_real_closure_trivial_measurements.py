"""Reject incomplete root sets, wrong Yun labels and forged exact presentations."""
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


if __name__ == '__main__':
    unittest.main()
