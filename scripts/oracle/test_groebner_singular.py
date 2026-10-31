"""Adversarial checks for the independent Singular basis oracle."""
import copy
import shutil
import tempfile
import unittest
from unittest.mock import patch

from scripts.oracle.groebner_singular import polynomial, run


class Parsing(unittest.TestCase):
    def test_signed_residues(self):
        self.assertEqual(polynomial("x0^2-x1+5x0", 2, 7),
                         [((0, 1), 6), ((1, 0), 5), ((2, 0), 1)])

    def test_reject_syntax(self):
        for text in ["system('bad')", "x2", "(x0+1)"]:
            with self.assertRaises(ValueError):
                polynomial(text, 2, 7)


@unittest.skipUnless(shutil.which("Singular"), "Singular is an if_available oracle")
class IndependentChecks(unittest.TestCase):
    def setUp(self):
        self.binary = shutil.which("Singular")
        self.record = {"case": "adversarial", "value": {
            "p": 7, "variables": 2, "order": "grevlex",
            "generators": [[[[2, 0], 1], [[0, 1], 6]], [[[1, 1], 1], [[0, 0], 6]]],
            "basis": [[[[2, 0], 1], [[0, 1], 6]], [[[1, 1], 1], [[0, 0], 6]],
                      [[[0, 2], 1], [[1, 0], 6]]]}}

    def reject(self, record):
        with tempfile.TemporaryDirectory() as directory, \
                patch("scripts.oracle.groebner_singular.write_failure", return_value=directory):
            with self.assertRaisesRegex(ValueError, "different reduced basis"):
                run([record], self.binary)

    def test_accept(self):
        self.assertEqual(run([self.record], self.binary), 1)

    def test_missing_s_pair(self):
        record = copy.deepcopy(self.record)
        record["value"]["basis"].pop()
        self.reject(record)

    def test_wrong_ideal(self):
        record = copy.deepcopy(self.record)
        record["value"]["basis"] = [[[[0, 0], 1]]]
        self.reject(record)

    def test_formal_f2(self):
        self.reject({"case": "formal-f2", "value": {"p": 2, "variables": 1,
            "order": "grevlex", "generators": [[[[2], 1]]], "basis": [[[[1], 1]]]}})

    def test_zero_variable_cancellation(self):
        self.assertEqual(run([{"case": "constant-zero", "value": {
            "p": 7, "variables": 0, "order": "lex",
            "generators": [[[[], 1], [[], 6]]], "basis": []}}], self.binary), 1)


if __name__ == "__main__":
    unittest.main()
