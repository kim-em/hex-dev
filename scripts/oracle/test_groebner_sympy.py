"""Reject generating sets that fail reduced-basis, ideal or order obligations."""
import copy
import json
from pathlib import Path
import unittest

from scripts.oracle.groebner_sympy import check


class GroebnerOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexGroebner/f4.jsonl"
        cls.cases = {r["case"]: r["value"] for r in map(json.loads, path.read_text().splitlines())}

    def test_valid_basis(self):
        check(self.cases["p3/grevlex/missing-s-pair"])

    def test_missing_s_pair(self):
        value = copy.deepcopy(self.cases["p3/grevlex/missing-s-pair"])
        value["basis"] = value["basis"][:2]
        with self.assertRaisesRegex(ValueError, "different reduced basis"):
            check(value)

    def test_wrong_ideal(self):
        value = copy.deepcopy(self.cases["p3/grevlex/missing-s-pair"])
        value["basis"] = [[[[0, 0], 1]]]
        with self.assertRaises(ValueError):
            check(value)

    def test_wrong_order(self):
        value = copy.deepcopy(self.cases["p3/grevlex/missing-s-pair"])
        value["order"] = "lex"
        with self.assertRaises(ValueError):
            check(value)

    def test_nonmonic(self):
        value = copy.deepcopy(self.cases["p3/grevlex/missing-s-pair"])
        value["basis"][0][0][1] = 2
        with self.assertRaises(ValueError):
            check(value)

    def test_formal_characteristic_two(self):
        value = copy.deepcopy(self.cases["p2/grevlex/ordinary-f2"])
        value["basis"] = [[[[1, 0], 1], [[0, 1], 1]]]
        with self.assertRaises(ValueError):
            check(value)

    def test_zero_ideal(self):
        value = copy.deepcopy(self.cases["p3/lex/empty"])
        value["basis"] = [[[[0, 0], 1]]]
        with self.assertRaises(ValueError):
            check(value)


if __name__ == "__main__":
    unittest.main()
