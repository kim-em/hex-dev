"""Reject generating sets that fail reduced-basis, ideal or order obligations."""
import copy
import json
from pathlib import Path
import unittest
import subprocess
import sys

from scripts.oracle.groebner_sympy import check
from scripts.oracle.groebner_corpus import validate_corpus


class GroebnerOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexGroebner/f4.jsonl"
        cls.records = list(map(json.loads, path.read_text().splitlines()))
        cls.cases = {r["case"]: r["value"] for r in cls.records}

    def test_complete_scheduling_profiles(self):
        unique = validate_corpus(self.records)
        self.assertEqual(len(unique), 567)
        self.assertTrue(all(r["value"]["scheduling"] == "degree" for r in unique))

    def test_missing_scheduling_case(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            validate_corpus(self.records[:-1])

    def test_duplicate_scheduling_case(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            validate_corpus(self.records + self.records[:1])

    def test_incompatible_scheduling_problem(self):
        rows = copy.deepcopy(self.records)
        next(r for r in rows if r["value"]["scheduling"] == "sugar")["value"]["p"] = 3
        with self.assertRaisesRegex(ValueError, "scheduling changes p"):
            validate_corpus(rows)

    def test_wrong_scheduling_metadata(self):
        rows = copy.deepcopy(self.records)
        rows[0]["value"]["scheduling"] = "sugar"
        with self.assertRaisesRegex(ValueError, "scheduling case mismatch"):
            validate_corpus(rows)

    def test_missing_scheduling_metadata(self):
        rows = copy.deepcopy(self.records)
        del rows[0]["value"]["scheduling"]
        with self.assertRaisesRegex(ValueError, "missing scheduling metadata"):
            validate_corpus(rows)

    def test_invalid_sugar_header(self):
        rows = copy.deepcopy(self.records)
        next(r for r in rows if r["value"]["scheduling"] == "sugar")["op"] = "other"
        with self.assertRaisesRegex(ValueError, "invalid F4 record header"):
            validate_corpus(rows)

    def test_optimized_validation(self):
        result = subprocess.run([sys.executable, "-O", "-c",
            "from scripts.oracle.groebner_corpus import validate_corpus; validate_corpus([])"],
            capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("ValueError: incomplete scheduling corpus", result.stderr)

    def test_valid_basis(self):
        check(self.cases["p3/grevlex/missing-s-pair"])

    def test_all_orders_and_field_widths(self):
        for prime in (2, 251, 257, 65521, 65537, 2147483647):
            for order in ("lex", "grlex", "grevlex"):
                with self.subTest(prime=prime, order=order):
                    check(self.cases[f"p{prime}/{order}/missing-s-pair"])

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
