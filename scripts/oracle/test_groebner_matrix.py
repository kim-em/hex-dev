"""Ensure the independent oracle rejects lost row spaces and false provenance."""
import copy
import json
from pathlib import Path
import unittest

from scripts.oracle.groebner_matrix import check


class MatrixOracleTests(unittest.TestCase):
    def setUp(self):
        path = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexGroebner/matrix.jsonl"
        self.value = next(json.loads(line)["value"] for line in path.read_text().splitlines()
                          if json.loads(line)["case"] == "p3/dependent")

    def test_accept(self):
        check(self.value)

    def test_wrong_space_same_rank(self):
        self.value["rows"][0][-1] = (self.value["rows"][0][-1] + 1) % 3
        with self.assertRaisesRegex(ValueError, "different row spaces"):
            check(self.value)

    def test_wrong_input_space(self):
        self.value["reducers"][0][-1] = 0
        with self.assertRaises(ValueError):
            check(self.value)

    def test_forward_reference(self):
        self.value["trace"][0] = [2, 0, 1]
        with self.assertRaisesRegex(ValueError, "forward or invalid reference"):
            check(self.value)

    def test_false_derivation(self):
        ref = self.value["refs"][0]
        node = self.value["trace"][ref]
        self.assertEqual(node[0], 2)
        node[-1] = 3 - node[-1]
        with self.assertRaisesRegex(ValueError, "incorrect row derivation"):
            check(self.value)

    def test_bad_origin(self):
        self.value["fromTarget"][0] = True
        with self.assertRaisesRegex(ValueError, "reducer rank"):
            check(self.value)

    def test_bad_reference(self):
        for ref in (-1, len(self.value["trace"]), None):
            value = copy.deepcopy(self.value)
            value["refs"][0] = ref
            with self.assertRaisesRegex(ValueError, "invalid output reference"):
                check(value)


if __name__ == "__main__":
    unittest.main()
