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

    def test_independent_zero_retained(self):
        self.value["remainders"].pop()
        with self.assertRaisesRegex(ValueError, "lost zero"):
            check(self.value)

    def test_independent_wrong_scalar(self):
        path = Path(__file__).resolve().parents[2] / "conformance-fixtures/HexGroebner/matrix.jsonl"
        value = next(json.loads(line)["value"] for line in path.read_text().splitlines()
                     if json.loads(line)["case"] == "p3/full-rank")
        value["remainders"][0] = [c * 2 % 3 for c in value["remainders"][0]]
        with self.assertRaisesRegex(ValueError, "scalar mismatch"):
            check(value)

    def test_independent_false_derivation(self):
        self.value["remainderRefs"][0] = self.value["refs"][0]
        with self.assertRaisesRegex(ValueError, "incorrect row derivation"):
            check(self.value)

    def test_zero_from_wrong_input(self):
        # A dependent reducer and a target both evaluate to zero, but only the
        # target's own coefficient-one derivation proves its reduction.
        trace = self.value["remainderTrace"]
        zero_reducer = next(i for i, node in enumerate(trace) if node[0] == 1)
        self.value["remainderRefs"][0] = zero_reducer
        with self.assertRaisesRegex(ValueError, "mixed target inputs"):
            check(self.value)


if __name__ == "__main__":
    unittest.main()
