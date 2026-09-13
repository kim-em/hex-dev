"""Mutation checks for the complete field inverse/solve oracle contracts."""
from __future__ import annotations

from copy import deepcopy
from pathlib import Path
import unittest

from scripts.oracle.common import read_fixtures, split_fixtures_results
from scripts.oracle.matrix_flint import _field_check


class FieldOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[2]
        cls.inputs, results = split_fixtures_results(read_fixtures(
            root / "conformance-fixtures/HexRowReduce/rowreduce.jsonl"))
        cls.results = [r for r in results if r["op"].startswith("field-")]

    def check_value(self, result, value):
        _field_check(self.inputs[(result["lib"], result["case"])], value, result["op"])

    def test_committed_outputs(self):
        for result in self.results:
            with self.subTest(case=result["case"], op=result["op"]):
                self.check_value(result, result["value"])

    def test_false_singularity_including_empty(self):
        for result in self.results:
            if result["op"] == "field-inverse" and result["value"] is not None:
                with self.subTest(case=result["case"]), self.assertRaises(ValueError):
                    self.check_value(result, None)

    def test_zero_separators_rejected(self):
        zeros = {"Rat": [0, 1], "ZMod64": 0, "RationalFn": [[], [[1, 1]]]}
        for result in self.results:
            if result["op"] != "field-solve" or "error" not in result["value"]:
                continue
            record = self.inputs[(result["lib"], result["case"])]
            value = {"error": [zeros[record["carrier"]]] * record["n"]}
            with self.subTest(case=result["case"]), self.assertRaises(ValueError):
                self.check_value(result, value)

    def test_dependent_bases_rejected(self):
        # Duplicating a basis column keeps A*N=0 but destroys completeness.
        for result in self.results:
            if result["op"] != "field-solve" or not result["case"].endswith("leading-free"):
                continue
            value = deepcopy(result["value"])
            for row in value["basis"]:
                row[1] = deepcopy(row[0])
            with self.subTest(case=result["case"]), self.assertRaises(ValueError):
                self.check_value(result, value)

    def test_rectangular_shape_not_inferred_from_empty_rows(self):
        for result in self.results:
            if result["op"] != "field-solve" or not result["case"].endswith("no-equations"):
                continue
            value = deepcopy(result["value"])
            value["basis"] = []
            with self.subTest(case=result["case"]), self.assertRaises(ValueError):
                self.check_value(result, value)


if __name__ == "__main__":
    unittest.main()
