"""Mutation checks for the native algebraic-coefficient differential oracle."""
from __future__ import annotations

import copy
import json
import unittest

from scripts.oracle.common import OracleMismatch
from scripts.oracle.real_closure_trivial import DEFAULT, validate_records, check_record
from scripts.oracle.real_algebraic_flint import Checker
from scripts.oracle.real_algebraic_qqbar import QQBar


class TrivialOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.records = [json.loads(line) for line in DEFAULT.read_text().splitlines() if line]
        cls.q = QQBar()
        cls.checker = Checker(cls.q)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.q.close()

    def record(self, name: str) -> dict:
        return copy.deepcopy(next(r for r in self.records if r["case"] == name))

    def reject(self, record: dict) -> None:
        with self.assertRaises(OracleMismatch):
            check_record(self.checker, record)

    def test_valid(self) -> None:
        validate_records(self.records)
        for record in self.records:
            check_record(self.checker, record)

    def test_missing_case(self) -> None:
        with self.assertRaisesRegex(OracleMismatch, "missing required"):
            validate_records(self.records[:-1])

    def test_duplicate_case(self) -> None:
        with self.assertRaisesRegex(OracleMismatch, "duplicate"):
            validate_records(self.records + self.records[:1])

    def test_boolean_schema(self) -> None:
        records = copy.deepcopy(self.records)
        records[0]["value"]["schema"] = True
        with self.assertRaisesRegex(OracleMismatch, "schema"):
            validate_records(records)

    def test_boolean_multiplicity(self) -> None:
        records = copy.deepcopy(self.records)
        record = next(r for r in records if r["case"] == "dependent linear")
        record["value"]["roots"][0]["multiplicity"] = True
        with self.assertRaisesRegex(OracleMismatch, "multiplicity"):
            validate_records(records)

    def test_wrong_operation(self) -> None:
        records = copy.deepcopy(self.records)
        records[0]["op"] = "algebraicRoots"
        with self.assertRaisesRegex(OracleMismatch, "unexpected"):
            validate_records(records)

    def test_lost_universal_zero(self) -> None:
        record = self.record("zero")
        record["value"]["roots"] = []
        self.reject(record)

    def test_false_universal_constant(self) -> None:
        record = self.record("constant")
        record["value"]["roots"] = None
        self.reject(record)

    def test_missing_root(self) -> None:
        record = self.record("dependent linear")
        record["value"]["roots"] = []
        self.reject(record)

    def test_wrong_root(self) -> None:
        record = self.record("dependent linear")
        record["value"]["roots"][0]["root"] = {
            "poly": [0, 1], "re": [0, 1], "im": [0, 1], "prec": 0}
        self.reject(record)

    def test_wrong_multiplicity(self) -> None:
        record = self.record("mixed algebraic coefficients and multiplicities")
        record["value"]["roots"][0]["multiplicity"] += 1
        self.reject(record)

    def test_wrong_order(self) -> None:
        record = self.record("mixed algebraic coefficients and multiplicities")
        self.assertGreater(len(record["value"]["roots"]), 1)
        record["value"]["roots"].reverse()
        self.reject(record)

    def test_duplicate_root(self) -> None:
        record = self.record("mixed algebraic coefficients and multiplicities")
        record["value"]["roots"][1] = copy.deepcopy(record["value"]["roots"][0])
        self.reject(record)

    def test_wrong_generator(self) -> None:
        record = self.record("dependent linear")
        record["value"]["generators"][1] = {
            "poly": [0, 1], "re": [0, 1], "im": [0, 1], "prec": 0}
        self.reject(record)

    def test_wrong_native_coefficient(self) -> None:
        record = self.record("dependent linear")
        record["value"]["nativeCoefficients"][0] = []
        self.reject(record)

    def test_wrong_native_sign(self) -> None:
        record = self.record("dependent linear")
        record["value"]["nativeCoefficients"][0][1] *= -1
        self.reject(record)

    def test_wrong_coefficient(self) -> None:
        record = self.record("dependent linear")
        record["value"]["coefficients"][0] = {
            "poly": [0, 1], "re": [0, 1], "im": [0, 1], "prec": 0}
        self.reject(record)


if __name__ == "__main__":
    unittest.main()
