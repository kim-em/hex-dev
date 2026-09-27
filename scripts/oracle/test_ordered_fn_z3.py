"""Regression checks for rejecting incorrect infinitesimal results."""

import copy
import json
import unittest

from scripts.oracle.ordered_fn_z3 import DEFAULT, OracleMismatch, check_record


class OrderedFnOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = {r["case"]: r for r in map(json.loads, DEFAULT.read_text().splitlines())}

    def test_fixtures(self):
        for record in self.records.values():
            with self.subTest(case=record["case"]):
                check_record(record)

    def test_wrong_sign(self):
        record = copy.deepcopy(self.records["level1/sign/1"])
        record["value"] = -1
        with self.assertRaises(OracleMismatch):
            check_record(record)

    def test_wrong_tower_order(self):
        record = copy.deepcopy(self.records["level2/compare/1"])
        record["value"] *= -1
        with self.assertRaises(OracleMismatch):
            check_record(record)

    def test_fabricated_difference(self):
        record = copy.deepcopy(self.records["level2/compare/1"])
        record["difference"] = record["left"]
        with self.assertRaises(OracleMismatch):
            check_record(record)

    def test_wrong_normalization(self):
        record = copy.deepcopy(self.records["normalize/3/-3"])
        record["value"] = self.records["level1/sign/1"]["input"]
        with self.assertRaises(OracleMismatch):
            check_record(record)

    def test_zero_denominator(self):
        record = copy.deepcopy(self.records["level1/sign/1"])
        record["input"]["den"] = []
        with self.assertRaises(OracleMismatch):
            check_record(record)

    def test_wrong_depth(self):
        record = copy.deepcopy(self.records["level2/sign/1"])
        record["depth"] = 1
        with self.assertRaises(OracleMismatch):
            check_record(record)


if __name__ == "__main__":
    unittest.main()
