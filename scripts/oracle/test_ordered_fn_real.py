"""Adversarial checks for the real-refinement oracle."""
import copy
import json
import unittest

from scripts.oracle.common import OracleMismatch
from scripts.oracle.ordered_fn_real import DEFAULT, check_record


class RealOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = [json.loads(line) for line in DEFAULT.read_text().splitlines()]

    def sample(self, case):
        return copy.deepcopy(next(r for r in self.records if r["case"] == case))

    def test_fixtures(self):
        for record in self.records:
            with self.subTest(case=record["case"]):
                check_record(record)

    def reject(self, record):
        with self.assertRaises(OracleMismatch):
            check_record(record)

    def test_changed_source_expression(self):
        record = self.sample("positive/false/8")
        record["expression"] = ["rat", [1, 1]]
        self.reject(record)

    def test_wrong_canonical_fraction(self):
        record = self.sample("degree/false/8")
        record["num"][0] = [1, 1]
        self.reject(record)

    def test_cancelled_divisor_guard(self):
        record = self.sample("cancelled-pole/false/8")
        self.assertEqual(record["total_sign"], 1)
        self.assertIsNone(record["guarded_sign"])
        record["guarded_sign"] = 1
        self.reject(record)

    def test_forged_source_regularity(self):
        record = self.sample("cancelled-pole/true/8")
        record["source_regular"] = True
        self.reject(record)

    def test_wrong_subject(self):
        record = self.sample("positive/false/8")
        record["subject"] = [3, 1]
        self.reject(record)

    def test_wrong_request(self):
        record = self.sample("positive/false/8")
        record["request"] = [1, 8]
        self.reject(record)

    def test_unrefined_coefficient(self):
        record = self.sample("positive/true/8")
        record["coeff_num"][0] = [[-2, 1], [0, 1]]
        self.reject(record)

    def test_fabricated_horner_bound(self):
        record = self.sample("degree/true/8")
        record["num_bound"] = [[0, 1], [1, 1]]
        self.reject(record)

    def test_wrong_sign(self):
        record = self.sample("negative-denominator/false/8")
        record["attempt"] = 1
        self.reject(record)

    def test_boolean_sign(self):
        record = self.sample("positive/false/8")
        record["attempt"] = True
        self.reject(record)

    def test_pole_success(self):
        record = self.sample("pole/false/8")
        record["finite"] = 1
        self.reject(record)

    def test_skipped_first_approximation(self):
        record = self.sample("positive/false/12")
        record["total_approx"] = record["approx_attempt"]
        self.reject(record)

    def test_default_total_sign(self):
        record = self.sample("near-zero/true/12")
        record["total_sign"] = 0
        self.reject(record)


if __name__ == "__main__":
    unittest.main()
