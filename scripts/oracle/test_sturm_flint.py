#!/usr/bin/env python3
"""Acceptance/refusal controls for the pinned direct Sturm oracle."""
import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.common import OracleMismatch
from scripts.oracle.sturm_flint import check_record


class SturmOracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = ROOT / "conformance-fixtures/HexSturm/sturm.jsonl"
        cls.records = {r["case"]: r for r in map(json.loads, path.read_text(encoding="utf-8").splitlines())}

    def test_valid_and_invalid_domains(self):
        for name in ("two-roots/0", "constant/0", "zero-head/0", "repeated-head/0",
                     "two-roots/4", "two-roots/8", "two-roots/10", "noncanonical/0"):
            with self.subTest(case=name):
                check_record(self.records[name])

    def test_corrupted_outputs(self):
        for key, value in (("query", [3, 0, -2, 0, -1, 0, 2, 0]),
                           ("query", []), ("root_count", 1), ("prepared", False),
                           ("prepared_count", 1), ("producer_replay", [False] * 8),
                           ("prepared_replay", [1] * 8)):
            with self.subTest(field=key, value=value):
                changed = copy.deepcopy(self.records["two-roots/0"])
                changed["value"]["result"][key] = value
                with self.assertRaises(OracleMismatch):
                    check_record(changed)

    def test_corrupted_integer_agreement(self):
        changed = copy.deepcopy(self.records["two-roots/1"])
        changed["value"]["integer_count"] = 1
        with self.assertRaises(OracleMismatch):
            check_record(changed)

    def test_corrupted_storage(self):
        changed = copy.deepcopy(self.records["noncanonical/0"])
        changed["value"]["raw_head"] = []
        with self.assertRaises(OracleMismatch):
            check_record(changed)

    def test_false_success_on_invalid_domain(self):
        changed = copy.deepcopy(self.records["zero-head/0"])
        changed["value"]["result"]["prepared"] = True
        with self.assertRaises(OracleMismatch):
            check_record(changed)


if __name__ == "__main__":
    unittest.main()
