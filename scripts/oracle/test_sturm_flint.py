#!/usr/bin/env python3
"""Acceptance/refusal controls for the pinned direct Sturm oracle."""
import copy
import json
import io
import tempfile
from contextlib import redirect_stdout, redirect_stderr
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.common import OracleMismatch
from scripts.oracle.sturm_flint import check_record, check


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
                           ("prepared_count", 1), ("prepared_query", []),
                           ("reduced_query", []), ("retargeted_count", 1),
                           ("certificate_values", []), ("wrong_value_replay", [True] * 8), ("producer_replay", [False] * 8),
                           ("prepared_replay", [1] * 8)):
            with self.subTest(field=key, value=value):
                changed = copy.deepcopy(self.records["two-roots/0"])
                changed["value"]["result"][key] = value
                with self.assertRaises(OracleMismatch):
                    check_record(changed)

    def test_corrupted_integer_agreement(self):
        changed = copy.deepcopy(self.records["two-roots/1"])
        changed["value"]["integer"][0] = 1
        with self.assertRaises(OracleMismatch):
            check_record(changed)

    def test_corrupted_storage(self):
        changed = copy.deepcopy(self.records["noncanonical/0"])
        changed["value"]["raw_head"][0][0][0] += 1
        with self.assertRaises(OracleMismatch):
            check_record(changed)

    def test_false_success_on_invalid_domain(self):
        changed = copy.deepcopy(self.records["zero-head/0"])
        changed["value"]["result"]["prepared"] = True
        with self.assertRaises(OracleMismatch):
            check_record(changed)

    def test_raw_query_and_endpoint_corruption(self):
        for field in ("raw_queries", "raw_lower"):
            changed = copy.deepcopy(self.records["noncanonical/1"])
            if field == "raw_queries":
                changed["value"][field][0][0][0][0] += 1
            else:
                changed["value"][field][0][0] += 1
            with self.subTest(field=field), self.assertRaises(OracleMismatch):
                check_record(changed)

    def test_header_and_fixed_input_corruption(self):
        for location, field, value in (("record", "lib", "HexSignDet"),
                                       ("value", "seed", 1), ("value", "schema", True),
                                       ("value", "head", []), ("value", "queries", []),
                                       ("value", "storage", "noncanonical")):
            changed = copy.deepcopy(self.records["two-roots/0"])
            target = changed if location == "record" else changed["value"]
            target[field] = value
            with self.subTest(field=field), self.assertRaises(OracleMismatch):
                check_record(changed)
        changed = copy.deepcopy(self.records["noncanonical/0"])
        changed["value"]["storage"] = "rational"
        with self.assertRaises(OracleMismatch):
            check_record(changed)

    def test_integer_type_corruption(self):
        for value in (True, 2.0):
            changed = copy.deepcopy(self.records["two-roots/1"])
            changed["value"]["integer"][0] = value
            with self.subTest(value=value), self.assertRaises(OracleMismatch):
                check_record(changed)

    def test_missing_and_duplicate_stream_cases(self):
        records = list(self.records.values())
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "cases.jsonl"
            for name, modified in (("missing", records[1:]),
                                   ("duplicate", records + [records[0]])):
                path.write_text("".join(json.dumps(r) + "\n" for r in modified), encoding="utf-8")
                with self.subTest(stream=name), redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                    if name == "missing":
                        with self.assertRaises(OracleMismatch):
                            check(path, Path(tmp))
                    else:
                        self.assertEqual(check(path, Path(tmp)), 1)


if __name__ == "__main__":
    unittest.main()
