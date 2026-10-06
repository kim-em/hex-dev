"""Reject corrupted workflow results, bindings and measurement schedules."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from scripts.bench.sign_det_maximal_workflow import validate_export


class WorkflowTest(unittest.TestCase):
    def test_reject_mutations(self):
        r = {"function": "Hex.SignDetBench.maximalOne", "kind": "fixed", "hashable": True,
             "hashes_agree": True, "budget_truncated": False, "observed_hash": "0x7",
             "env": {"git_commit": "a" * 40, "git_dirty": False},
             "config": {"warmup_first_iter": False, "warmup": True, "repeats": 1,
                        "min_total_seconds": 0.1, "max_seconds_per_call": 30,
                        "expected_hash": None}, "median_nanos": 100,
             "points": [{"status": "ok", "repeat_index": 0, "result_hash": "0x7",
                         "inner_repeats": 10, "total_nanos": 1000}]}
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "export.json"
            def check(row):
                p.write_text(json.dumps({"export_schema_version": 1, "results": [row]}))
                return validate_export(p, "maximalOne", 7, "a" * 40)
            self.assertEqual(check(r), 100)
            mutations = [("observed_hash", "0x8"), ("budget_truncated", True),
                         ("median_nanos", 101), ("points", []), ("hashes_agree", False)]
            for key, value in mutations:
                bad = copy.deepcopy(r); bad[key] = value
                with self.subTest(key=key), self.assertRaises(ValueError): check(bad)
            for section, key, value in (("env", "git_dirty", True), ("env", "git_commit", "b" * 40),
                                        ("config", "repeats", 2)):
                bad = copy.deepcopy(r); bad[section][key] = value
                with self.subTest(key=key), self.assertRaises(ValueError): check(bad)
            for key, value in (("status", "error"), ("result_hash", "0x8"),
                               ("inner_repeats", 0), ("total_nanos", -1)):
                bad = copy.deepcopy(r); bad["points"][0][key] = value
                with self.subTest(key=key), self.assertRaises(ValueError): check(bad)


if __name__ == "__main__":
    unittest.main()
