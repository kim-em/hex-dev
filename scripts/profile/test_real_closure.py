"""Validate retained benchmark rows before profiling attribution."""
import sys
from pathlib import Path
import unittest
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parent))
from factor_sampling_profile import analyse
from scripts.profile.real_closure import measurement_rows, validate_measurement

class MeasurementTests(unittest.TestCase):
    def test_schema_string_hash_and_clean_commit(self):
        row = {"status": "ok", "result_hash": "0x1", "function": "Hex.RealClosure.Bench.runMetiSecond", "param": 3, "profile_kernel": True, "env": {"git_commit": "abc", "git_dirty": False}}
        self.assertIs(validate_measurement([row], "abc", "second"), row)
        self.assertEqual(measurement_rows('noise\n{"status":"ok"}\n'), [{"status": "ok"}])
        for update in ({"function": "other"}, {"param": 5}, {"profile_kernel": False}, {"result_hash": 1}, {"result_hash": "0x0"}, {"status": "error"},
                       {"env": {"git_commit": "other", "git_dirty": False}},
                       {"env": {"git_commit": "abc", "git_dirty": True}}):
            with self.subTest(update=update), self.assertRaises(RuntimeError):
                validate_measurement([{**row, **update}], "abc", "second")
        for rows in ([], [row, row]):
            with self.assertRaises(RuntimeError):
                validate_measurement(rows, "abc", "second")

class RankingTests(unittest.TestCase):
    def test_equal_inclusive_shares_have_stable_name_order(self):
        thread = {"samples": {"length": 2, "stack": [0, 1]},
                  "stackTable": {"frame": [0, 1, 2], "prefix": [2, 2, None]}}
        names = [(s, s) for s in ("Hex.Z", "Hex.A", "Hex.Root")]
        with patch('factor_sampling_profile.main_thread', return_value=thread), \
             patch('factor_sampling_profile.frame_names', return_value=names):
            summary = analyse({}, None, 20)
        self.assertEqual(summary['top_inclusive'], [
            {"function": "Hex.Root", "percent": 100.0},
            {"function": "Hex.A", "percent": 50.0},
            {"function": "Hex.Z", "percent": 50.0}])
        self.assertEqual(summary['inclusive_hex'], summary['top_inclusive'])

if __name__ == "__main__":
    unittest.main()
