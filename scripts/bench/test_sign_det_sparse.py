#!/usr/bin/env python3
"""Reject incomplete schedules and silent failed benchmark outputs."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from scripts.bench.sign_det_sparse import inventory_hashes, validate_export


class ExportValidation(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "export.json"
        self.params = [64, 128, 256, 512, 1024, 2048]
        self.expected = {p: {"productionResultHash": 123, "replayResultHash": 1}
                         for p in self.params}
        self.result = {
            "function": "Hex.SignDetBench.runProduce", "kind": "parametric",
            "hashable": True, "budget_truncated": False,
            "env": {"git_commit": "deadbeef", "git_dirty": False},
            "config": {"param_floor": 64, "param_ceiling": 2048, "outer_trials": 6,
                       "target_inner_nanos": 100000000, "max_seconds_per_call": 10,
                       "signal_floor_multiplier": 1, "cache_mode": "warm",
                       "verdict_warmup_fraction": 0.2, "slope_tolerance": 0.15,
                       "narrow_range_noise_floor": 1.5,
                       "param_schedule": {"kind": "custom", "params": self.params}},
            "points": [{"trial_index": t, "param": p, "status": "ok",
                        "part_of_verdict": True, "result_hash": "0x7b",
                        "per_call_nanos": 1000000, "inner_repeats": 100}
                       for t in range(6) for p in self.params],
            "verdict": "consistent_with_declared_complexity",
            "complexity_formula": "s * (Nat.log2 s + 1)", "slope": 0,
            "c_min": 100, "c_max": 110, "advisories": []}

    def validate(self, result, name="runProduce"):
        self.path.write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
        return validate_export(self.path, name, self.expected, "deadbeef")

    def test_complete_and_inconclusive_are_retained(self):
        self.validate(self.result)
        self.result["verdict"] = "inconclusive"
        self.assertEqual(self.validate(self.result)["verdict"], "inconclusive")

    def test_replay_requires_true_output(self):
        self.result["function"] = "Hex.SignDetBench.runGraph"
        for p in self.result["points"]:
            p["result_hash"] = "0x1"
        self.validate(self.result, "runGraph")
        self.result["points"][0]["result_hash"] = "0x0"
        with self.assertRaises(ValueError):
            self.validate(self.result, "runGraph")

    def test_invalid_samples(self):
        for key, value in (("result_hash", "0x0"), ("result_hash", None),
                           ("status", "error"), ("status", "timed_out"),
                           ("part_of_verdict", False), ("per_call_nanos", 0),
                           ("per_call_nanos", float("nan")), ("inner_repeats", 0)):
            with self.subTest(key=key, value=value):
                result = copy.deepcopy(self.result)
                result["points"][0][key] = value
                with self.assertRaises(ValueError):
                    self.validate(result)

    def test_missing_duplicate_and_reordered_samples(self):
        points = self.result["points"]
        for changed in (points[:-1], points + [points[0]], list(reversed(points)),
                        [points[1]] + points[1:]):
            with self.subTest(points=changed):
                result = dict(self.result, points=changed)
                with self.assertRaises(ValueError):
                    self.validate(result)

    def test_wrong_schedule_and_truncation(self):
        result = copy.deepcopy(self.result)
        result["config"]["outer_trials"] = 1
        with self.assertRaises(ValueError):
            self.validate(result)
        with self.assertRaises(ValueError):
            self.validate(dict(self.result, budget_truncated=True))
        result = copy.deepcopy(self.result)
        result["config"]["slope_tolerance"] = 0.30
        with self.assertRaises(ValueError):
            self.validate(result)

    def test_binary_source_binding(self):
        for changed in ({"git_commit": "other", "git_dirty": False},
                        {"git_commit": "deadbeef", "git_dirty": True}):
            with self.subTest(env=changed):
                result = copy.deepcopy(self.result)
                result["env"] = changed
                with self.assertRaises(ValueError):
                    self.validate(result)

    def test_component_hashes_are_separate(self):
        for name in ("runQueries", "runProducts", "runMatrices", "runSolvers", "runSigns"):
            with self.subTest(name=name):
                for row in self.expected.values():
                    row[name] = 123
                result = copy.deepcopy(self.result)
                result["function"] = "Hex.SignDetBench." + name
                self.validate(result, name)
                result["points"][0]["result_hash"] = "0x1"
                with self.assertRaises(ValueError):
                    self.validate(result, name)

    def test_inventory_rejects_missing_parameter_or_invalid_hash(self):
        rows = [{"queries": p, "productionResultHash": 123,
                 "replayResultHash": 1, "inputHash": 99} for p in self.params]
        self.path.write_text("\n".join(map(json.dumps, rows)))
        self.assertEqual(len(inventory_hashes(self.path)), 6)
        self.path.write_text("\n".join(map(json.dumps, rows[:-1])))
        with self.assertRaises(ValueError):
            inventory_hashes(self.path)
        rows[0]["productionResultHash"] = True
        self.path.write_text("\n".join(map(json.dumps, rows)))
        with self.assertRaises(ValueError):
            inventory_hashes(self.path)


if __name__ == "__main__":
    unittest.main()
