#!/usr/bin/env python3
"""Reject substituted height inputs even when the noncryptographic hash agrees."""
import copy
import json
import math
from pathlib import Path
import tempfile
import unittest

from scripts.bench.sign_det_height import HEIGHTS, PHASE_HEIGHTS, expected, phase_expected, validate, validate_phases, validate_export


class HeightValidation(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "inventory.jsonl"
        self.rows = [dict(expected(h), inputHash=1, productionResultHash=1, replayResultHash=2,
                          reducedGraphBytes=100+16*(len(str(2**h-1))-len(str(2**64-1))),
                          directGraphBytes=100) for h in HEIGHTS]

    def check(self, rows):
        self.path.write_text("\n".join(map(json.dumps, rows)))
        return validate(self.path)

    def test_complete(self):
        self.assertEqual(self.check(self.rows), 7)

    def test_changed_evidence(self):
        for field in ("queries", "table", "directTable", "fullTable", "reducedWitnessBits",
                      "directWitnessBits", "graphNodes", "maxColumns", "context"):
            with self.subTest(field=field), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[0][field] = 0
                self.check(rows)

    def test_wrong_byte_growth(self):
        self.rows[2]["reducedGraphBytes"] += 1
        with self.assertRaises(ValueError):
            self.check(self.rows)

    def test_same_hash_changed_height(self):
        self.rows[1] = copy.deepcopy(self.rows[0])
        self.rows[1]["height"] = HEIGHTS[1]
        with self.assertRaises(ValueError):
            self.check(self.rows)

    def test_incomplete_reordered_and_boolean(self):
        for rows in (self.rows[:-1], self.rows[::-1],
                     [dict(self.rows[0], table=[[[True, 1, 1], 1]])] + self.rows[1:]):
            with self.assertRaises(ValueError):
                self.check(rows)


class HeightExportValidation(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "inventory.jsonl"
        rows = [dict(phase_expected(h), inputHash=1, productionResultHash=1, replayResultHash=2)
                for h in PHASE_HEIGHTS]
        self.path.write_text("\n".join(map(json.dumps, rows)))
        self.export = Path(self.temp.name) / "timings.json"
        self.result = {
            "function": "Hex.SignDetBench.Height.runCheck", "kind": "parametric",
            "hashable": True, "budget_truncated": False,
            "env": {"git_commit": "source", "git_dirty": False},
            "config": {"param_floor": 8192, "param_ceiling": 524288,
                       "outer_trials": 6, "target_inner_nanos": 1000000000,
                       "max_seconds_per_call": 10, "signal_floor_multiplier": 10,
                       "cache_mode": "warm", "verdict_warmup_fraction": 0.2,
                       "slope_tolerance": 0.15, "narrow_range_noise_floor": 1.5,
                       "param_schedule": {"kind": "custom", "params": PHASE_HEIGHTS}},
            "points": [{"trial_index": t, "param": h, "status": "ok",
                        "result_hash": "0x2", "part_of_verdict": True, "below_signal_floor": False,
                        "per_call_nanos": 10000, "inner_repeats": 100}
                       for t in range(6) for h in PHASE_HEIGHTS],
            "verdict": "inconclusive", "complexity_formula": "height",
            "slope": -0.5, "c_min": 1, "c_max": 2, "advisories": []}

    def check_export(self, result):
        self.export.write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
        return validate_export(self.export, "Height.runCheck", self.path, "source")

    def test_symbolic_phase_oracle(self):
        self.assertEqual(validate_phases(self.path), 7)
        rows = [json.loads(line) for line in self.path.read_text().splitlines()]
        for key, value in [("head", "X^3+1"), ("coefficient", "2^height"),
                           ("queryDegrees", [True, 1, 0]), ("steps", False),
                           ("coefficientBytes", 42), ("productionResultHash", -1)]:
            changed = copy.deepcopy(rows)
            changed[0][key] = value
            self.path.write_text("\n".join(map(json.dumps, changed)))
            with self.subTest(key=key), self.assertRaises(ValueError):
                validate_phases(self.path)
        self.path.write_text("\n".join(map(json.dumps, rows)))

    def test_inconclusive_is_retained(self):
        self.assertEqual(self.check_export(self.result)["verdict"], "inconclusive")

    def test_wrong_source_protocol_and_result(self):
        for key, value in [("env", {"git_commit": "old", "git_dirty": False}),
                           ("env", {"git_commit": "source", "git_dirty": True}),
                           ("function", "Hex.SignDetBench.Height.runReduce"),
                           ("budget_truncated", True), ("verdict", "pass")]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                result = copy.deepcopy(self.result)
                result[key] = value
                self.check_export(result)
        result = copy.deepcopy(self.result)
        result["config"]["outer_trials"] = 2
        with self.assertRaises(ValueError):
            self.check_export(result)

    def test_missing_reordered_and_duplicated_samples(self):
        points = self.result["points"]
        for changed in [points[:-1], points[::-1], [points[0], points[0]] + points[2:]]:
            result = dict(self.result, points=changed)
            with self.assertRaises(ValueError):
                self.check_export(result)

    def test_invalid_sample_values(self):
        for key, value in [("result_hash", "0x1"), ("status", "timeout"),
                           ("part_of_verdict", False), ("below_signal_floor", True), ("trial_index", False),
                           ("per_call_nanos", math.inf), ("per_call_nanos", -1),
                           ("per_call_nanos", True), ("inner_repeats", True)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                result = copy.deepcopy(self.result)
                result["points"][0][key] = value
                self.check_export(result)


if __name__ == "__main__":
    unittest.main()
