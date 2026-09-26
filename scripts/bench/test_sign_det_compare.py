#!/usr/bin/env python3
"""Reject broken pairing, substituted outcomes and altered comparison summaries."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from scripts.bench.sign_det_compare import ARMS, PARAMS, TRIALS, validate


class PairedValidation(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "samples.jsonl"
        self.inventory = Path(self.temp.name) / "inventory.log"
        self.inventory.write_text("\n".join(json.dumps({"queries": p, "resultHash": 123})
                                              for p in PARAMS))
        self.rows = [{"kind": "header", "schema": "hex-sign-det-paired-v1",
                      "params": PARAMS, "trials": TRIALS, "left": ARMS[0], "right": ARMS[1],
                      "env": {"git_commit": "test-revision", "git_dirty": False}}]
        points = {a: [] for a in ARMS}
        for trial in range(TRIALS):
            for param in PARAMS:
                for arm in (ARMS if trial % 2 == 0 else ARMS[::-1]):
                    point = {"param": param, "trial_index": trial, "status": "ok",
                             "result_hash": "0x7b", "part_of_verdict": True,
                             "below_signal_floor": False, "per_call_nanos": 1000,
                             "inner_repeats": 100}
                    points[arm].append(point)
                    self.rows.append({"kind": "sample", "arm": arm, "point": point})
        for arm in ARMS:
            self.rows.append({"kind": "summary", "result": {
                "function": arm, "kind": "parametric", "hashable": True,
                "budget_truncated": False, "points": copy.deepcopy(points[arm]),
                "env": copy.deepcopy(self.rows[0]["env"]),
                "config": {"param_floor": 1, "param_ceiling": 5, "outer_trials": TRIALS,
                           "param_schedule": {"kind": "custom", "params": PARAMS},
                           "target_inner_nanos": 100000000, "max_seconds_per_call": 60,
                           "signal_floor_multiplier": 1, "cache_mode": "warm"},
                "verdict": "consistent_with_declared_complexity", "complexity_formula": "n",
                "slope": 0, "c_min": 1, "c_max": 1, "advisories": []}})

    def run_validation(self, rows):
        self.path.write_text("\n".join(map(json.dumps, rows)))
        return validate(self.path, self.inventory, "test-revision")

    def test_complete_and_inconclusive_are_retained(self):
        result = self.run_validation(self.rows)
        self.assertEqual(result["paired"][0]["ratios"], [1] * TRIALS)
        self.rows[-1]["result"]["verdict"] = "inconclusive"
        self.assertEqual(self.run_validation(self.rows)["observations"][ARMS[1]]["verdict"],
                         "inconclusive")

    def test_missing_extra_and_reordered_arms(self):
        for rows in (self.rows[:-1], self.rows + [self.rows[-1]],
                     [self.rows[0], self.rows[2], self.rows[1], *self.rows[3:]]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                self.run_validation(rows)

    def test_failed_or_substituted_samples(self):
        for key, value in (("status", "error"), ("result_hash", "0x0"),
                           ("inner_repeats", 0), ("per_call_nanos", float("nan")),
                           ("trial_index", 1), ("below_signal_floor", True)):
            with self.subTest(key=key), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[1]["point"][key] = value
                self.run_validation(rows)

    def test_summary_cannot_replace_raw_measurement(self):
        self.rows[-1]["result"]["points"][0]["per_call_nanos"] = 1
        with self.assertRaises(ValueError):
            self.run_validation(self.rows)

    def test_configuration_and_inventory_must_match(self):
        self.rows[-1]["result"]["config"]["outer_trials"] = 1
        with self.assertRaises(ValueError):
            self.run_validation(self.rows)
        self.inventory.write_text("[]")
        with self.assertRaises((ValueError, TypeError)):
            self.run_validation(self.rows)

    def test_dirty_or_mismatched_revision_fails(self):
        for key, value in (("git_commit", "old-revision"), ("git_dirty", True)):
            with self.subTest(key=key), self.assertRaises(ValueError):
                rows = copy.deepcopy(self.rows)
                rows[0]["env"][key] = value
                self.run_validation(rows)
        rows = copy.deepcopy(self.rows)
        rows[-1]["result"]["env"]["git_dirty"] = True
        with self.assertRaises(ValueError):
            self.run_validation(rows)


if __name__ == "__main__":
    unittest.main()
