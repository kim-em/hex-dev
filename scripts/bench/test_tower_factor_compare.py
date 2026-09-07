# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison
"""Adversarial checks for fixed-case export admission and retention."""

import copy
import json
from pathlib import Path
import tempfile
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tower_factor_compare as compare

REPORTS = Path(__file__).resolve().parents[2] / "reports" / "bench-results"
BASE = REPORTS / "hex-number-field-tower-followup-modular-6-left.json"
FAST = REPORTS / "hex-number-field-tower-followup-modular-6-right.json"


class TowerFactorCompareTests(unittest.TestCase):
    def setUp(self):
        self.sample = json.loads(BASE.read_text())
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "export.json"

    def rejected(self, edit):
        edit(self.sample)
        self.path.write_text(json.dumps(self.sample))
        with self.assertRaises(ValueError):
            compare.read_export(self.path, compare.NAMES)

    def pair(self, number, right=FAST):
        runs = [dict(arm="left", export=str(BASE)), dict(arm="right", export=str(right))]
        if number == 2:
            runs.reverse()
        return dict(attempt=number, runs=runs, accepted=True)

    def test_real_export_and_retention(self):
        self.assertEqual(len(compare.read_export(BASE, compare.NAMES)), 15)
        verdict = compare.decision([self.pair(1), self.pair(2)], compare.NAMES)
        self.assertTrue(verdict["eligible"])
        self.assertEqual(len(verdict["checks"]), 16)

    def test_incomplete_series_has_no_verdict(self):
        verdict = compare.decision([self.pair(1)], compare.NAMES)
        self.assertFalse(verdict["complete"])
        self.assertIsNone(verdict["eligible"])

    def test_unchanged_canonical_cost_does_not_qualify(self):
        verdict = compare.decision([self.pair(1, BASE), self.pair(2, BASE)], compare.NAMES)
        self.assertFalse(verdict["eligible"])

    def test_disjoint_rung_regression_rejects_otherwise_faster_candidate(self):
        candidate = json.loads(FAST.read_text())
        row = candidate["results"][0]
        for point in row["points"]:
            point["total_nanos"] *= 10
        times = sorted(p["total_nanos"] // p["inner_repeats"] for p in row["points"])
        row.update(min_nanos=times[0], median_nanos=times[2], max_nanos=times[4])
        self.path.write_text(json.dumps(candidate))
        verdict = compare.decision([self.pair(1, self.path), self.pair(2, self.path)], compare.NAMES)
        self.assertFalse(verdict["eligible"])

    def test_missing_case(self):
        self.rejected(lambda sample: sample["results"].pop())

    def test_duplicate_case(self):
        self.rejected(lambda sample: sample["results"].__setitem__(-1, copy.deepcopy(sample["results"][0])))

    def test_missing_repeat(self):
        self.rejected(lambda sample: sample["results"][0]["points"].pop())

    def test_inconsistent_repeat_hash(self):
        self.rejected(lambda sample: sample["results"][0]["points"][0].update(result_hash="0x0"))

    def test_forged_summary(self):
        self.rejected(lambda sample: sample["results"][0].update(median_nanos=1))

    def test_truncated_budget(self):
        self.rejected(lambda sample: sample["results"][0].update(budget_truncated=True))

    def test_disabled_warmup(self):
        self.rejected(lambda sample: sample["results"][0]["config"].update(warmup=False))

    def test_expected_hash_failure(self):
        self.rejected(lambda sample: sample["results"][0]["expected_hash_check"].update(status="mismatch"))

    def test_offline_sibling_is_not_idle(self):
        topology = {24: {24, 72}, 25: {25, 73}}
        self.assertEqual(compare.select_core({24: 0, 25: 0, 73: 0}, topology, set()), 25)
        self.assertIsNone(compare.select_core({24: 0}, {24: {24, 72}}, set()))

    def test_busy_threshold_is_strict(self):
        self.assertIsNone(compare.select_core({24: 5, 72: 0}, {24: {24, 72}}, set()))


if __name__ == "__main__":
    unittest.main()
