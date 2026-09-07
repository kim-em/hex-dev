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
        runs = [dict(arm=arm, export=str(path), accepted=True,
                     source_commit=arm, binary_sha256=arm)
                for arm, path in (("left", BASE), ("right", right))]
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

    def candidate_ranges(self, separated):
        candidate = json.loads(FAST.read_text())
        baseline = compare.read_export(BASE, compare.NAMES)
        for row in candidate["results"]:
            if row["function"] not in compare.HEX_NAMES[-2:]:
                continue
            base = baseline[row["function"]]
            # Improve the median but overlap the baseline unless requested.
            high = base["min_nanos"] - 1 if row["function"] in separated else base["max_nanos"]
            times = [base["min_nanos"] // 2] * 4 + [high]
            for point, nanos in zip(row["points"], times):
                point["total_nanos"] = nanos * point["inner_repeats"]
            row.update(min_nanos=times[0], median_nanos=times[2], max_nanos=times[4])
        path = Path(self.directory.name) / ("candidate-" + str(len(list(Path(self.directory.name).glob('candidate-*')))) + ".json")
        path.write_text(json.dumps(candidate))
        return path

    def test_stricter_gate_preserves_old_verdict(self):
        path = self.candidate_ranges(set())
        pairs = [self.pair(1, path), self.pair(2, path)]
        self.assertTrue(compare.decision(pairs, compare.NAMES)["eligible"])
        self.assertFalse(compare.decision(pairs, compare.NAMES,
                                         require_separated_canonical=True)["eligible"])

    def test_separation_required_for_each_canonical_case(self):
        path = self.candidate_ranges({compare.HEX_NAMES[-2]})
        self.assertFalse(compare.decision([self.pair(1, path), self.pair(2, path)],
                         compare.NAMES, require_separated_canonical=True)["eligible"])

    def test_separation_can_occur_in_different_pairs(self):
        first = self.candidate_ranges({compare.HEX_NAMES[-2]})
        second = self.candidate_ranges({compare.HEX_NAMES[-1]})
        self.assertTrue(compare.decision([self.pair(1, first), self.pair(2, second)],
                        compare.NAMES, require_separated_canonical=True)["eligible"])

    def test_stricter_incomplete_series_has_no_verdict(self):
        self.assertIsNone(compare.decision([self.pair(1)], compare.NAMES,
                                          require_separated_canonical=True)["eligible"])

    def test_invalid_pair_provenance(self):
        edits = [lambda p: p.update(accepted=False),
                 lambda p: p["runs"][0].update(accepted=False),
                 lambda p: p["runs"][0].update(binary_sha256="changed"),
                 lambda p: p["runs"][0].update(source_commit="changed"),
                 lambda p: p["runs"].reverse(),
                 lambda p: p.update(attempt=1)]
        for edit in edits:
            with self.subTest(edit=edit):
                pair = self.pair(2)
                edit(pair)
                with self.assertRaises(ValueError):
                    compare.decision([self.pair(1), pair], compare.NAMES)

    def test_cross_arm_hash_mismatch(self):
        candidate = json.loads(FAST.read_text())
        row = next(r for r in candidate["results"] if r["function"] == compare.HEX_NAMES[-1])
        row.update(observed_hash="0x0", expected_hash_check={"status": "unset"})
        for point in row["points"]:
            point["result_hash"] = "0x0"
        self.path.write_text(json.dumps(candidate))
        verdict = compare.decision([self.pair(1, self.path), self.pair(2, self.path)], compare.NAMES)
        self.assertFalse(verdict["eligible"])

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

    def test_registered_configuration(self):
        for config in ({"repeats": 3}, {"min_total_seconds": 0.1}):
            with self.subTest(config=config):
                self.rejected(lambda sample: sample["results"][0]["config"].update(config))
                self.sample = json.loads(BASE.read_text())
        row = next(r for r in self.sample["results"] if r["function"] == compare.HEX_NAMES[-2])
        self.rejected(lambda _: row["config"].update(max_seconds_per_call=60))

    def test_pari_hex_hash_mismatch(self):
        row = next(r for r in self.sample["results"] if r["function"] == compare.NAMES[8])
        row.update(observed_hash="0x0", expected_hash_check={"status": "unset"})
        for point in row["points"]:
            point["result_hash"] = "0x0"
        self.rejected(lambda _: None)

    def test_expected_hash_failure(self):
        self.rejected(lambda sample: sample["results"][0]["expected_hash_check"].update(status="mismatch"))

    def test_offline_sibling_is_not_idle(self):
        topology = {24: {24, 72}, 25: {25, 73}}
        self.assertEqual(compare.select_core({24: 0, 25: 0, 73: 0}, topology, set()), 25)
        self.assertIsNone(compare.select_core({24: 0}, {24: {24, 72}}, set()))

    def test_busy_threshold_is_strict(self):
        self.assertIsNone(compare.select_core({24: 5, 72: 0}, {24: {24, 72}}, set()))

    def test_avoided_core_is_not_selected(self):
        self.assertIsNone(compare.select_core({24: 0, 72: 0}, {24: {24, 72}}, {24}))


if __name__ == "__main__":
    unittest.main()
