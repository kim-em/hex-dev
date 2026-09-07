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

    def pair(self, number, right=FAST, *, strict=False, windows=1, max_busy=None):
        cpu, sibling = 24 + number, 72 + number
        loads = {cpu: 0.0, sibling: 1.0}
        runs = [dict(arm=arm, export=str(path), accepted=True,
                     source_commit=arm, binary_sha256=arm,
                     command=["taskset", "-c", str(cpu), "/saved/bench", "run"] + compare.NAMES,
                     preflight=loads.copy(), postflight=loads.copy(),
                     during=[{cpu: 100.0, sibling: 1.0}], sibling_mean={sibling: 1.0},
                     exit_code=0, export_error=None)
                for arm, path in (("left", BASE), ("right", right))]
        if number == 2:
            runs.reverse()
        whole = {0: 0.0, 48: 0.0, **loads}
        for run in runs:
            run["preflight_all"] = whole.copy()
        return dict(attempt=number, runs=runs, accepted=True, cpu=cpu,
                    siblings=[cpu, sibling], cpu_ids=list(whole),
                    preflight_windows=[whole.copy() for _ in range(windows)],
                    require_separated_canonical=strict, quiet_windows=windows,
                    max_busy_cpus=max_busy)

    def test_real_export_and_retention(self):
        self.assertEqual(len(compare.read_export(BASE, compare.NAMES)), 15)
        verdict = compare.decision([self.pair(1), self.pair(2)], compare.NAMES)
        self.assertTrue(verdict["eligible"])
        self.assertEqual(len(verdict["checks"]), 16)

    def test_committed_series_reproduce_with_host_audit(self):
        directory = REPORTS / "tower-singleton-quadratic"
        decisions = sorted(directory.glob("*-decision.json"))
        self.assertGreaterEqual(len(decisions), 7)
        for path in decisions:
            with self.subTest(series=path.name):
                saved = json.loads(path.read_text())
                stem = path.name.removesuffix("-decision.json")
                pairs = [json.loads((directory / f"{stem}-{n}-host.json").read_text())
                         for n in saved["accepted_pairs"]]
                for pair in pairs:
                    for run in pair["runs"]:
                        run["export"] = str(REPORTS.parents[1] / run["export"])
                names = pairs[0]["names"] if pairs else compare.HEX_NAMES
                actual = compare.decision(pairs, names,
                    require_separated_canonical=saved["require_separated_canonical"],
                    quiet_windows=saved.get("quiet_windows", 1),
                    max_busy_cpus=saved.get("max_busy_cpus"))
                self.assertEqual(actual, {k: saved[k] for k in actual})

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
        for pair in pairs:
            pair["require_separated_canonical"] = True
        self.assertFalse(compare.decision(pairs, compare.NAMES,
                                         require_separated_canonical=True)["eligible"])

    def test_separation_required_for_each_canonical_case(self):
        path = self.candidate_ranges({compare.HEX_NAMES[-2]})
        self.assertFalse(compare.decision([self.pair(1, path, strict=True), self.pair(2, path, strict=True)],
                         compare.NAMES, require_separated_canonical=True)["eligible"])

    def test_separation_can_occur_in_different_pairs(self):
        first = self.candidate_ranges({compare.HEX_NAMES[-2]})
        second = self.candidate_ranges({compare.HEX_NAMES[-1]})
        self.assertTrue(compare.decision([self.pair(1, first, strict=True), self.pair(2, second, strict=True)],
                        compare.NAMES, require_separated_canonical=True)["eligible"])

    def test_stricter_incomplete_series_has_no_verdict(self):
        self.assertIsNone(compare.decision([self.pair(1, strict=True)], compare.NAMES,
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

    def test_host_admission_recomputed_from_samples(self):
        edits = {
            "busy preflight": lambda p: p["runs"][0]["preflight"].update({p["cpu"]: 5}),
            "busy postflight": lambda p: p["runs"][0]["postflight"].update({p["siblings"][1]: 5}),
            "forged mean": lambda p: p["runs"][0]["sibling_mean"].update({p["siblings"][1]: 0}),
            "busy during": lambda p: p["runs"][0]["during"][0].update({p["siblings"][1]: 5}),
            "missing during": lambda p: p["runs"][0].update(during=[]),
            "missing sibling": lambda p: p["runs"][0]["during"][0].pop(p["siblings"][1]),
            "nonfinite telemetry": lambda p: p["runs"][0]["postflight"].update({p["cpu"]: float("nan")}),
            "wrong affinity": lambda p: p["runs"][0]["command"].__setitem__(2, "99"),
            "failed process": lambda p: p["runs"][0].update(exit_code=1),
            "invalid export": lambda p: p["runs"][0].update(export_error="missing case"),
            "wrong benchmarks": lambda p: p.update(names=compare.HEX_NAMES),
        }
        for label, edit in edits.items():
            with self.subTest(label=label):
                pair = self.pair(1)
                edit(pair)
                with self.assertRaises(ValueError):
                    compare.decision([pair], compare.NAMES)

    def test_busy_sibling_rejected_with_consistent_mean(self):
        pair = self.pair(1)
        sibling = pair["siblings"][1]
        pair["runs"][0]["during"][0][sibling] = 5.0
        pair["runs"][0]["sibling_mean"][sibling] = 5.0
        with self.assertRaises(ValueError):
            compare.decision([pair], compare.NAMES)

    def test_recorded_quiet_windows_rechecked(self):
        pair = self.pair(1, windows=15)
        self.assertIsNone(compare.decision([pair], compare.NAMES, quiet_windows=15)["eligible"])
        pair["preflight_windows"][0][pair["siblings"][1]] = 5.0
        with self.assertRaises(ValueError):
            compare.decision([pair], compare.NAMES, quiet_windows=15)
        pair["preflight_windows"].pop(0)
        with self.assertRaises(ValueError):
            compare.decision([pair], compare.NAMES, quiet_windows=15)

    def test_protocol_flags_cannot_be_reinterpreted(self):
        for pair in (self.pair(1, strict=True), self.pair(1, windows=15)):
            with self.subTest(pair=pair):
                with self.assertRaises(ValueError):
                    compare.decision([pair], compare.NAMES)
        with self.assertRaises(ValueError):
            compare.decision([self.pair(1), self.pair(2, strict=True)], compare.NAMES)

    def test_global_ceiling_applies_to_each_window(self):
        cpus = [0, 1, 2]
        rotating = [{0: 5, 1: 0, 2: 0}, {0: 0, 1: 5, 2: 0}]
        self.assertTrue(compare.quiet_host(rotating, 2, cpus, 1))
        rotating[0][2] = 5
        self.assertFalse(compare.quiet_host(rotating, 2, cpus, 1))
        self.assertFalse(compare.quiet_host(rotating[:1], 2, cpus, 1))
        self.assertFalse(compare.quiet_host([{0: 0, 1: 0}], 1, cpus, 0))

    def test_global_history_is_rechecked(self):
        pair = self.pair(1, windows=2, max_busy=1)
        self.assertIsNone(compare.decision([pair], compare.NAMES,
            quiet_windows=2, max_busy_cpus=1)["eligible"])
        pair["preflight_windows"][0].update({0: 100, 48: 100})
        with self.assertRaisesRegex(ValueError, "busy whole host"):
            compare.decision([pair], compare.NAMES, quiet_windows=2, max_busy_cpus=1)

    def test_between_arm_global_preflight_is_rechecked(self):
        pair = self.pair(1, max_busy=1)
        pair["runs"][1]["preflight_all"].update({0: 100, 48: 100})
        with self.assertRaisesRegex(ValueError, "busy whole host"):
            compare.decision([pair], compare.NAMES, max_busy_cpus=1)

    def test_global_preflight_must_match_selected_core(self):
        pair = self.pair(1, max_busy=1)
        pair["runs"][0]["preflight_all"][pair["cpu"]] = 1
        with self.assertRaisesRegex(ValueError, "inconsistent"):
            compare.decision([pair], compare.NAMES, max_busy_cpus=1)

    def test_global_ceiling_cannot_be_reinterpreted(self):
        with self.assertRaises(ValueError):
            compare.decision([self.pair(1, max_busy=1)], compare.NAMES)
        with self.assertRaises(ValueError):
            compare.decision([self.pair(1)], compare.NAMES, max_busy_cpus=1)

    def test_serialized_cpu_keys(self):
        pair = json.loads(json.dumps(self.pair(1)))
        self.assertIsNone(compare.decision([pair], compare.NAMES)["eligible"])

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

    def test_quiet_history_must_be_complete(self):
        self.assertEqual(compare.quiet_load([{24: 0, 72: 0}], 2), {})

    def test_earlier_busy_window_blocks_selection(self):
        history = [{24: 0, 72: 5}, {24: 0, 72: 0}]
        self.assertIsNone(compare.select_core(compare.quiet_load(history, 2),
                                             {24: {24, 72}}, set()))
        history.append({24: 0, 72: 0})
        self.assertEqual(compare.select_core(compare.quiet_load(history, 2),
                                             {24: {24, 72}}, set()), 24)

    def test_missing_cpu_in_any_quiet_window_blocks_selection(self):
        history = [{24: 0}, {24: 0, 72: 0}]
        self.assertEqual(compare.quiet_load(history, 2)[72], 100.0)

    def test_busy_threshold_is_strict(self):
        self.assertIsNone(compare.select_core({24: 5, 72: 0}, {24: {24, 72}}, set()))

    def test_avoided_core_is_not_selected(self):
        self.assertIsNone(compare.select_core({24: 0, 72: 0}, {24: {24, 72}}, {24}))


if __name__ == "__main__":
    unittest.main()
