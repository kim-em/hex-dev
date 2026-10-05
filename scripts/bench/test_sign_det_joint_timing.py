"""Reject corrupted outputs and schedules in joint-query scientific records."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.bench import sign_det_joint_timing as timing


class JointTimingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name)/"records.json"
        self.expected = {n: {key: 100+i for i, key in enumerate(sorted(set(timing.RESULT_KEYS.values())))}
                         for n in timing.DEGREES}
        self.env = {"git_commit": "measured", "git_dirty": False}

    def result(self, name):
        return {"function": timing.PREFIX+name, "kind": "parametric", "hashable": True,
                "budget_truncated": False, "env": self.env, "config": timing.CONFIG,
                "complexity_formula": "n^3", "verdict": "inconclusive", "slope": 3,
                "c_min": 1, "c_max": 2, "advisories": [], "points": [
                    {"trial_index": trial, "param": n, "status": "ok",
                     "result_hash": hex(self.expected[n][timing.RESULT_KEYS[name]]),
                     "part_of_verdict": True, "below_signal_floor": False,
                     "per_call_nanos": n**3, "inner_repeats": 1,
                     "peak_rss_kb": 1000, "alloc_bytes": None}
                    for trial in range(timing.TRIALS) for n in timing.DEGREES]}

    def pair(self, names=("runReduced", "runDirect")):
        results = [self.result(name) for name in names]
        rows = [{"kind": "header", "schema": "hex-sign-det-paired-v1", "params": timing.DEGREES,
                 "trials": timing.TRIALS, "left": timing.PREFIX+names[0],
                 "right": timing.PREFIX+names[1], "env": self.env}]
        for trial in range(timing.TRIALS):
            for slot, _n in enumerate(timing.DEGREES):
                for arm in ((0, 1) if trial % 2 == 0 else (1, 0)):
                    rows.append({"kind": "sample", "arm": timing.PREFIX+names[arm],
                                 "point": results[arm]["points"][trial*len(timing.DEGREES)+slot]})
        rows.extend({"kind": "summary", "result": r} for r in results)
        return names, rows

    def validate_pair(self, names, rows):
        self.path.write_text("\n".join(map(json.dumps, rows)))
        return timing.validate_pair(self.path, names, self.expected, "measured")

    def test_complete_pairs_retain_inconclusive_verdicts(self):
        names, rows = self.pair()
        summary = self.validate_pair(names, rows)
        self.assertEqual(len(rows), 63)
        self.assertEqual(summary["observations"][names[0]]["verdict"], "inconclusive")
        self.assertEqual(len(summary["paired"]), 5)
        self.assertEqual(summary["paired"][0]["ratios"], [1]*6)

    def test_wider_protocol_rejects_old_schedule_and_preserves_model(self):
        name = "runComparison"
        expected = {n: {key: 100+i for i, key in enumerate(sorted(set(timing.RESULT_KEYS.values())))}
                    for n in timing.WIDE_DEGREES}
        result = self.result(name)
        result["config"] = timing.WIDE_CONFIG
        result["points"] = [dict(result["points"][0], param=n, trial_index=trial,
                                 per_call_nanos=n**3)
                            for trial in range(timing.TRIALS) for n in timing.WIDE_DEGREES]
        timing.validate_result(result, name, expected, "measured",
                               degrees=timing.WIDE_DEGREES, config=timing.WIDE_CONFIG)
        with self.assertRaisesRegex(ValueError, "registered schedule"):
            timing.validate_result(result, name, expected, "measured")
        altered = copy.deepcopy(result)
        altered["config"]["slope_tolerance"] = 0.5
        with self.assertRaisesRegex(ValueError, "registered schedule"):
            timing.validate_result(altered, name, expected, "measured",
                                   degrees=timing.WIDE_DEGREES, config=timing.WIDE_CONFIG)
        altered = copy.deepcopy(result)
        altered["points"][0]["param"] = 3
        with self.assertRaisesRegex(ValueError, "scientific observations"):
            timing.validate_result(altered, name, expected, "measured",
                                   degrees=timing.WIDE_DEGREES, config=timing.WIDE_CONFIG)

    def test_missing_reordered_or_duplicated_arms_rejected(self):
        names, rows = self.pair()
        for alter in (lambda rs: rs.pop(1), lambda rs: rs.insert(1, rs[1]),
                      lambda rs: rs.__setitem__(slice(1, 3), rs[1:3][::-1])):
            with self.subTest(alter=alter), self.assertRaises(ValueError):
                changed = copy.deepcopy(rows)
                alter(changed)
                self.validate_pair(names, changed)

    def test_wrong_results_memory_and_probe_substitution_rejected(self):
        for key, value in (("result_hash", "0xc"), ("status", "timed_out"),
                           ("part_of_verdict", False), ("below_signal_floor", True),
                           ("per_call_nanos", float("nan")), ("inner_repeats", True),
                           ("param", 3.0), ("trial_index", False),
                           ("peak_rss_kb", None), ("alloc_bytes", 100)):
            with self.subTest(key=key), self.assertRaises(ValueError):
                result = self.result("runComparison")
                result["points"][0][key] = value
                timing.validate_result(result, "runComparison", self.expected, "measured")

    def test_summary_binding_config_and_model_rejected(self):
        for key, value in (("budget_truncated", True), ("function", "wrong"),
                           ("complexity_formula", "n^2"), ("verdict", "unknown")):
            with self.subTest(key=key), self.assertRaises(ValueError):
                result = self.result("runCompletion")
                result[key] = value
                timing.validate_result(result, "runCompletion", self.expected, "measured")
        names, rows = self.pair()
        rows[-1]["result"] = copy.deepcopy(rows[-1]["result"])
        rows[-1]["result"]["points"][0]["per_call_nanos"] += 1
        with self.assertRaisesRegex(ValueError, "summary differs"):
            self.validate_pair(names, rows)
        result = copy.deepcopy(self.result("runCompletion"))
        result["config"]["outer_trials"] = 2
        with self.assertRaisesRegex(ValueError, "registered schedule"):
            timing.validate_result(result, "runCompletion", self.expected, "measured")

    def test_dirty_or_different_source_rejected(self):
        for env in ({"git_commit": "other", "git_dirty": False},
                    {"git_commit": "measured", "git_dirty": True}):
            with self.subTest(env=env), self.assertRaises(ValueError):
                result = self.result("runCompletion")
                result["env"] = env
                timing.validate_result(result, "runCompletion", self.expected, "measured")

    def test_callback_hash_schedule_and_types(self):
        rows = [{"degree": n, "queries": 3*n+1, **self.expected[n]} for n in timing.DEGREES]
        self.path.write_text("\n".join(map(json.dumps, rows)))
        self.assertEqual(timing.validate_hashes(self.path), rows_to_expected(rows))
        for key, value in (("queries", 0), ("tableResultHash", True), ("tableResultHash", 2**64)):
            with self.subTest(key=key), self.assertRaises(ValueError):
                changed = copy.deepcopy(rows)
                changed[0][key] = value
                self.path.write_text("\n".join(map(json.dumps, changed)))
                timing.validate_hashes(self.path)

    def test_single_exports_and_distinct_result_hashes(self):
        export = {"export_schema_version": 1, "results": [self.result("runCompletion")]}
        self.path.write_text(json.dumps(export))
        timing.validate_single(self.path, "runCompletion", self.expected, "measured")
        for change in (lambda d: d.update(export_schema_version=2),
                       lambda d: d["results"].append(d["results"][0])):
            changed = copy.deepcopy(export)
            change(changed)
            self.path.write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                timing.validate_single(self.path, "runCompletion", self.expected, "measured")
        swapped = copy.deepcopy(export)
        swapped["results"][0]["points"][0]["result_hash"] = hex(
            self.expected[3][timing.RESULT_KEYS["runComparison"]])
        self.path.write_text(json.dumps(swapped))
        with self.assertRaises(ValueError):
            timing.validate_single(self.path, "runCompletion", self.expected, "measured")

    def test_retained_completion_rejects_comparison_hash_binding(self):
        directory = timing.ROOT/"reports/data/sign-det-joint-timing/1f55c4de9"
        expected = timing.validate_hashes(directory/"callbacks.log")
        revision = json.loads((directory/"metadata.json").read_text())["revision"]
        config = dict(timing.CONFIG, max_seconds_per_call=60)
        with patch.object(timing, "CONFIG", config):
            timing.validate_single(directory/"runCompletion.json", "runCompletion", expected, revision)
            with patch.dict(timing.RESULT_KEYS, runCompletion="comparisonResultHash"):
                with self.assertRaisesRegex(ValueError, "scientific observation"):
                    timing.validate_single(directory/"runCompletion.json", "runCompletion", expected, revision)

    def test_complete_retained_collection_and_archive_binding(self):
        import hashlib
        directory = timing.ROOT/"reports/data/sign-det-joint-timing/394c3c548"
        metadata = json.loads((directory/"metadata.json").read_text())
        archive = json.loads((directory/"archive.json").read_text())
        self.assertEqual(archive["source_revision"], metadata["revision"])
        self.assertEqual(metadata["state"], "complete")
        self.assertEqual(metadata["scientific_samples"], 180)
        for name, digest in archive["files_sha256"].items():
            self.assertEqual(Path(name).name, name)
            self.assertEqual(hashlib.sha256((directory/name).read_bytes()).hexdigest(), digest)
        self.assertEqual(set(archive["files_sha256"]),
                         {p.name for p in directory.iterdir() if p.is_file()}-{"archive.json"})
        self.assertEqual(metadata["source_sha256_after"], metadata["source_sha256"])
        self.assertEqual(metadata["binary_sha256_after"], metadata["binary_sha256"])
        self.assertEqual(metadata["revision_after"], metadata["revision"])
        self.assertEqual(metadata["status_after"], "")
        self.assertEqual(metadata["harness_binding_after"], metadata["harness_binding"])
        expected = timing.validate_hashes(directory/"callbacks.log")
        observations = {}
        pairs = {}
        for name in ("runCompletion", "runComparison"):
            observations[name] = timing.validate_single(
                directory/(name+".json"), name, expected, metadata["revision"])
        for label, names in (("production", ("runReduced", "runDirect")),
                             ("replay", ("runCheckReduced", "runCheckDirect"))):
            computed = timing.validate_pair(directory/(label+".jsonl"), names, expected, metadata["revision"])
            observations.update(computed["observations"])
            pairs[label] = computed["paired"]
        summary = json.loads((directory/"summary.json").read_text())
        self.assertEqual(summary["observations"], observations)
        self.assertEqual(summary["pairs"], pairs)
        self.assertEqual(summary["validation_errors"], [])

    def test_retained_profile_and_allocation_analysis(self):
        import hashlib
        base = timing.ROOT/"reports/data/sign-det-joint-timing"
        for label in ("profile", "allocation"):
            directory = base/(label+"-394c3c548")
            original = json.loads((directory/"artifacts.json").read_text())
            hashes = original.get("sha256", original.get("artifacts", {}))
            additional = json.loads((directory/"analysis-artifacts.json").read_text())["sha256"]
            raw_only = ({"heaptrack.zst", "comparison-allocations.stacks"} if label == "allocation"
                        else {"perf.data", "perf-script.txt", "summary.json", "perf-ip.txt", "perf-ip-pids.txt"})
            for name, digest in {**hashes, **additional}.items():
                target = directory/name
                self.assertEqual(Path(name).name, name)
                if name not in raw_only:
                    self.assertTrue(target.is_file(), name)
                    self.assertEqual(hashlib.sha256(target.read_bytes()).hexdigest(), digest)
            self.assertEqual((set(hashes)-raw_only) | set(additional) | {"artifacts.json", "analysis-artifacts.json"},
                             {p.name for p in directory.iterdir() if p.is_file()})
        profile = base/"profile-394c3c548"
        leaves = json.loads((profile/"leaf-categories.json").read_text())
        ips = json.loads((profile/"ip-summary.json").read_text())
        categories = {}
        for symbol, count in ips["leaf_counts"].items():
            category = leaves["assignments"][symbol]
            categories[category] = categories.get(category, 0) + count
        self.assertEqual(leaves["categories"], categories)
        self.assertEqual(sum(categories.values()), leaves["samples"])
        allocation = base/"allocation-394c3c548"
        original = json.loads((allocation/"summary.json").read_text())
        derived = json.loads((allocation/"reanalysis.json").read_text())
        self.assertEqual(derived["exact_callback_stack_calls"], original["exact_callback_stack_allocation_calls"])
        self.assertEqual(derived["other_filtered_stack_calls"], original["other_filtered_stack_allocation_calls"])
        frames = json.loads((allocation/"frame-allocation-counts.json").read_text())["frames"]
        self.assertNotIn("", frames)
        for frame, count in derived["callback_frame_variants"].items():
            self.assertEqual(frames[frame], count)
        self.assertEqual(frames["__gmp_default_allocate"] + frames["__gmp_default_reallocate"],
                         derived["filtered_stack_calls"])
        histogram = [tuple(map(int, row.split())) for row in
                     (allocation/"comparison-histogram.tsv").read_text().splitlines()]
        self.assertEqual(sum(count for _, count in histogram), derived["whole_process_intercepted_calls"])
        self.assertEqual(sum(size*count for size, count in histogram), derived["whole_process_requested_bytes"])
        self.assertEqual(derived["whole_process_intercepted_calls"], original["whole_process_allocation_calls"])
        self.assertEqual(derived["whole_process_requested_bytes"], original["whole_process_requested_bytes"])
        inclusive = json.loads((profile/"inclusive-summary.json").read_text())
        diagnostics = json.loads((profile/"diagnostics.json").read_text())
        self.assertEqual(inclusive["diagnostics"], diagnostics)
        self.assertEqual(inclusive["samples"], ips["operation_samples"])
        self.assertGreaterEqual(inclusive["classified_percent"], 90)
        self.assertEqual(diagnostics["confidence"], "passed")
        self.assertEqual(diagnostics["sensitivity"]["verdict"], "passed")

    def test_profile_call_paths_and_report_format(self):
        import re
        directory = timing.ROOT/"reports/data/sign-det-joint-timing/profile-394c3c548"
        paths = json.loads((directory/"stack-plausibility.json").read_text())
        self.assertEqual(paths["status"], "checked-paths-consistent")
        self.assertEqual(paths["unexpected_frames_below_gcd"], 0)
        self.assertEqual(paths["gmp_add_or_shift_without_uint64_constructor"], 0)
        summary = json.loads((directory/"inclusive-summary.json").read_text())
        share = next(row["percent"] for row in summary["top_inclusive"]
                     if row["function"] == "lean_nat_gcd")
        self.assertEqual(round(100*paths["gcd_ancestor_samples"]/paths["samples"], 2), share)
        self.assertIn("<__gmpz_add>", (directory/"constructor-disassembly.txt").read_text())
        self.assertIn("<__gmpz_mul_2exp>", (directory/"constructor-disassembly.txt").read_text())
        self.assertIn("<_ZN4lean3mpzC1Em>", (directory/"gcd-disassembly.txt").read_text())
        analysis = json.loads((directory/"samply-analysis.json").read_text())
        clock = json.loads((directory/"analysis-clock-anchor.json").read_text())
        conversion = analysis["clock_conversion"]
        self.assertEqual(conversion["residual_ns"], 0)
        self.assertEqual(conversion["sample_count"], paths["samples"] + 1232)
        self.assertAlmostEqual(conversion["corrected_start_time_ms"],
                               (clock["wall_ns_at_spawn"] - clock["mono_ns_at_spawn"]
                                + conversion["origin_ns"])/1e6, places=3)
        report = (timing.ROOT/"reports/sign-det-joint-performance.md").read_text()
        for destination in re.findall(r"\]\(([^)]*)\)", report):
            self.assertNotIn("\n", destination)
        opened = False
        for line in report.splitlines():
            if line.startswith("```"):
                if opened:
                    self.assertRegex(line, r"^```+$")
                opened = not opened
        self.assertFalse(opened)

    def test_pair_header_and_summary_environment_rejected(self):
        names, rows = self.pair()
        for change in (lambda r: r[0].update(params=[3]),
                       lambda r: r[0]["env"].update(git_dirty=True),
                       lambda r: r[-1]["result"].update(env={"git_commit": "other", "git_dirty": False})):
            changed = copy.deepcopy(rows)
            change(changed)
            with self.assertRaises(ValueError):
                self.validate_pair(names, changed)

    def test_callback_reordering_and_extra_fields_rejected(self):
        rows = [{"degree": n, "queries": 3*n+1, **self.expected[n]} for n in timing.DEGREES]
        for change in (lambda r: r.reverse(), lambda r: r[0].update(extra=1)):
            changed = copy.deepcopy(rows)
            change(changed)
            self.path.write_text("\n".join(map(json.dumps, changed)))
            with self.assertRaises(ValueError):
                timing.validate_hashes(self.path)

    def test_bad_first_arm_does_not_suppress_later_measurements(self):
        calls = []
        def run(label, arguments):
            calls.append(label)
            target = Path(arguments[-1])
            if label in ("runCompletion", "runComparison"):
                result = self.result(label)
                if label == "runCompletion":
                    result["points"][0]["status"] = "timed_out"
                target.write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
            else:
                names = (("runReduced", "runDirect") if label == "production" else
                         ("runCheckReduced", "runCheckDirect"))
                target.write_text("\n".join(map(json.dumps, self.pair(names)[1])))
            return 1
        summary = timing.collect_results(run, Path(self.tmp.name), self.expected, "measured")
        self.assertEqual(calls, ["runCompletion", "runComparison", "production", "replay"])
        self.assertEqual(summary["validation_errors"][0]["label"], "runCompletion")
        self.assertEqual(set(summary["observations"]), set(timing.RESULT_KEYS)-{"runCompletion"})
        self.assertEqual(json.loads((Path(self.tmp.name)/"summary.json").read_text()), summary)

    def test_harness_must_match_clean_manifest_pin(self):
        root = Path(self.tmp.name)
        (root/"lake-manifest.json").write_text(json.dumps({"packages": [
            {"name": "«lean-bench»", "rev": "pinned"}]}))
        for revision, status in (("other", ""), ("pinned", " M source.lean\n")):
            with patch.object(timing.subprocess, "check_output", side_effect=[revision, status]):
                with self.assertRaises(ValueError):
                    timing.harness_binding(root)
        with patch.object(timing.subprocess, "check_output", side_effect=["pinned", ""]):
            self.assertEqual(timing.harness_binding(root), {
                "revision": "pinned", "manifest_revision": "pinned", "status": ""})


def rows_to_expected(rows):
    return {row["degree"]: row for row in rows}


if __name__ == "__main__":
    unittest.main()
