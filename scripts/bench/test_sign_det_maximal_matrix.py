"""Adversarial validation of the full-support matrix measurement records."""
import copy
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from scripts.bench import sign_det_maximal_matrix as bench


class MatrixEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.inventory = [{"queries": s, "matrixSize": 3**s, "supportSize": 3**s,
                           "countSum": 3**s, "inverseIdentityScalarPairs": 27**s,
                           "inverseBits": s+1, "denominatorBits": s+1,
                           "valuesBits": (3**s).bit_length(),
                           "matchesPolynomialSystem": True if s <= 3 else None,
                           "inputHash": s, "solveResultHash": 100+s, "checkResultHash": 11}
                          for s in bench.PARAMS]
        self.expected = {r["queries"]: r for r in self.inventory}
        self.result = {"function": bench.PREFIX+"runSolve", "kind": "parametric",
                       "hashable": True, "budget_truncated": False,
                       "env": {"git_commit": "source", "git_dirty": False},
                       "config": copy.deepcopy(bench.CONFIG), "complexity_formula": "27 ^ s",
                       "verdict": "inconclusive", "slope": 0.3, "c_min": 1, "c_max": 2,
                       "advisories": [], "points": [
                           {"trial_index": t, "param": s, "status": "ok",
                            "result_hash": hex(100+s), "part_of_verdict": True,
                            "below_signal_floor": False, "per_call_nanos": 1000+s,
                            "inner_repeats": 100, "peak_rss_kb": 1024, "alloc_bytes": None}
                           for t in range(bench.TRIALS) for s in bench.PARAMS]}

    def inventory_check(self, rows):
        with TemporaryDirectory() as d:
            path = Path(d)/"inventory.jsonl"
            path.write_text("".join(json.dumps(r)+"\n" for r in rows))
            return bench.validate_inventory(path)

    def result_check(self, result):
        with TemporaryDirectory() as d:
            path = Path(d)/"export.json"
            path.write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
            return bench.validate_export(path, "runSolve", self.expected, "source")

    def test_valid_records_keep_inconclusive(self):
        self.assertEqual(self.inventory_check(self.inventory), self.expected)
        self.assertEqual(self.result_check(self.result)["verdict"], "inconclusive")

    def test_incomplete_or_reordered_inventory(self):
        for rows in (self.inventory[:-1], self.inventory[::-1], self.inventory+self.inventory[:1]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                self.inventory_check(rows)

    def test_dimensions_counts_or_bits_must_match(self):
        for key in ("matrixSize", "supportSize", "countSum", "inverseIdentityScalarPairs",
                    "inverseBits", "denominatorBits", "valuesBits"):
            rows = copy.deepcopy(self.inventory)
            rows[2][key] += 1
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.inventory_check(rows)

    def test_polynomial_check_cannot_be_omitted_or_invented(self):
        for index, value in ((0, None), (2, False), (3, True), (4, False), (0, 1)):
            rows = copy.deepcopy(self.inventory)
            rows[index]["matchesPolynomialSystem"] = value
            with self.subTest(index=index, value=value), self.assertRaises(ValueError):
                self.inventory_check(rows)

    def test_noninteger_inventory_or_invalid_hashes(self):
        for key, value in (("queries", True), ("inputHash", -1), ("solveResultHash", 2**64),
                           ("checkResultHash", True), ("inverseBits", 2.0)):
            rows = copy.deepcopy(self.inventory)
            rows[0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.inventory_check(rows)

    def test_missing_or_duplicate_scientific_sample(self):
        for points in (self.result["points"][:-1], self.result["points"]+[self.result["points"][0]],
                       self.result["points"][::-1]):
            result = copy.deepcopy(self.result)
            result["points"] = points
            with self.subTest(points=points), self.assertRaises(ValueError):
                self.result_check(result)

    def test_failed_or_substituted_samples(self):
        for key, value in (("status", "timeout"), ("result_hash", "0x0"),
                           ("part_of_verdict", False), ("below_signal_floor", True),
                           ("trial_index", False), ("param", True)):
            result = copy.deepcopy(self.result)
            result["points"][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.result_check(result)

    def test_invalid_timing_or_memory(self):
        for key, value in (("per_call_nanos", -1), ("per_call_nanos", float("nan")),
                           ("inner_repeats", 0), ("inner_repeats", True),
                           ("peak_rss_kb", None), ("alloc_bytes", 100)):
            result = copy.deepcopy(self.result)
            result["points"][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.result_check(result)

    def test_profile_artifacts_and_scope(self):
        root = bench.ROOT/"reports/data/sign-det-maximal-matrices/profile-4540051d3"
        analysis = json.loads((root/"analysis.json").read_text())
        for name, expected in analysis["committed_files_sha256"].items():
            self.assertEqual(hashlib.sha256((root/name).read_bytes()).hexdigest(), expected)
        metadata = json.loads((root/"metadata.json").read_text())
        self.assertTrue(metadata["provenance_unchanged"])
        self.assertEqual(metadata["profile_row"]["inner_repeats"], 1)
        self.assertTrue(metadata["profile_row"]["profile_kernel"])
        conversion = json.loads((root/"clock-conversion.json").read_text())
        self.assertEqual(conversion["sample_count"], 577)
        self.assertEqual(conversion["residual_ns"], 0)
        summary = json.loads((root/"inclusive-summary.json").read_text())
        self.assertEqual(summary["samples"], 281)
        self.assertEqual(summary["diagnostics"]["confidence"], "passed")
        self.assertEqual(summary["diagnostics"]["sensitivity"]["verdict"], "passed")
        scientific = json.loads((bench.ROOT/"reports/data/sign-det-maximal-matrices/a7c9b34fb/metadata.json").read_text())
        self.assertEqual(metadata["binary_sha256"], scientific["binary_sha256"])
        self.assertEqual(metadata["binary_sha256"], analysis["raw_sha256"]["archived-debuggee"])
        region = metadata["operation_region"]
        self.assertEqual(region["mono_t1_ns"]-region["mono_t0_ns"], metadata["profile_row"]["total_nanos"])
        paths = json.loads((root/"stack-plausibility-v2.json").read_text())
        self.assertEqual(paths["status"], "checked-paths-consistent")
        self.assertEqual(paths["unexpected_frames_below_gcd"], 0)
        self.assertEqual(paths["gmp_add_or_shift_without_uint64_constructor"], 0)
        self.assertEqual(paths["samples"], summary["samples"])
        self.assertEqual(paths["unresolved_frames_below_gcd"], 0)
        self.assertEqual(paths["unresolved_samples_below_gcd"], 0)
        self.assertEqual(paths["row_add_and_gcd_samples"], 224)
        self.assertEqual(paths["uint64_constructor_under_gcd_samples"], 168)
        symbols = json.loads((root/"constructor-symbols.json").read_text())["symbols"]
        self.assertEqual(len(symbols), 2)
        self.assertEqual(symbols[0]["address"], symbols[1]["address"])
        self.assertEqual(symbols[0]["size"], symbols[1]["size"])

    def test_caller_analysis_replays_from_committed_profile(self):
        root = bench.ROOT/"reports/data/sign-det-maximal-matrices/profile-4540051d3"
        with TemporaryDirectory() as d:
            output = Path(d)/"replayed.json"
            subprocess.run([sys.executable, str(root/"stack_plausibility_v2.py"),
                            str(root/"filtered.json.gz"), str(root/"symbols.json"), str(output)],
                           check=True, stdout=subprocess.DEVNULL)
            self.assertEqual(json.loads(output.read_text()), json.loads((root/"stack-plausibility-v2.json").read_text()))

    def test_wrong_export_identity_or_verdict(self):
        for key, value in (("function", bench.PREFIX+"runCheck"), ("kind", "fixed"),
                           ("hashable", False), ("verdict", "passed")):
            result = copy.deepcopy(self.result)
            result[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.result_check(result)
        with TemporaryDirectory() as d:
            path = Path(d)/"export.json"
            for export in ({"export_schema_version": 2, "results": [self.result]},
                           {"export_schema_version": 1, "results": []},
                           {"export_schema_version": 1, "results": [self.result, self.result]}):
                path.write_text(json.dumps(export))
                with self.subTest(export=export), self.assertRaises(ValueError):
                    bench.validate_export(path, "runSolve", self.expected, "source")

    def test_retained_model_ratios_follow_harness_filter(self):
        root = bench.ROOT/"reports/data/sign-det-maximal-matrices/a7c9b34fb"
        for name in bench.KEYS:
            result = json.loads((root/(name+".json")).read_text())["results"][0]
            self.assertEqual([p for p, _ in result["ratios"]], [2, 3, 4, 5])
            self.assertEqual(result["verdict_dropped_leading"], 0)
            self.assertIsNone(result["slope"])

    def test_source_or_schedule_changes(self):
        for mutate in (lambda r: r["env"].update(git_commit="other"),
                       lambda r: r["env"].update(git_dirty=True),
                       lambda r: r["config"].update(outer_trials=5),
                       lambda r: r["config"].update(param_floor=True),
                       lambda r: r.update(complexity_formula="s^3"),
                       lambda r: r.update(budget_truncated=True)):
            result = copy.deepcopy(self.result)
            mutate(result)
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                self.result_check(result)

    def test_retained_collection_checks_all_sixty_samples(self):
        root = bench.ROOT/"reports/data/sign-det-maximal-matrices/a7c9b34fb"
        metadata = json.loads((root/"metadata.json").read_text())
        self.assertEqual(metadata["state"], "complete")
        self.assertEqual(metadata["scientific_samples"], 60)
        for before, after in (("revision", "revision_after"),
                              ("binary_sha256", "binary_sha256_after"),
                              ("source_sha256", "source_sha256_after"),
                              ("harness_binding", "harness_binding_after")):
            self.assertEqual(metadata[before], metadata[after])
        self.assertEqual(metadata["status_after"], "")
        expected = bench.validate_inventory(root/"inventory.log")
        summary = json.loads((root/"summary.json").read_text())
        self.assertEqual(summary["validation_errors"], [])
        for name in bench.KEYS:
            observation = bench.validate_export(root/(name+".json"), name, expected, metadata["revision"])
            self.assertEqual(observation, summary["observations"][name])

    def test_collect_keeps_second_arm_after_first_failure(self):
        calls = []
        with TemporaryDirectory() as d:
            out = Path(d)
            def run(name, args):
                calls.append(name)
                if name == "runSolve":
                    return 70
                result = copy.deepcopy(self.result)
                result["function"] = bench.PREFIX+name
                for point in result["points"]:
                    point["result_hash"] = hex(11)
                Path(args[-1]).write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
                return 1
            summary = bench.collect(run, out, self.expected, "source")
            self.assertEqual(calls, ["runSolve", "runCheck"])
            self.assertEqual(summary["observations"]["runCheck"]["verdict"], "inconclusive")
            self.assertTrue(summary["validation_errors"])
            self.assertEqual(json.loads((out/"summary.json").read_text()), summary)


class DimensionEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.rows = [{"queries": s, "matrixSize": 3**s, "supportSize": 3**s,
                      "countSum": 3**s, "inverseIdentityScalarPairs": 27**s,
                      "inverseBits": s+1, "denominatorBits": s+1,
                      "valuesBits": (3**s).bit_length(),
                      "matchesPolynomialSystem": True if s <= 3 else None,
                      "inputHash": s, "solveResultHash": 100+s, "checkResultHash": 11}
                     for s in range(1, 7)]
        self.expected = {r["matrixSize"]: r for r in self.rows}
        params, _, config, formula = bench.sweep_settings(True)
        self.result = {"function": bench.PREFIX+"runSolveDimension", "kind": "parametric",
                       "hashable": True, "budget_truncated": False,
                       "env": {"git_commit": "source", "git_dirty": False},
                       "config": copy.deepcopy(config), "complexity_formula": formula,
                       "verdict": "inconclusive", "slope": 0.3, "c_min": 1, "c_max": 2,
                       "advisories": [], "points": [
                           {"trial_index": t, "param": r, "status": "ok",
                            "result_hash": hex(self.expected[r]["solveResultHash"]),
                            "part_of_verdict": True, "below_signal_floor": False,
                            "per_call_nanos": 1000+r, "inner_repeats": 100,
                            "peak_rss_kb": 1024, "alloc_bytes": None}
                           for t in range(6) for r in params]}

    def inventory(self, rows):
        with TemporaryDirectory() as d:
            p = Path(d)/"inventory.jsonl"
            p.write_text("".join(json.dumps(r)+"\n" for r in rows))
            return bench.validate_inventory(p, by_dimension=True)

    def export(self, result):
        with TemporaryDirectory() as d:
            p = Path(d)/"result.json"
            p.write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
            return bench.validate_export(p, "runSolveDimension", self.expected, "source",
                                         by_dimension=True)

    def test_natural_dimension_records(self):
        self.assertEqual(self.inventory(self.rows), self.expected)
        self.assertEqual(self.export(self.result)["verdict"], "inconclusive")
        self.assertEqual(sorted(self.expected), [3, 9, 27, 81, 243, 729])

    def test_query_counts_cannot_replace_dimensions(self):
        result = copy.deepcopy(self.result)
        for p in result["points"]:
            p["param"] = self.expected[p["param"]]["queries"]
        with self.assertRaises(ValueError):
            self.export(result)
        rows = copy.deepcopy(self.rows)
        rows[0]["queries"] = rows[0]["matrixSize"]
        with self.assertRaises(ValueError):
            self.inventory(rows)

    def test_missing_largest_system(self):
        with self.assertRaises(ValueError):
            self.inventory(self.rows[:-1])
        result = copy.deepcopy(self.result)
        result["points"] = [p for p in result["points"] if p["param"] != 729]
        with self.assertRaises(ValueError):
            self.export(result)

    def test_legacy_model_or_registration_rejected(self):
        for key, value in (("complexity_formula", "27^s"),
                           ("function", bench.PREFIX+"runSolve"),
                           ("config", bench.CONFIG)):
            result = copy.deepcopy(self.result)
            result[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.export(result)


if __name__ == "__main__":
    unittest.main()
