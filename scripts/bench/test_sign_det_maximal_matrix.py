"""Adversarial validation of the full-support matrix measurement records."""
import copy
import hashlib
import json
import math
import os
import statistics
import subprocess
import sys
import runpy
import io
from contextlib import redirect_stderr
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch, Mock

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

    def test_retained_dimension_collection_and_archive(self):
        root = bench.ROOT/"reports/data/sign-det-maximal-matrices/ff35bd9da-dimensions"
        metadata = json.loads((root/"metadata.json").read_text())
        archive = json.loads((root/"archive.json").read_text())
        self.assertEqual(metadata["state"], "complete")
        self.assertEqual(metadata["scientific_samples"], 72)
        self.assertEqual(archive["scientific_samples"], 72)
        self.assertEqual(archive["source_hashes_verified"], len(metadata["source_sha256"]))
        for name, digest in archive["files"].items():
            self.assertEqual(hashlib.sha256((root/name).read_bytes()).hexdigest(), digest)
        for before, after in (("revision", "revision_after"),
                              ("binary_sha256", "binary_sha256_after"),
                              ("source_sha256", "source_sha256_after"),
                              ("harness_binding", "harness_binding_after")):
            self.assertEqual(metadata[before], metadata[after])
        self.assertEqual(metadata["status_after"], "")
        expected = bench.validate_inventory(root/"inventory.log", by_dimension=True)
        summary = json.loads((root/"summary.json").read_text())
        self.assertEqual(summary["validation_errors"], [])
        table = {row["dimension"]: row for row in json.loads((root/"table.json").read_text())}
        for name, label in (("runSolveDimension", "solve"), ("runCheckDimension", "check")):
            observation = bench.validate_export(root/(name+".json"), name, expected,
                                                metadata["revision"], by_dimension=True)
            self.assertEqual(observation, summary["observations"][name])
            result = json.loads((root/(name+".json")).read_text())["results"][0]
            self.assertEqual([r for r, _ in result["ratios"]], bench.DIMENSION_PARAMS)
            self.assertEqual(result["verdict_dropped_leading"], 1)
            ratios = result["ratios"][1:]
            xs, ys = [math.log(r) for r, _ in ratios], [math.log(c) for _, c in ratios]
            slope = sum((x-statistics.mean(xs))*(y-statistics.mean(ys))
                        for x, y in zip(xs, ys))/sum((x-statistics.mean(xs))**2 for x in xs)
            self.assertAlmostEqual(result["slope"], slope, places=6)
            for r in bench.DIMENSION_PARAMS:
                points = [p for p in result["points"] if p["param"] == r]
                self.assertEqual(table[r]["queries"], expected[r]["queries"])
                self.assertEqual(table[r][label+"_median_ms"],
                                 statistics.median(p["per_call_nanos"] for p in points)/1e6)
                self.assertEqual(table[r][label+"_peak_rss_median_mib"],
                                 statistics.median(p["peak_rss_kb"] for p in points)/1024)
        with TemporaryDirectory() as d:
            env = dict(os.environ, GIT_INDEX_FILE=str(Path(d)/"index"))
            subprocess.run(["git", "read-tree", archive["source_base"]],
                           cwd=bench.ROOT, env=env, check=True)
            subprocess.run(["git", "apply", "--cached", "--unidiff-zero"],
                           input=(root/"committed-source.patch").read_bytes(),
                           cwd=bench.ROOT, env=env, check=True)
            for name, digest in metadata["source_sha256"].items():
                contents = subprocess.check_output(["git", "show", ":"+name], cwd=bench.ROOT, env=env)
                self.assertEqual(hashlib.sha256(contents).hexdigest(), digest, name)

    def test_size_729_actual_elimination_inventory(self):
        root = bench.ROOT/"reports/data/sign-det-maximal-matrices/elimination-3042b0016"
        archive = json.loads((root/"archive.json").read_text())
        for name, digest in archive["files"].items():
            self.assertEqual(hashlib.sha256((root/name).read_bytes()).hexdigest(), digest)
        metadata = json.loads((root/"metadata.json").read_text())
        self.assertEqual(metadata["exit_code"], 0)
        self.assertFalse(metadata["scientific_timing"])
        self.assertEqual(metadata["source_sha256"], metadata["source_sha256_after"])
        self.assertEqual(metadata["binary_sha256"], metadata["binary_sha256_after"])
        self.assertEqual(metadata["status_after"], "")
        row = json.loads((root/"inventory.jsonl").read_text())
        self.assertEqual(row["queries"], 6)
        self.assertEqual(row["matrixSize"], 729)
        self.assertTrue(row["matchesInverse"])
        self.assertEqual(len(row["updatesPerColumn"]), 729)
        self.assertEqual(sum(row["updatesPerColumn"]), row["eliminatedRows"])
        self.assertEqual(row["eliminatedRows"], 2*(6**6-3**6))
        self.assertEqual(row["rowAddCalls"], 2*row["eliminatedRows"])
        self.assertEqual(row["rowAddScalarPairs"], 4*(18**6-9**6))
        self.assertEqual(row["rowScaleScalarProducts"], 2*729**2)
        self.assertEqual(row["inverseIdentityScalarPairs"], 729**3)
        timing = json.loads((bench.ROOT/"reports/data/sign-det-maximal-matrices/ff35bd9da-dimensions/metadata.json").read_text())
        for name,digest in metadata["source_sha256"].items():
            if name not in {"bench/HexSignDet/Bench.lean", "bench/HexSignDet/Small.lean",
                            "bench/HexSignDet/MaximalMatrix.lean"}:
                self.assertEqual(digest, timing["source_sha256"][name], name)
        source = metadata["source_archive"]
        patch_bytes = (root/source["file"]).read_bytes()
        self.assertEqual(hashlib.sha256(patch_bytes).hexdigest(), source["sha256"])
        with TemporaryDirectory() as d:
            env = dict(os.environ, GIT_INDEX_FILE=str(Path(d)/"index"))
            subprocess.run(["git", "read-tree", source["base_revision"]],
                           cwd=bench.ROOT, env=env, check=True)
            subprocess.run(["git", "apply", "--cached", "--unidiff-zero"], input=patch_bytes,
                           cwd=bench.ROOT, env=env, check=True)
            for name,digest in metadata["source_sha256"].items():
                contents = subprocess.check_output(["git", "show", ":"+name], cwd=bench.ROOT, env=env)
                self.assertEqual(hashlib.sha256(contents).hexdigest(), digest, name)

    def test_collect_dimension_mode_retains_both_arms(self):
        calls = []
        with TemporaryDirectory() as d:
            out = Path(d)
            def run(name, args):
                calls.append(name)
                result = copy.deepcopy(self.result)
                result["function"] = bench.PREFIX+name
                if name == "runCheckDimension":
                    for point in result["points"]:
                        point["result_hash"] = hex(11)
                Path(args[-1]).write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
                return 0
            summary = bench.collect(run, out, self.expected, "source", by_dimension=True)
            self.assertEqual(calls, ["runSolveDimension", "runCheckDimension"])
            self.assertEqual(summary["validation_errors"], [])
            self.assertEqual(len(summary["observations"]), 2)

    def test_retired_collection_cli_stops_before_running_commands(self):
        script = bench.ROOT/"scripts/bench/sign_det_maximal_matrix.py"
        with patch.object(sys, "argv", [str(script), "--output", "/unused-test-output"]), \
             patch.object(subprocess, "check_output") as output, \
             patch.object(subprocess, "Popen") as spawn, \
             patch.object(subprocess, "run") as run, \
             redirect_stderr(io.StringIO()) as stderr:
            with self.assertRaises(SystemExit) as exit_error:
                runpy.run_path(str(script), run_name="__main__")
        self.assertEqual(exit_error.exception.code, 2)
        self.assertIn("Reference-solve scaling registrations are retired", stderr.getvalue())
        output.assert_not_called()
        spawn.assert_not_called()
        run.assert_not_called()

    def test_main_dispatches_dimension_inventory_and_retains_exit_status(self):
        with TemporaryDirectory() as d:
            root, out = Path(d)/"source", Path(d)/"records"
            exe = root/".lake/build/bin/hexsigndet_bench"
            exe.parent.mkdir(parents=True)
            exe.write_bytes(b"test executable")
            for name in ("scripts/bench/sign_det_maximal_matrix.py",
                         "scripts/bench/test_sign_det_maximal_matrix.py",
                         "scripts/bench/sign_det_compare.py", "reports/sign-det-maximal-matrices.md"):
                p = root/name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("test source")
            commands = []
            fail = [False]
            def run(command, **kwargs):
                commands.append(command)
                if command[0] == str(exe):
                    if command[1] == "inspect-maximal-matrix-dimensions":
                        kwargs["stdout"].write("".join(json.dumps(r)+"\n" for r in self.rows))
                    else:
                        result = copy.deepcopy(self.result)
                        result["function"] = command[2]
                        if fail[0]:
                            result["points"][0]["status"] = "error"
                        if command[2].endswith("runCheckDimension"):
                            for point in result["points"]:
                                point["result_hash"] = hex(11)
                        Path(command[-1]).write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
                return Mock(returncode=0)
            def git(command, **kwargs):
                return "source\n" if command[1] == "rev-parse" else ""
            with patch.object(bench, "ROOT", root), \
                 patch.object(sys, "argv", ["collector", "--parameter", "matrix-size", "--output", str(out)]), \
                 patch.object(bench.subprocess, "check_output", side_effect=git), \
                 patch.object(bench.subprocess, "run", side_effect=run), \
                 patch.object(bench, "harness_binding", return_value={"clean": True}), \
                 patch.object(bench, "archive_sources"), \
                 patch.object(bench, "source_hashes", return_value={}), \
                 patch.object(bench, "acquire_cpu", return_value=(0, Mock())), \
                 patch.object(bench.os, "sched_setaffinity"), \
                 patch.object(bench.os, "sched_getaffinity", return_value={0}):
                self.assertEqual(bench.main(), 1)
                fail[0] = True
                failed_out = Path(d)/"failed-records"
                sys.argv[-1] = str(failed_out)
                with self.assertRaisesRegex(ValueError, "scientific validation failed"):
                    bench.main()
            self.assertIn([str(exe), "inspect-maximal-matrix-dimensions"], commands)
            metadata = json.loads((out/"metadata.json").read_text())
            self.assertEqual(metadata["collector_exit_code"], 1)
            self.assertEqual(metadata["schema"], "hex-sign-det-maximal-matrix-timing-v2")
            self.assertEqual(metadata["parameter"], "matrix-size")
            failure = json.loads((failed_out/"metadata.json").read_text())
            self.assertEqual(failure["collector_exit_code"], 2)
            self.assertEqual(failure["state"], "failed")
            self.assertTrue((failed_out/"runSolveDimension.json").exists())
            self.assertTrue((failed_out/"runCheckDimension.json").exists())

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
