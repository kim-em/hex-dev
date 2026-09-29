"""Adversarial validation of the full-support matrix measurement records."""
import copy
import json
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


if __name__ == "__main__":
    unittest.main()
