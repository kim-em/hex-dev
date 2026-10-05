"""Independent one-root oracle and fixed nested-table export validation."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from scripts.bench import sign_det_nested_tables as bench


class NestedTablesTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name)/"records"
        # Actual compiled inventories; fingerprints are not invented by the test.
        fixture = Path(__file__).with_name("fixtures")/"sign-det-nested-table-inputs.jsonl"
        self.rows = [json.loads(line) for line in fixture.read_text().splitlines()]

    def inputs(self, rows):
        self.path.write_text("\n".join(map(json.dumps, rows))+"\n")
        return bench.validate_inputs(self.path)

    def test_literal_oracle_and_complete_inputs(self):
        self.inputs(self.rows)
        for key, value in (("table", [[[0]*8, 1]]), ("rootCount", 2),
                           ("coefficient", bench.constant(1, 1)),
                           ("queryPolynomials", []), ("head", []),
                           ("momentSlots", 3), ("inputHash", True),
                           ("queryReductionSteps", 8), ("leafDomains", 0),
                           ("replayResultHash", 1)):
            changed = copy.deepcopy(self.rows); changed[0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.inputs(changed)
        with self.assertRaises(ValueError):
            self.inputs(self.rows[:-1])
        with self.assertRaises(ValueError):
            self.inputs(self.rows[::-1])

    def test_exact_export_declaration_and_observations(self):
        expected = self.inputs(self.rows)
        result = {"function": bench.PREFIX+"runProduce2", "kind": "parametric",
                  "hashable": True, "budget_truncated": False, "config": bench.CONFIG,
                  "complexity_formula": "s * (Nat.log2 s + 1)",
                  "env": {"git_commit": "source", "git_dirty": False},
                  "verdict": "inconclusive", "slope": 1, "advisories": [], "points": [
                      {"trial_index": trial, "param": size, "status": "ok",
                       "result_hash": hex(expected[2, size]["productionResultHash"]),
                       "part_of_verdict": True, "below_signal_floor": False,
                       "per_call_nanos": size*100, "inner_repeats": 1, "peak_rss_kb": 100, "alloc_bytes": None}
                      for trial in range(bench.TRIALS) for size in bench.SIZES]}
        def check(value):
            self.path.write_text(json.dumps({"export_schema_version": 1, "results": [value]}))
            return bench.validate_result(self.path, "runProduce2", expected, "source")
        self.assertEqual(check(result)["verdict"], "inconclusive")
        for key, value in (("result_hash", hex(expected[1, bench.SIZES[0]]["productionResultHash"])),
                           ("status", "killed_at_cap"), ("per_call_nanos", float("nan")),
                           ("inner_repeats", True)):
            changed = copy.deepcopy(result); changed["points"][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check(changed)
        for key, value in (("complexity_formula", "s"), ("function", bench.PREFIX+"runTree2")):
            changed = copy.deepcopy(result); changed[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check(changed)
        changed = copy.deepcopy(result); changed["env"]["git_dirty"] = True
        with self.assertRaises(ValueError):
            check(changed)
        changed = copy.deepcopy(result); changed["points"].pop()
        with self.assertRaises(ValueError):
            check(changed)

    def test_replay_rejects_another_depth_or_query_count(self):
        expected = self.inputs(self.rows)
        hashes = [row["replayResultHash"] for row in expected.values()]
        self.assertEqual(len(set(hashes)), len(hashes))
        for size in bench.SIZES:
            self.assertNotEqual(expected[1, size]["productionResultHash"],
                                expected[2, size]["productionResultHash"])
        result = {"function": bench.PREFIX+"runTree2", "kind": "parametric",
                  "hashable": True, "budget_truncated": False, "config": bench.CONFIG,
                  "complexity_formula": "s * (Nat.log2 s + 1)",
                  "env": {"git_commit": "source", "git_dirty": False},
                  "verdict": "inconclusive", "slope": 1, "advisories": [], "points": [
                      {"trial_index": trial, "param": size, "status": "ok",
                       "result_hash": hex(expected[2, size]["replayResultHash"]),
                       "part_of_verdict": True, "below_signal_floor": False,
                       "per_call_nanos": size*100, "inner_repeats": 1,
                       "peak_rss_kb": 100, "alloc_bytes": None}
                      for trial in range(bench.TRIALS) for size in bench.SIZES]}
        def check(value):
            self.path.write_text(json.dumps({"export_schema_version": 1, "results": [value]}))
            return bench.validate_result(self.path, "runTree2", expected, "source")
        check(result)
        for depth, size in ((1, bench.SIZES[0]), (2, bench.SIZES[1])):
            changed = copy.deepcopy(result)
            changed["points"][0]["result_hash"] = hex(expected[depth, size]["replayResultHash"])
            with self.subTest(depth=depth, size=size), self.assertRaises(ValueError):
                check(changed)
