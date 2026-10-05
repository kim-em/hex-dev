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
        # Compiled inventory snapshot; fingerprints are not invented by the test.
        # The collector regenerates live inputs; this fixture is not a freshness gate.
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
                           ("queryReductionSteps", 8), ("leafNodes", 0),
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

    def test_historical_ladder_requires_explicit_binding(self):
        fixture = Path(__file__).with_name("fixtures")/"sign-det-nested-table-short-inputs.jsonl"
        with self.assertRaisesRegex(ValueError, "missing or reordered"):
            bench.validate_inputs(fixture)
        historical = bench.validate_inputs(fixture, sizes=bench.SHORT_SIZES)
        self.assertEqual(len(historical), 10)
        self.assertEqual(bench.configuration(bench.SHORT_SIZES)["param_floor"], 8)
        self.assertEqual(bench.CONFIG["param_floor"], 128)
        with self.assertRaisesRegex(ValueError, "unknown declared"):
            bench.validate_inputs(fixture, sizes=list(reversed(bench.SHORT_SIZES)))
        with self.assertRaisesRegex(ValueError, "unknown declared"):
            bench.configuration([8, 128])

    def test_historical_export_requires_explicit_binding(self):
        fixture = Path(__file__).with_name("fixtures")/"sign-det-nested-table-short-inputs.jsonl"
        expected = bench.validate_inputs(fixture, sizes=bench.SHORT_SIZES)
        result = {"function": bench.PREFIX+"runTree2", "kind": "parametric",
                  "hashable": True, "budget_truncated": False,
                  "config": bench.configuration(bench.SHORT_SIZES),
                  "complexity_formula": "s * (Nat.log2 s + 1)",
                  "env": {"git_commit": "source", "git_dirty": False},
                  "verdict": "inconclusive", "slope": -0.16, "advisories": [],
                  "points": [{"trial_index": trial, "param": size, "status": "ok",
                              "result_hash": hex(expected[2, size]["replayResultHash"]),
                              "part_of_verdict": True, "below_signal_floor": False,
                              "per_call_nanos": size*100, "inner_repeats": 1,
                              "peak_rss_kb": 100, "alloc_bytes": None}
                             for trial in range(bench.TRIALS) for size in bench.SHORT_SIZES]}
        self.path.write_text(json.dumps({"export_schema_version": 1, "results": [result]}))
        self.assertEqual(bench.validate_result(self.path, "runTree2", expected, "source",
                                             sizes=bench.SHORT_SIZES)["slope"], -0.16)
        with self.assertRaisesRegex(ValueError, "wrong registration"):
            bench.validate_result(self.path, "runTree2", expected, "source")

    def test_retained_timing_records_and_corruption(self):
        from scripts.bench.sign_det_nested_archive import validate
        directory = Path(__file__).resolve().parents[2]/"reports/data/sign-det-nested-tables/39066b34e1"
        self.assertEqual(len(validate(directory)), 2)
        import shutil
        copy = Path(self.tmp.name)/"archive"
        shutil.copytree(directory, copy)
        manifest = json.loads((copy/"archive.json").read_text())
        file = copy/manifest["timing_collections"][0]["files"]["runTree2.json"]["file"]
        original = file.read_bytes()
        file.write_bytes(original+b"corrupt")
        with self.assertRaisesRegex(ValueError, "changed stored bytes"):
            validate(copy)
        file.write_bytes(original)
        manifest["timing_collections"][1]["observations"]["runProduce2"]["verdict"] = "consistent_with_declared_complexity"
        (copy/"archive.json").write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "summary disagrees"):
            validate(copy)

    def test_retained_allocation_regions_and_corruption(self):
        from scripts.bench.sign_det_nested_archive import validate_allocation
        directory = Path(__file__).resolve().parents[2]/"reports/data/sign-det-nested-tables/39066b34e1/allocation"
        self.assertEqual(len(validate_allocation(directory)), 36)
        import shutil
        copy = Path(self.tmp.name)/"allocation"
        shutil.copytree(directory, copy)
        manifest = json.loads((copy/"archive.json").read_text())
        name = manifest["files"]["metadata.json"]["file"]
        file = copy/name; original = file.read_bytes()
        file.write_bytes(original+b"changed")
        with self.assertRaises(ValueError):
            validate_allocation(copy)
        file.write_bytes(original)
        manifest["summary"][bench.PREFIX+"runTree2"]["128"]["callbacks"] = 0
        (copy/"archive.json").write_text(json.dumps(manifest))
        with self.assertRaises(ValueError):
            validate_allocation(copy)
