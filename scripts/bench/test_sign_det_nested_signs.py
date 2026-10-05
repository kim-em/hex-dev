"""Reject fabricated nested coefficient inputs and incomplete timing streams."""
import copy
import json
import gzip
from pathlib import Path
import tempfile
import unittest
from scripts.bench import sign_det_nested_signs as bench


class NestedSigns(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = Path(self.temporary.name) / "records.json"
        self.rows = []
        for d in bench.DEPTHS:
            literal = json.dumps({"num": [bench.constant(0, d-1), bench.constant(1, d-1)],
                                  "den": [bench.constant(1, d-1)]})
            self.rows.append({"depth": d, "coefficient": literal, "encodedBytes": len(literal),
                                "predictedBaseSigns": 2**d, "resultHash": 2})

    def inputs(self, rows):
        self.path.write_text("\n".join(map(json.dumps, rows)))
        return bench.validate_inputs(self.path)

    def test_literal_coefficients_and_schedule(self):
        self.inputs(self.rows)
        for key, value in (("depth", 2.0), ("predictedBaseSigns", True),
                           ("resultHash", -1), ("encodedBytes", 1)):
            changed = copy.deepcopy(self.rows)
            changed[0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.inputs(changed)
        changed = copy.deepcopy(self.rows)
        literal = json.loads(changed[0]["coefficient"])
        literal["den"] = [bench.constant(-1, 1)]
        changed[0]["coefficient"] = json.dumps(literal)
        changed[0]["encodedBytes"] = len(changed[0]["coefficient"])
        with self.assertRaises(ValueError):
            self.inputs(changed)

    def test_failed_nonfinite_or_missing_observations(self):
        expected = self.inputs(self.rows)
        result = {"function": bench.FUNCTION, "kind": "parametric", "hashable": True,
                  "budget_truncated": False, "complexity_formula": "numeralCost d", "config": bench.CONFIG,
                  "env": {"git_commit": "source", "git_dirty": False}, "verdict": "inconclusive",
                  "slope": 1, "advisories": [], "points": [
                      {"trial_index": trial, "param": d, "status": "ok", "result_hash": "0x2",
                       "part_of_verdict": True, "below_signal_floor": False,
                       "per_call_nanos": 2**d, "inner_repeats": 1, "peak_rss_kb": 100, "alloc_bytes": None}
                      for trial in range(6) for d in bench.DEPTHS]}
        def check(value):
            self.path.write_text(json.dumps({"export_schema_version": 1, "results": [value]}))
            return bench.validate_result(self.path, expected, "source")
        self.assertEqual(check(result)["verdict"], "inconclusive")
        for key, value in (("status", "killed_at_cap"), ("per_call_nanos", float("nan")),
                           ("inner_repeats", True), ("result_hash", "0x0")):
            changed = copy.deepcopy(result)
            changed["points"][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check(changed)
        changed = copy.deepcopy(result)
        changed["points"].pop()
        with self.assertRaises(ValueError):
            check(changed)

    def test_original_declaration_is_retained_and_rejected(self):
        root = Path(__file__).resolve().parents[2]
        directory = root / "reports/data/sign-det-nested-signs/596ef4d810/timing"
        raw = gzip.decompress((directory / "timings.json.gz").read_bytes())
        result = json.loads(raw)["results"][0]
        self.assertEqual(result["complexity_formula"].replace(" ", ""), "2^d")
        self.assertEqual(result["verdict"], "inconclusive")
        self.assertAlmostEqual(result["slope"], 3.924086, places=5)
        self.path.write_bytes(raw)
        expected = {
            d: result["points"][i]["result_hash"] for i, d in enumerate(bench.DEPTHS)}
        with self.assertRaises(ValueError):
            bench.validate_result(self.path, expected, result["env"]["git_commit"])
