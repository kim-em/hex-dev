"""Reject corrupted outputs and schedules in joint-query scientific records."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from scripts.bench import sign_det_joint_timing as timing


class JointTimingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name)/"records.json"
        self.expected = {n: {key: 11 for key in set(timing.RESULT_KEYS.values())}
                         for n in timing.DEGREES}
        self.env = {"git_commit": "measured", "git_dirty": False}

    def result(self, name):
        return {"function": timing.PREFIX+name, "kind": "parametric", "hashable": True,
                "budget_truncated": False, "env": self.env, "config": timing.CONFIG,
                "complexity_formula": "n^3", "verdict": "inconclusive", "slope": 3,
                "c_min": 1, "c_max": 2, "advisories": [], "points": [
                    {"trial_index": trial, "param": n, "status": "ok", "result_hash": "0xb",
                     "part_of_verdict": True, "below_signal_floor": False,
                     "per_call_nanos": n**3, "inner_repeats": 1,
                     "peak_rss_kb": 1000, "alloc_bytes": None}
                    for trial in range(timing.TRIALS) for n in timing.DEGREES]}

    def pair(self):
        names = ("runReduced", "runDirect")
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


def rows_to_expected(rows):
    return {row["degree"]: row for row in rows}


if __name__ == "__main__":
    unittest.main()
