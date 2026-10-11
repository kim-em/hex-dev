"""Reject changed canonical outputs and incomplete before/after schedules."""
import copy
import json
import hashlib
from pathlib import Path
import tarfile
import unittest
from scripts.bench import rationalfn_constants as bench


class Constants(unittest.TestCase):
    def test_retained_comparisons(self):
        root = Path(__file__).resolve().parents[2] / "reports/data/rationalfn-constants"
        archive = json.loads((root / "archive.json").read_text())
        for label in archive:
            item = archive[label]
            path = root / item["stored"]
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), item["sha256"])
            with tarfile.open(path) as tar:
                files = {member.name: tar.extractfile(member).read() for member in tar.getmembers()}
            metadata = json.loads(files["metadata.json"])
            self.assertEqual(metadata["state"], "complete")
            self.assertEqual(set(files), {"metadata.json", *metadata["file_sha256"]})
            for name, digest in metadata["file_sha256"].items():
                self.assertEqual(hashlib.sha256(files[name]).hexdigest(), digest)
            if label.startswith("sign-"):
                export = json.loads(files["timings.json"])["results"][0]
                self.assertEqual(export["env"]["git_commit"], metadata["revision"])
                self.assertEqual(export["complexity_formula"].replace(" ", ""), "signCostd")
                self.assertEqual(len(export["points"]), item["observations"])
                self.assertTrue(all(p["status"] == "ok" and p["result_hash"] == "0x2"
                                    for p in export["points"]))
                continue
            hashes = bench.validate_inventory([
                json.loads(line) for line in files["before-inputs.jsonl"].splitlines()])
            self.assertEqual(hashes, bench.validate_inventory([
                json.loads(line) for line in files["after-inputs.jsonl"].splitlines()]))
            for d in (6, 9, 12):
                hashes[("sign", d)] = "0x2"
            rows = [json.loads(line) for line in files["samples.jsonl"].splitlines()]
            summary = bench.validate_samples(rows, hashes, metadata["bindings"],
                                             cases=metadata["protocol"]["cases"])
            self.assertEqual(summary, json.loads(files["summary.json"]))
            self.assertEqual(len(rows), item["observations"])

    def inventory(self):
        rows = []
        for op, _, _, depths in bench.CASES[:2]:
            for d in depths:
                value = ({"zero": bench.constant(0, d), "one": bench.constant(1, d)} if op == "units"
                         else {"num": [bench.constant(1, d-1), bench.constant(1, d-1)],
                               "den": [bench.constant(-1, d-1), bench.constant(1, d-1)]})
                rows.append({"operation": op, "depth": d, "input": json.dumps(value),
                             "output": json.dumps(value), "resultHash": 2})
        return rows

    def test_complete_canonical_outputs(self):
        rows = self.inventory()
        bench.validate_inventory(rows)
        for corrupt in (rows[:-1], list(reversed(rows))):
            with self.assertRaises(ValueError):
                bench.validate_inventory(corrupt)
        corrupt = copy.deepcopy(rows)
        corrupt[0]["output"] = '{}'
        with self.assertRaises(ValueError):
            bench.validate_inventory(corrupt)

    def test_schedule_and_source(self):
        bindings = {arm: {"revision": arm} for arm in ("before", "after")}
        hashes = {(op, d): "0x2" for op, _, _, depths in bench.CASES for d in depths}
        rows = [{"trial": trial, "operation": op, "depth": d, "arm": arm,
                 "point": {"status": "ok", "result_hash": "0x2", "inner_repeats": 10,
                           "per_call_nanos": 10 if arm == "before" else 5,
                           "function": function, "param": d, "cache_mode": "warm",
                           "env": {"git_commit": arm, "git_dirty": False}}}
                for trial in range(bench.TRIALS) for op, _, function, depths in bench.CASES
                for d in depths for arm in (["before", "after"] if trial % 2 == 0 else ["after", "before"])]
        self.assertTrue(all(r["paired_speedup_median"] == 2
                            for r in bench.validate_samples(rows, hashes, bindings)))
        for corrupt in (rows[:-1], list(reversed(rows))):
            with self.assertRaises(ValueError):
                bench.validate_samples(corrupt, hashes, bindings)
        for key, value in (("status", "error"), ("per_call_nanos", float('nan')),
                           ("inner_repeats", True), ("result_hash", "0x3"),
                           ("function", "other"), ("param", 99), ("cache_mode", "cold"),
                           ("env", {"git_commit": "wrong", "git_dirty": False})):
            corrupt = copy.deepcopy(rows)
            corrupt[0]["point"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                bench.validate_samples(corrupt, hashes, bindings)


if __name__ == "__main__":
    unittest.main()
