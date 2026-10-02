"""Validate retained sign-determination measurements and source archives."""
from pathlib import Path
import hashlib
import json
import statistics
import os
import subprocess
from tempfile import TemporaryDirectory
import unittest

ROOT = Path(__file__).resolve().parents[2]
EXPECTED_NESTED_PAIRS = {
    f"depth-{depth}-{kind}" for depth in (1, 2, 3)
    for kind in ("Accept", "RejectArithmetic", "RejectStale", "ArithmeticCause")
} | {
    f"depth-{depth}-{kind}" for depth in (1, 2)
    for kind in ("AcceptFraction", "RejectProduct", "FieldArithmetic", "Certificates")
}


class RetainedEvidenceTests(unittest.TestCase):
    def test_expanded_retained_records_and_source_archive(self):
        root = ROOT/"reports/data/sign-det-nested-kernel/6d3801053"
        archive = json.loads((root/"archive.json").read_text())
        for name, digest in archive["files"].items():
            self.assertEqual(hashlib.sha256((root/name).read_bytes()).hexdigest(), digest)
        report = json.loads((root/"nested-kernel.json").read_text())
        self.assertEqual(report["measurement_state"], "complete")
        self.assertTrue(report["validity"]["release_quality"])
        self.assertEqual(report["validity"]["exceptions"], [])
        self.assertFalse(report["environment"]["git_dirty"])
        self.assertIsNone(report["partial_samples"])
        self.assertEqual(archive["measured_revision"], report["environment"]["git_commit"])
        self.assertEqual(archive["schema"], report["schema"])
        self.assertEqual(archive["completed_pairs"], 120)
        self.assertEqual(archive["completed_arms"], 240)
        self.assertEqual(archive["source_hashes_verified"], len(report["source_sha256"]))
        self.assertEqual(set(report["results"]), EXPECTED_NESTED_PAIRS)
        table = {r["pair"]: r for r in json.loads((root/"summary.json").read_text())}
        self.assertEqual(set(table), set(report["results"]))
        samples = []
        for name, result in report["results"].items():
            self.assertEqual(len(result["samples"]), 6)
            self.assertEqual({s["round"] for s in result["samples"]}, set(range(1,7)))
            for s in result["samples"]:
                self.assertEqual(s["build_order"], (["reference", "candidate"] if s["round"] % 2
                                                     else ["candidate", "reference"]))
                self.assertEqual(set(s["candidate"]["axioms"]),
                                 {"propext", "Classical.choice", "Quot.sound"})
                self.assertIsNone(s["reference"]["axioms"])
                self.assertEqual(s["signed_wall_delta_nanos"],
                                 s["candidate"]["wall_nanos"]-s["reference"]["wall_nanos"])
                samples.append((name, result, s))
            for key, field, side, divisor in (
                    ("candidate_seconds", "wall_nanos", "candidate", 1e9),
                    ("reference_seconds", "wall_nanos", "reference", 1e9),
                    ("candidate_peak_rss_gib", "peak_rss_kb", "candidate", 1048576)):
                expected = int(statistics.median(s[side][field] for s in result["samples"]))
                self.assertEqual(table[name][key], expected/divisor)
                self.assertEqual(result["median_"+side+"_"+field], expected)
            delta = int(statistics.median(s["signed_wall_delta_nanos"] for s in result["samples"]))
            self.assertEqual(table[name]["paired_delta_seconds"], delta/1e9)
            self.assertEqual(result["median_signed_wall_delta_nanos"], delta)
        samples.sort(key=lambda x:(x[2]["round"],x[2]["slot_index"]))
        order = report["config"]["order"]
        for i in range(6):
            self.assertEqual([name for name,_,s in samples if s["round"] == i+1],
                             order[i:]+order[:i])
        records = [json.loads(l) for l in (root/"nested-kernel.json.samples.jsonl").read_text().splitlines()]
        self.assertEqual(records[0]["source_sha256"], report["source_sha256"])
        self.assertEqual(records[-1], {"type":"complete", "code":0})
        expected = [(r[side]["module"],s[side]) for _,r,s in samples for side in s["build_order"]]
        self.assertEqual(len(records[1:-1]), 240)
        for record, (module, sample) in zip(records[1:-1], expected, strict=True):
            self.assertEqual(record["type"], "sample")
            self.assertEqual(record["module"], module)
            for key,value in record.items():
                if key in ("type", "module"):continue
                if key == "cpu_accounting":
                    self.assertEqual({k:sample[key][k] for k in value}, value)
                    self.assertLessEqual(set(sample[key])-set(value),
                                         {"aggregate_core_interference_seconds"})
                else:self.assertEqual(sample[key],value)
        with TemporaryDirectory() as d:
            env = dict(os.environ, GIT_INDEX_FILE=str(Path(d)/"index"))
            subprocess.run(["git", "read-tree", archive["source_base"]],
                           cwd=ROOT, env=env, check=True)
            subprocess.run(["git", "apply", "--cached", "--unidiff-zero"],
                           input=(root/"committed-source.patch").read_bytes(),
                           cwd=ROOT, env=env, check=True)
            for name,digest in report["source_sha256"].items():
                contents = subprocess.check_output(["git", "show", ":"+name], cwd=ROOT, env=env)
                self.assertEqual(hashlib.sha256(contents).hexdigest(), digest, name)


    def test_semantic_sources_reconstruct(self):
        path = ROOT / "reports/data/sign-det-semantics/source-archive.json"
        archive = json.loads(path.read_text())
        self.assertEqual(archive["schema"], "hex-source-archive-v1")
        count = 0
        for snapshot in archive["snapshots"].values():
            report = json.loads((ROOT / snapshot["measurement"]).read_text())
            self.assertEqual(snapshot["commit"], report["environment"]["git_commit"])
            self.assertEqual(snapshot["source_sha256"], report["source_sha256"])
            self.assertLessEqual(set(snapshot["overrides"]), set(snapshot["source_sha256"]))
            for name, expected in snapshot["source_sha256"].items():
                if name in snapshot["overrides"]:
                    contents = snapshot["overrides"][name].encode("utf-8")
                else:
                    contents = subprocess.check_output(
                        ["git", "show", archive["baseCommit"] + ":" + name], cwd=ROOT)
                self.assertEqual(hashlib.sha256(contents).hexdigest(), expected, name)
                count += 1
        self.assertEqual(count, 442)


if __name__ == "__main__":
    unittest.main()
