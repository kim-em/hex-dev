"""Check retention and output paths for the nested-field sweep."""
from pathlib import Path
import hashlib
import json
import statistics
import os
import subprocess
from tempfile import TemporaryDirectory
import unittest

from scripts.bench import sign_det_nested_kernel as runner
from scripts.bench.fresh_module_sweep import validate_spec
from scripts.bench import test_sign_det_semantics as retention


class NestedOutputTests(retention.OutputTests):
    runner = runner


class ProbeInventoryTests(unittest.TestCase):
    def test_expanded_retained_records_and_source_archive(self):
        root = runner.ROOT/"reports/data/sign-det-nested-kernel/6d3801053"
        archive = json.loads((root/"archive.json").read_text())
        for name, digest in archive["files"].items():
            self.assertEqual(hashlib.sha256((root/name).read_bytes()).hexdigest(), digest)
        report = json.loads((root/"nested-kernel.json").read_text())
        self.assertEqual(report["measurement_state"], "complete")
        self.assertTrue(report["validity"]["release_quality"])
        self.assertEqual(report["validity"]["exceptions"], [])
        self.assertFalse(report["environment"]["git_dirty"])
        self.assertIsNone(report["partial_samples"])
        self.assertEqual(archive["completed_pairs"], 120)
        self.assertEqual(archive["completed_arms"], 240)
        self.assertEqual(archive["source_hashes_verified"], len(report["source_sha256"]))
        self.assertEqual(set(report["results"]), {p.name for p in runner.PAIRS})
        table = {r["pair"]: r for r in json.loads((root/"summary.json").read_text())}
        samples = []
        for name, result in report["results"].items():
            self.assertEqual(len(result["samples"]), 6)
            self.assertEqual({s["round"] for s in result["samples"]}, set(range(1,7)))
            for s in result["samples"]:
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
            delta = int(statistics.median(s["signed_wall_delta_nanos"] for s in result["samples"]))
            self.assertEqual(table[name]["paired_delta_seconds"], delta/1e9)
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
                           cwd=runner.ROOT, env=env, check=True)
            subprocess.run(["git", "apply", "--cached", "--unidiff-zero"],
                           input=(root/"committed-source.patch").read_bytes(),
                           cwd=runner.ROOT, env=env, check=True)
            for name,digest in report["source_sha256"].items():
                contents = subprocess.check_output(["git", "show", ":"+name], cwd=runner.ROOT, env=env)
                self.assertEqual(hashlib.sha256(contents).hexdigest(), digest, name)

    def test_spec_and_metadata(self):
        validate_spec(runner.SPEC)
        self.assertEqual(len(runner.PAIRS), 20)
        keys = set(runner.PAIRS[0].metadata)
        self.assertTrue(all(set(p.metadata) == keys for p in runner.PAIRS))
        self.assertIn(runner.ROOT / "scripts/bench/test_sign_det_nested_kernel.py",
                      [runner.ROOT / p for p in runner.SPEC.extra_sources])

    def test_every_proof_module_is_registered(self):
        source = runner.ROOT / "bench/HexSignDetMathlib"
        files = [*source.glob("ProofProbe/Nested/N*/*.lean"),
                 *source.glob("NestedProofProbe/N3/*.lean")]
        proofs = {"HexSignDetMathlib." + ".".join(p.relative_to(source).with_suffix("").parts)
                  for p in files if not p.stem.endswith("Baseline")}
        self.assertEqual({p.candidate.module for p in runner.PAIRS}, proofs)

    def test_imports_match_baselines(self):
        for p in runner.PAIRS:
            def imports(module):
                path = runner.ROOT / "bench" / Path(*module.split(".")).with_suffix(".lean")
                return [line for line in path.read_text().splitlines()
                        if line.startswith(("public import ", "public meta import "))]
            self.assertEqual(imports(p.reference.module), imports(p.candidate.module), p.name)

    def test_namespaces_guards_and_manual_target(self):
        for p in runner.PAIRS:
            path = runner.ROOT / "bench" / Path(*p.candidate.module.split(".")).with_suffix(".lean")
            source = path.read_text()
            self.assertIn("namespace " + p.candidate.axiom_namespace, source, p.name)
            self.assertIn("#guard_msgs (whitespace := lax) in\n#print axioms checked", source, p.name)
            self.assertEqual(p.metadata["build_target"] == "HexSignDetMathlibNestedProofProbe",
                             p.metadata["extension_depth"] == 3)


if __name__ == "__main__":
    unittest.main()
