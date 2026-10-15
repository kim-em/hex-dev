"""Regression checks for immutable primality evidence across the Theory rename."""
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "primality_factor_replay", Path(__file__).with_name("check_primality_factor_replay.py"))
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class ReplaySources(unittest.TestCase):
    def test_all_retained_source_hashes(self):
        manifests = [AUDIT.REPORTS / "kernel-certificates.json",
                     AUDIT.ROOT / "reports/primality/adoption/kernel-replay.json"]
        for path in manifests:
            data = json.loads(path.read_text())
            self.assertEqual(AUDIT.digest(AUDIT.retained_source(data["source"])),
                             data["source_sha256"])
        corpus = json.loads((AUDIT.REPORTS / "corpus-replay-v3.json").read_text())
        directory = AUDIT.ROOT / "bench/HexPrimalityTheory/ProofProbe/FactorCorpus"
        AUDIT.check_retained_sources(corpus["hex_sources"], directory)

    def test_changed_proof_does_not_match_archived_hash(self):
        record = json.loads((AUDIT.REPORTS / "kernel-certificates.json").read_text())
        text = AUDIT.retained_path(record["source"]).read_text()
        changed = text.replace("HexPrimalityTheory.Prime", "HexPrimalityTheory.PrimeX", 1)
        self.assertNotEqual(changed, text)
        with patch.object(Path, "read_text", return_value=changed):
            self.assertNotEqual(AUDIT.digest(AUDIT.retained_source(record["source"])),
                                record["source_sha256"])

    def test_other_paths_and_source_names_are_unchanged(self):
        source = "bench/Other/ProofProbe/A.lean"
        self.assertEqual(AUDIT.retained_path(source), AUDIT.ROOT / source)
        embedded = "other/bench/HexPrimalityMathlib/ProofProbe/A.lean"
        self.assertEqual(AUDIT.retained_path(embedded), AUDIT.ROOT / embedded)
        with patch.object(Path, "read_text", return_value="HexPrimalityTheory.Prime"):
            self.assertEqual(AUDIT.retained_source(source), "HexPrimalityTheory.Prime")
        with patch.object(Path, "read_text", return_value="HexPrimalityTheory"):
            self.assertEqual(AUDIT.retained_source(
                "bench/HexPrimalityMathlib/ProofProbe/A.lean"), "HexPrimalityTheory")

    def test_changed_corpus_membership_is_refused(self):
        corpus = json.loads((AUDIT.REPORTS / "corpus-replay-v3.json").read_text())
        sources = corpus["hex_sources"]
        directory = AUDIT.ROOT / "bench/HexPrimalityTheory/ProofProbe/FactorCorpus"
        missing = dict(sources)
        source, _ = missing.popitem()
        with self.assertRaisesRegex(AssertionError, "membership differs"):
            AUDIT.check_retained_sources(missing, directory)
        duplicate = dict(sources)
        path = AUDIT.retained_path(source)
        duplicate[str(path.relative_to(AUDIT.ROOT))] = AUDIT.digest(path.read_text())
        with self.assertRaisesRegex(AssertionError, "duplicate resolved"):
            AUDIT.check_retained_sources(duplicate, directory)
        files = list(directory.glob("*.lean")) + [directory / "Extra.lean"]
        with patch.object(Path, "glob", return_value=iter(files)):
            with self.assertRaisesRegex(AssertionError, "membership differs"):
                AUDIT.check_retained_sources(sources, directory)


if __name__ == "__main__":
    unittest.main()
