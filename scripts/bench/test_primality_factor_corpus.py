"""Reject corrupt corpus identities and skipped earlier prime candidates."""
import copy
import hashlib
import json
import re
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.ci import check_primality_factor_replay as replay

from scripts.bench.primality_factor_corpus import candidate, composite_witness, validate


class CorpusTests(unittest.TestCase):
    def setUp(self):
        source = Path(__file__).resolve().parents[2] / 'reports/primality/factor-policy/corpus-v3.json'
        self.corpus = copy.deepcopy(json.loads(source.read_text()))
        self.corpus['count_per_size'] = 4
        self.corpus['cases'] = [x for x in self.corpus['cases'] if x['index'] < 4]
        for x in self.corpus['cases']:
            x['split'] = 'tuning' if x['index'] == 0 else 'validation'
            x['id'] = f"{x['split']}-{x['bits']}-{x['index']}"

    def test_small_reproduction(self):
        validate(self.corpus)

    def test_corrupt_subject_and_split(self):
        for field, value in [('subject', self.corpus['cases'][0]['subject'] + 2),
                             ('split', 'validation')]:
            corpus = copy.deepcopy(self.corpus)
            corpus['cases'][0][field] = value
            with self.assertRaises(AssertionError):
                validate(corpus)

    def test_cannot_skip_a_prime(self):
        case = self.corpus['cases'][0]
        counter = case['counter'] + 1
        while True:
            n = candidate(case['bits'], case['index'], counter)
            if not any(composite_witness(n, a) for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]):
                break
            counter += 1
        case.update(counter=counter, subject=n)
        # The previous accepted prime is now an earlier candidate. Its absence
        # of a compositeness witness must reject this otherwise consistent row.
        with self.assertRaises(AssertionError):
            validate(self.corpus)


class RetainedSourceTests(unittest.TestCase):
    def test_retained_corpus_and_adoption_hashes(self):
        corpus = json.loads((replay.REPORTS / "corpus-replay-v3.json").read_text())
        for source, expected in corpus["hex_sources"].items():
            with self.subTest(source=source):
                self.assertEqual(replay.digest(replay.retained_source(source)), expected)
        adoption = json.loads((replay.ROOT / "reports/primality/adoption/kernel-replay.json").read_text())
        self.assertEqual(replay.digest(replay.retained_source(adoption["source"])),
                         adoption["source_sha256"])

    def test_only_directory_and_import_are_translated(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            current = root / replay.CURRENT_PREFIX / "Probe.lean"
            current.parent.mkdir(parents=True)
            current.write_text("public import HexPrimalityTheory.Prime\n"
                               "namespace HexPrimalityTheory.X\n"
                               "theorem test : True := by trivial\n")
            name = replay.HISTORICAL_PREFIX + "Probe.lean"
            expected = ("public import HexPrimalityMathlib.Prime\n"
                        "namespace HexPrimalityTheory.X\ntheorem test : True := by trivial\n")
            with patch.object(replay, "ROOT", root):
                self.assertEqual(replay.retained_source(name), expected)
                current.write_text(current.read_text().replace("True", "False"))
                self.assertNotEqual(replay.digest(replay.retained_source(name)), replay.digest(expected))
                current.write_text(expected)
                with self.assertRaisesRegex(ValueError, "removed module"):
                    replay.retained_source(name)
                with self.assertRaises(FileNotFoundError):
                    replay.retained_source(replay.HISTORICAL_PREFIX + "Missing.lean")

    def test_recorded_source_after_companion_rename(self):
        from scripts.ci.check_primality_factor_replay import ROOT, retained_source
        manifest = json.loads((ROOT / 'reports/primality/factor-policy/kernel-certificates.json').read_text())
        self.assertEqual(hashlib.sha256(retained_source(manifest['source']).encode()).hexdigest(),
                         manifest['source_sha256'])

    def test_certificate_edits_are_not_normalized(self):
        from scripts.ci.check_primality_factor_replay import ROOT, retained_source, retained_path
        manifest = json.loads((ROOT / 'reports/primality/factor-policy/kernel-certificates.json').read_text())
        original = retained_path(manifest['source']).read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'bench/HexPrimalityTheory/ProofProbe/FactorExperiment.lean'
            path.parent.mkdir(parents=True)
            changed_certificate = re.sub(
                r'(\(c := Hex\.Nat\.PrimeCert\.\w+\s+)([0-9])',
                lambda m: m[1] + str((int(m[2]) + 1) % 10), original, count=1)
            for changed in (original.replace('theorem case0', 'theorem changedCase0', 1),
                            changed_certificate):
                with self.subTest(changed_certificate=changed == changed_certificate):
                    self.assertNotEqual(changed, original)
                    path.write_text(changed)
                    self.assertNotEqual(
                        hashlib.sha256(retained_source(manifest['source'], root).encode()).hexdigest(),
                        manifest['source_sha256'])

    def test_missing_unrelated_source_is_not_redirected(self):
        from scripts.ci.check_primality_factor_replay import retained_source
        with tempfile.TemporaryDirectory() as directory:
            alternate = Path(directory) / 'bench/OtherTheory/Probe.lean'
            alternate.parent.mkdir(parents=True)
            alternate.write_text('theorem unrelated : True := by trivial\n')
            with self.assertRaises(FileNotFoundError):
                retained_source('bench/OtherMathlib/Probe.lean', Path(directory))


    def test_all_recorded_corpus_sources(self):
        from scripts.ci.check_primality_factor_replay import ROOT, check_retained_sources
        report = json.loads((ROOT / 'reports/primality/factor-policy/corpus-replay-v3.json').read_text())
        check_retained_sources(report['hex_sources'],
                               ROOT / 'bench/HexPrimalityTheory/ProofProbe/FactorCorpus')
        from scripts.ci.check_primality_factor_replay import retained_source
        adoption = json.loads((ROOT / 'reports/primality/adoption/kernel-replay.json').read_text())
        self.assertEqual(hashlib.sha256(retained_source(adoption['source']).encode()).hexdigest(),
                         adoption['source_sha256'])

    def make_corpus(self, root):
        old = 'bench/HexPrimalityMathlib/ProofProbe/FactorCorpus/'
        directory = root / 'bench/HexPrimalityTheory/ProofProbe/FactorCorpus'
        directory.mkdir(parents=True)
        sources = {}
        for index in range(2):
            name = f'Chunk{index:03}.lean'
            text = ('public import HexPrimalityTheory.Prime\n'
                    f'theorem case{index} : True := by trivial\n')
            (directory / name).write_text(text)
            legacy = text.replace('HexPrimalityTheory.Prime', 'HexPrimalityMathlib.Prime')
            sources[old + name] = hashlib.sha256(legacy.encode()).hexdigest()
        return sources, directory

    def test_changed_proof_rejected_by_corpus_checker(self):
        from scripts.ci.check_primality_factor_replay import check_retained_sources
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sources, directory = self.make_corpus(root)
            check_retained_sources(sources, directory, root)
            path = directory / 'Chunk000.lean'
            original = path.read_text()
            changed = original.replace('by trivial', 'by exact True.intro')
            self.assertNotEqual(changed, original)
            path.write_text(changed)
            with self.assertRaisesRegex(AssertionError, 'source hash differs'):
                check_retained_sources(sources, directory, root)

    def test_corpus_membership_refusals(self):
        from scripts.ci.check_primality_factor_replay import check_retained_sources
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sources, directory = self.make_corpus(root)
            missing = dict(sources)
            source, _ = missing.popitem()
            with self.assertRaisesRegex(AssertionError, 'membership differs'):
                check_retained_sources(missing, directory, root)
            duplicate = dict(sources)
            path = directory / Path(source).name
            duplicate[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
            with self.assertRaisesRegex(AssertionError, 'duplicate resolved'):
                check_retained_sources(duplicate, directory, root)
            (directory / 'Extra.lean').write_text('-- extra proof file\n')
            with self.assertRaisesRegex(AssertionError, 'membership differs'):
                check_retained_sources(sources, directory, root)



if __name__ == '__main__':
    unittest.main()
