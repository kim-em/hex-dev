"""Check frozen root-route provenance and registered paired observations."""
import copy
import hashlib
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from scripts.bench.analyze_real_closure_trivial import analyze, audit_archive

RESULTS = Path(__file__).resolve().parents[2] / 'reports/bench-results/real-closure-trivial'


class CaptureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        with tarfile.open(RESULTS / 'capture.tar.gz') as contents:
            contents.extractall(self.directory, filter='data')
        self.index = json.loads((RESULTS / 'archive-index.json').read_text())
        self.metadata = json.loads((self.directory / 'metadata.json').read_text())

    def save(self):
        (self.directory / 'metadata.json').write_text(json.dumps(self.metadata))

    def mutate_export(self, mutate):
        path = self.directory / self.metadata['observations'][0]['export']
        data = json.loads(path.read_text())
        mutate(data['results'][0])
        path.write_text(json.dumps(data))
        self.metadata['artifacts'][path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.save()

    def reject(self):
        with self.assertRaises(ValueError):
            analyze(self.directory, self.index)

    def test_archive_and_analysis_reproduce(self):
        index = audit_archive(self.directory, RESULTS / 'archive-index.json', 'capture_sha256')
        self.assertEqual(analyze(self.directory, index),
                         json.loads((RESULTS / 'analysis.json').read_text()))

    def test_changed_affinity(self):
        self.metadata['affinity'] = [self.metadata['cpu'] + 1]
        self.save()
        self.reject()

    def test_changed_archive_source(self):
        self.index['source'] = 'different'
        self.reject()

    def test_changed_pair_order(self):
        self.metadata['observations'][0], self.metadata['observations'][1] = (
            self.metadata['observations'][1], self.metadata['observations'][0])
        self.save()
        self.reject()

    def test_incomplete_schedule(self):
        self.metadata['observations'].pop()
        self.save()
        self.reject()

    def test_wrong_function(self):
        self.mutate_export(lambda row: row.__setitem__('function', 'different'))
        self.reject()

    def test_dirty_source(self):
        self.mutate_export(lambda row: row['env'].__setitem__('git_dirty', True))
        self.reject()

    def test_truncated_arm(self):
        self.mutate_export(lambda row: row.__setitem__('budget_truncated', True))
        self.reject()

    def test_wrong_consumer_hash(self):
        self.mutate_export(lambda row: row.__setitem__('observed_hash', '0x2'))
        self.reject()

    def test_changed_call_protocol(self):
        self.mutate_export(lambda row: row['config'].__setitem__('min_total_seconds', 0.1))
        self.reject()

    def test_changed_batch(self):
        self.mutate_export(lambda row: row['points'][0].__setitem__('inner_repeats', 0))
        self.reject()

    def test_wrong_command_binding(self):
        self.metadata['commands'][self.metadata['observations'][0]['command_index']]['command'][2] = 'different'
        self.save()
        self.reject()


if __name__ == '__main__':
    unittest.main()
