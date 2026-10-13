"""Check frozen root-route provenance and registered paired observations."""
import hashlib
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
import subprocess

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

    def test_changed_export_without_digest(self):
        path = self.directory / self.metadata['observations'][0]['export']
        path.write_text(path.read_text() + ' ')
        self.reject()

    def test_changed_source_snapshot(self):
        name = next(iter(self.metadata['source_hashes']))
        path = self.directory / 'sources' / name
        path.write_bytes(path.read_bytes() + b'\n')
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        self.metadata['source_hashes'][name] = digest
        self.metadata['artifacts']['sources/' + name] = digest
        self.save()
        self.reject()

    def test_changed_source_hash(self):
        name = next(iter(self.metadata['source_hashes']))
        self.metadata['source_hashes'][name] = 'different'
        self.save()
        self.reject()

    def test_changed_export_commit(self):
        self.mutate_export(lambda row: row['env'].__setitem__('git_commit', 'different'))
        self.reject()

    def test_failed_command(self):
        row = self.metadata['observations'][0]
        row['exit_code'] = 1
        self.metadata['commands'][row['command_index']]['exit_code'] = 1
        self.save()
        self.reject()

    def test_hash_check_failure(self):
        self.mutate_export(lambda row: row['expected_hash_check'].__setitem__('status', 'mismatch'))
        self.reject()

    def test_changed_archive_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'capture.tar.gz').write_bytes((RESULTS / 'capture.tar.gz').read_bytes() + b' ')
            (root / 'archive-index.json').write_text(json.dumps(self.index))
            with self.assertRaisesRegex(ValueError, 'archive digest'):
                audit_archive(self.directory, root / 'archive-index.json', 'capture_sha256')

    def test_failed_preparation(self):
        self.metadata['commands'][1]['exit_code'] = 1
        self.save()
        self.reject()

    def test_parent_driver_stderr(self):
        command = self.metadata['commands'][self.metadata['observations'][0]['command_index']]
        path = self.directory / command['stderr']
        path.write_bytes(b'panic: root producer failed\n')
        self.metadata['artifacts'][path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.save()
        self.reject()

    def test_available_git_source(self):
        root = RESULTS.parents[2]
        source = self.index['source']
        available = subprocess.run(['git', 'cat-file', '-e', source + '^{commit}'],
                                   cwd=root, capture_output=True)
        if available.returncode:
            self.skipTest('measured source commit is absent in this shallow checkout')
        def revision(ref):
            return subprocess.check_output(['git', 'rev-parse', ref], cwd=root, text=True).strip()
        self.assertEqual(revision('refs/tags/' + self.index['source_tag'] + '^{commit}'), source)
        for name, blob in self.index['source_git_blobs'].items():
            self.assertEqual(revision(source + ':' + name), blob)

    def test_changed_functional_output(self):
        path = self.directory / 'functional.stdout'
        path.write_bytes(path.read_bytes() + b'\n')
        self.metadata['artifacts'][path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.save()
        self.reject()

    def test_changed_binary_digest(self):
        self.metadata['binary_sha256'] = 'different'
        self.save()
        self.reject()


if __name__ == '__main__':
    unittest.main()
