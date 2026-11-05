"""Memory observations remain optional when a measured process is killed."""
from pathlib import Path
import tempfile
import errno
import json
from unittest import mock
import unittest

from scripts.bench.groebner_cli_measure import read_rss, atomic_json, checkpoint_sample


class RssTests(unittest.TestCase):
    def test_missing_or_interrupted_output(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'rss'
            self.assertIsNone(read_rss(path))
            for text in ['', '\n', 'Command terminated by signal 9\n', 'partial']:
                path.write_text(text)
                self.assertIsNone(read_rss(path))

    def test_completed_failure_memory(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'rss'
            path.write_text('Command exited with non-zero status 1\n12345\n')
            self.assertEqual(read_rss(path), 12345)

    def test_zero_and_malformed_values(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'rss'
            path.write_text('0\n')
            self.assertEqual(read_rss(path), 0)
            for text in ['-1', '1.5', '123 KiB', '١٢٣']:
                path.write_text(text)
                self.assertIsNone(read_rss(path))


class CheckpointTests(unittest.TestCase):
    def test_partial_write_preserves_previous_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'metadata.json'
            atomic_json(path, {'samples': [{'wall_nanos': 123456789}]})
            previous = path.read_bytes()
            def fail(value, stream, **kwargs):
                stream.write('{"partial":')
                raise OSError(errno.ENOSPC, 'disk full')
            with mock.patch('scripts.bench.groebner_cli_measure.json.dump', side_effect=fail):
                with self.assertRaises(OSError):
                    atomic_json(path, {'samples': []})
            self.assertEqual(path.read_bytes(), previous)
            self.assertFalse(path.with_name('metadata.json.pending').exists())

    def test_failed_replace_preserves_previous_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'metadata.json'
            atomic_json(path, {'campaign_status': 'running'})
            with mock.patch('scripts.bench.groebner_cli_measure.os.replace',
                            side_effect=OSError(errno.ENOSPC, 'disk full')):
                with self.assertRaises(OSError):
                    atomic_json(path, {'campaign_status': 'completed'})
            self.assertEqual(json.loads(path.read_text()), {'campaign_status': 'running'})

    def test_exact_sample_journal_survives_metadata_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            metadata = {'samples': []}
            atomic_json(root / 'metadata.json', metadata)
            record = {'schedule_index': 0, 'wall_nanos': 1234567890123,
                      'command': ['producer', '--scheduling', 'degree'], 'status': 'ok'}
            with mock.patch('scripts.bench.groebner_cli_measure.atomic_json',
                            side_effect=OSError(errno.ENOSPC, 'disk full')):
                with self.assertRaises(OSError):
                    checkpoint_sample(root, metadata, record)
            self.assertEqual(json.loads((root / 'samples.jsonl').read_text()), record)
            self.assertEqual(json.loads((root / 'metadata.json').read_text()), {'samples': []})

    def test_checkpoint_preserves_precise_samples_in_order(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            metadata = {'samples': []}
            rows = [{'schedule_index': i, 'wall_nanos': 9876543210+i} for i in range(3)]
            for row in rows:
                checkpoint_sample(root, metadata, row)
            self.assertEqual([json.loads(line) for line in
                              (root / 'samples.jsonl').read_text().splitlines()], rows)
            self.assertEqual(json.loads((root / 'metadata.json').read_text()), metadata)


if __name__ == '__main__':
    unittest.main()
