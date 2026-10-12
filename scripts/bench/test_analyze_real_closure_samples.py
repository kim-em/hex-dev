"""Check retained archive identity and exact extraction provenance."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from scripts.bench.analyze_real_closure_samples import analyze, audit_archive


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.extracted = self.root / 'extracted'
        self.extracted.mkdir()
        self.archive = self.root / 'capture.tar.gz'
        data = b'{"source":"frozen"}\n'
        with tarfile.open(self.archive, 'w:gz') as stream:
            item = tarfile.TarInfo('metadata.json')
            item.size = len(data)
            stream.addfile(item, io.BytesIO(data))
        (self.extracted / 'metadata.json').write_bytes(data)
        self.index = self.root / 'archive-index.json'
        self.record = {'archive_sha256': hashlib.sha256(self.archive.read_bytes()).hexdigest(),
                       'retained_files': 1}
        self.index.write_text(json.dumps(self.record))

    def test_exact_archive_and_extraction(self):
        self.assertEqual(audit_archive(self.extracted, self.index), self.record)

    def test_changed_archive(self):
        self.archive.write_bytes(self.archive.read_bytes() + b'changed')
        with self.assertRaisesRegex(ValueError, 'archive digest'):
            audit_archive(self.extracted, self.index)

    def test_changed_count(self):
        self.record['retained_files'] = 2
        self.index.write_text(json.dumps(self.record))
        with self.assertRaisesRegex(ValueError, 'file count'):
            audit_archive(self.extracted, self.index)

    def test_changed_extracted_metadata(self):
        (self.extracted / 'metadata.json').write_text('{"source":"changed"}')
        with self.assertRaisesRegex(ValueError, 'extracted artifact'):
            audit_archive(self.extracted, self.index)

    def test_changed_cpu_affinity(self):
        (self.extracted / 'metadata.json').write_text(json.dumps({
            'status': 'completed', 'observations': [None] * 96,
            'cpu': 60, 'affinity': [61]}))
        with self.assertRaisesRegex(ValueError, 'affinity'):
            analyze(self.extracted)


if __name__ == '__main__':
    unittest.main()
