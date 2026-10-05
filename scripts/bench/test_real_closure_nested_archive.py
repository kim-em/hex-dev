"""Check the real committed archive and reject mutations without recapturing."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
from analyze_real_closure_nested import digest
from check_real_closure_nested_archive import check_archive

ARCHIVE = Path(__file__).resolve().parents[2] / 'reports/bench-results/real-closure-nested-measurement-ca2e22'


class ArchiveTests(unittest.TestCase):
    def test_real_archive_independent_of_live_protocol(self):
        # An archive must not import the live capture script or read its sources.
        with patch.dict(sys.modules, {'real_closure_nested_measurement': None}):
            result = check_archive(ARCHIVE)
        self.assertEqual(result['complete_arms'], 96)
        self.assertEqual(len(result['summary']), 8)

    def test_mutations(self):
        mutations = ('raw', 'analysis', 'table', 'source', 'snapshot', 'inventory', 'path')
        for mutation in mutations:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as name:
                folder = Path(name) / 'archive'
                shutil.copytree(ARCHIVE, folder)
                a = json.loads((folder / 'archive.json').read_text())
                m = json.loads((folder / 'manifest.json').read_text())
                if mutation == 'raw':
                    (folder / m['measurements'][0]['output']).write_text('changed\n')
                elif mutation == 'analysis':
                    path = folder / 'analysis.json'
                    data = json.loads(path.read_text()); data['summary'][0]['clean_ms'] = 0
                    path.write_text(json.dumps(data))
                    a['files'][path.name] = digest(path)
                elif mutation == 'table':
                    path = folder / 'README.md'
                    path.write_text(path.read_text().replace('0.065335 (', '0.000000 (', 1))
                elif mutation == 'source':
                    path = folder / a['sources']['capture_script_sha256']
                    path.write_text(path.read_text() + '\n# changed\n')
                    a['files'][path.relative_to(folder).as_posix()] = digest(path)
                elif mutation == 'snapshot':
                    a['omitted_snapshot']['sha256'] = '0' * 64
                elif mutation == 'inventory':
                    (folder / 'unrecorded.stdout').write_text('unrecorded\n')
                elif mutation == 'path':
                    a['files']['../manifest.json'] = a['files'].pop('manifest.json')
                (folder / 'archive.json').write_text(json.dumps(a))
                with self.assertRaises(ValueError):
                    check_archive(folder)


if __name__ == '__main__':
    unittest.main()
