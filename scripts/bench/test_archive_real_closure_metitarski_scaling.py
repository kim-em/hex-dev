"""Recompute the real retained archive and reject altered data or report numbers."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from scripts.bench.archive_real_closure_metitarski_scaling import (
    ARCHIVE, REPORT, digest, verify)

ROOT = Path(__file__).resolve().parents[2]


class ArchiveTests(unittest.TestCase):
    def test_retained_real_archive(self):
        result = verify(ROOT/ARCHIVE, ROOT/REPORT)
        self.assertEqual(result['source'], '14b03f863df9341f411a1f3df7461f41b82d4ab7')
        self.assertEqual((result['attempts'], result['completed_samples']), (24, 24))
        self.assertEqual([r['completed_trials'] for r in result['rows']], [6]*4)

    def test_changed_raw_derived_or_report_data(self):
        changes = [
            ('measurements.json', lambda d: d['results'][0]['points'][0].update(total_nanos=1)),
            ('analysis.json', lambda d: d['rows'][0].update(median_ns=1)),
            ('archive.json', lambda d: d['omitted_snapshots'].update(hexrealclosure_bench='0'*64)),
            ('manifest.json', lambda d: d.update(source_hashes={})),
        ]
        for name, mutate in changes:
            with self.subTest(file=name), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)/'archive'
                shutil.copytree(ROOT/ARCHIVE, folder)
                path = folder/name
                value = json.loads(path.read_text())
                mutate(value)
                path.write_text(json.dumps(value))
                # Even a resealed archive index cannot legitimize wrong derived results.
                if name != 'archive.json':
                    index = json.loads((folder/'archive.json').read_text())
                    index['files'][name] = digest(path)
                    (folder/'archive.json').write_text(json.dumps(index))
                with self.assertRaises(ValueError):
                    verify(folder, ROOT/REPORT)
        for changed in ['report', 'archive-report', 'extra-file', 'frozen-source']:
            with self.subTest(change=changed), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)/'archive'
                shutil.copytree(ROOT/ARCHIVE, folder)
                report = Path(directory)/'report.md'
                shutil.copyfile(ROOT/REPORT, report)
                if changed == 'report':
                    report.write_text(report.read_text().replace('213.826', '213.827'))
                elif changed == 'archive-report':
                    path = folder/'README.md'
                    path.write_text(path.read_text().replace('213.826', '213.827'))
                    index = json.loads((folder/'archive.json').read_text())
                    index['files']['README.md'] = digest(path)
                    (folder/'archive.json').write_text(json.dumps(index))
                elif changed == 'extra-file':
                    (folder/'extra.json').write_text('{}')
                else:
                    (folder/'sources/bench/HexRealClosure/Bench.lean').write_text('changed source')
                with self.assertRaises(ValueError): verify(folder, report)


if __name__ == '__main__':
    unittest.main()
