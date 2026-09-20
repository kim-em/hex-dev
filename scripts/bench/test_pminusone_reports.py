"""Regression guards for policy-measurement provenance and completeness."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    'pminusone_policy_report', Path(__file__).with_name('pminusone_policy_report.py'))
report = importlib.util.module_from_spec(spec)
spec.loader.exec_module(report)

class ProvenanceTests(unittest.TestCase):
    def collection(self, directory, name, source='source', executable='exe', resume=None):
        metadata={'type':'metadata','mode':'factor','source_sha256':{'Factor.lean':source},
                  'executable_sha256':{'factor':executable}}
        rows=[metadata]
        if resume is not None:
            rows.append({'type':'resume','metadata':resume})
        rows.append({'type':'complete'})
        path=Path(directory)/name
        path.write_text(''.join(json.dumps(row)+'\n' for row in rows))
        return path

    def test_missing_samples_cannot_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            path=self.collection(directory,'empty.jsonl')
            result=report.summarize([path])
            self.assertFalse(result['complete'])
            self.assertEqual(result['gate'],'incomplete')

    def test_mixed_source_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            before=self.collection(directory,'before.jsonl',source='four-slots')
            after=self.collection(directory,'after.jsonl',source='reserved-slot')
            with self.assertRaisesRegex(AssertionError,'mixed source'):
                report.summarize([before,after])

    def test_mixed_executable_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            before=self.collection(directory,'before.jsonl',executable='stale')
            after=self.collection(directory,'after.jsonl')
            with self.assertRaisesRegex(AssertionError,'mixed source or executable'):
                report.summarize([before,after])

    def test_mixed_resume_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path=self.collection(directory,'resumed.jsonl',resume={
                'source_sha256':{'Factor.lean':'different'},
                'executable_sha256':{'factor':'exe'}})
            with self.assertRaisesRegex(AssertionError,'mixed resume'):
                report.summarize([path])

if __name__ == '__main__':
    unittest.main()
