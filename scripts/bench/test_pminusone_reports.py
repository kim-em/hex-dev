"""Regression guards for policy-measurement provenance and completeness."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

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

proof_spec = importlib.util.spec_from_file_location(
    'pminusone_proof_report', Path(__file__).with_name('pminusone_proof_report.py'))
proof = importlib.util.module_from_spec(proof_spec)
proof_spec.loader.exec_module(proof)

class ProofProvenanceTests(unittest.TestCase):
    def collection(self, directory, name='table-2', commit='head', digest='source'):
        samples = []
        for i in range(1, 9):
            sample = {'round': i, 'build_order': ['reference', 'candidate'] if i % 2
                      else ['candidate', 'reference'], 'import_baseline_wall_nanos': 100}
            for role, enabled in [('reference', False), ('candidate', True)]:
                row = {'case': name, 'enabled': enabled,
                       'result': {'checked': True, 'attempts': 0, 'events': []}}
                sample[role] = {'wall_nanos': 110, 'compiler_output': 'info: Probe.lean:12:0: ' + json.dumps(row)}
                sample[role + '_workload_wall_nanos'] = 10
            samples.append(sample)
        record = {'measurement_state': 'complete',
                  'config': {'samples': 8, 'import_baseline_control': 'imports'},
                  'environment': {'git_commit': commit},
                  'source_sha256': {'Support.lean': digest},
                  'validity': {'release_quality': True},
                  'results': {'imports': {'samples': samples}, name: {
                      'samples': samples, 'workload_ratio_resolution': 'baseline-limited'}}}
        path = Path(directory) / (name + '.json')
        path.write_text(json.dumps(record))
        return path

    def test_missing_inputs_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.collection(directory)
            with self.assertRaisesRegex(AssertionError, 'incomplete input corpus'):
                proof.summarize([path])

    def test_mixed_commits_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            paths = [self.collection(directory), self.collection(directory, 'table-3', commit='other')]
            with self.assertRaisesRegex(AssertionError, 'mixed source commits'):
                proof.summarize(paths)

    def test_mixed_shared_sources_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            paths = [self.collection(directory), self.collection(directory, 'table-3', digest='other')]
            with self.assertRaisesRegex(AssertionError, 'mixed source hashes'):
                proof.summarize(paths)

    def test_unresolved_costs_do_not_pass_gate(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(proof, 'EXPECTED', {'table-2'}):
            result = proof.summarize([self.collection(directory)])
            self.assertTrue(result['retains_all_checked_successes'])
            self.assertFalse(result['families'][0]['resolved'])
            self.assertEqual(result['gate'], 'not-established')

if __name__ == '__main__':
    unittest.main()
