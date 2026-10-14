#!/usr/bin/env python3
"""Exercise the compiled Sturm export guard with synthetic parent documents.

These tests cover acceptance, regression and refusal, without collecting timing
samples or replacing LeanBench's statistical implementation.
"""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
GUARD = ROOT / '.lake/build/bin/hexsturm_compare_exports'
TEMPLATE = ROOT / 'reports/bench-results/sturm-sign-comparisons/rerun/results.json'


class ExportGuardTest(unittest.TestCase):
    def setUp(self):
        export = json.loads(TEMPLATE.read_text())
        result = export['results'][0]
        result['config']['outer_trials'] = 1
        result['points'] = [p for p in result['points'] if p['trial_index'] == 0]
        for p in result['points']:
            p.update(inner_repeats=1, total_nanos=100, per_call_nanos=100,
                     status='ok', error=None, part_of_verdict=True,
                     below_signal_floor=False)
        # The guard must recompute these, rather than trusting parent summaries.
        result['trial_summaries'] = []
        export['results'] = [result]
        self.documents = [deepcopy(export) for _ in range(8)]

    def check(self, expected):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            paths = []
            for i, document in enumerate(self.documents):
                path = out / f'{i}.json'
                path.write_text(json.dumps(document))
                paths.append(str(path))
            report = out / 'report.json'
            completed = subprocess.run([str(GUARD), str(report), *paths],
                                       text=True, capture_output=True)
            if expected == 'refuse':
                self.assertEqual(completed.returncode, 3, completed.stdout)
                self.assertFalse(report.exists())
                return None
            self.assertEqual(completed.returncode, expected, completed.stderr)
            return json.loads(report.read_text())

    def point(self, i):
        return self.documents[i]['results'][0]['points'][0]

    def test_stable_all_declared_inputs(self):
        report = self.check(0)
        self.assertEqual(len(report['comparisons']), 4)

    def test_three_trials_refused_even_if_complete_and_stable(self):
        # A registration default of three trials cannot override the SPEC's
        # fixed even comparison-block requirement.
        self.documents = self.documents[:3] + self.documents[4:7]
        self.check('refuse')

    def test_two_trials_refused(self):
        self.documents = self.documents[:2] + self.documents[4:6]
        self.check('refuse')

    def test_improvement(self):
        for i in range(4, 8):
            self.point(i)['per_call_nanos'] = 80
        self.assertEqual(self.check(0)['improvement_count'], 1)

    def test_different_source_function(self):
        for document in self.documents[4:]:
            document['results'][0]['function'] = 'Hex.SturmBench.other'
        self.check('refuse')

    def test_all_source_trials_below_floor(self):
        for i in range(4, 8):
            self.point(i)['below_signal_floor'] = True
        self.check(2)

    def test_missing_file_and_wrong_arguments(self):
        with tempfile.TemporaryDirectory() as directory:
            report = Path(directory) / 'report.json'
            for args in ([], [str(report), *(['does-not-exist.json'] * 8)]):
                result = subprocess.run([str(GUARD), *args], capture_output=True)
                self.assertEqual(result.returncode, 3)
                self.assertFalse(report.exists())

    def test_regression(self):
        for i in range(4, 8):
            self.point(i)['per_call_nanos'] = 112
        self.assertEqual(self.check(1)['regression_count'], 1)

    def test_one_outlier_does_not_replace_trial_median(self):
        self.point(4)['per_call_nanos'] = 1000
        self.check(0)

    def test_incomplete_identical_inputs(self):
        for document in self.documents:
            document['results'][0]['points'].pop()
        self.check('refuse')

    def test_mismatched_configuration(self):
        self.documents[7]['results'][0]['config']['target_inner_nanos'] *= 2
        self.check('refuse')

    def test_mismatched_source_configuration(self):
        for document in self.documents[4:]:
            document['results'][0]['config']['target_inner_nanos'] *= 2
        self.check('refuse')

    def test_one_ineligible_trial(self):
        self.point(4)['part_of_verdict'] = False
        self.check(2)

    def test_one_below_floor_trial(self):
        self.point(4)['below_signal_floor'] = True
        self.check(2)

    def test_wrong_result_hash(self):
        self.point(4)['result_hash'] = '0x1'
        self.check('refuse')

    def test_failed_measurement(self):
        self.point(4)['status'] = 'timeout'
        self.check('refuse')

    def test_budget_truncation(self):
        self.documents[4]['results'][0]['budget_truncated'] = True
        self.check('refuse')

    def test_duplicate_parameter(self):
        for document in self.documents:
            result = document['results'][0]
            result['config']['param_schedule']['params'][1] = result['points'][0]['param']
            result['points'][1]['param'] = result['points'][0]['param']
        self.check('refuse')

    def test_nonfinite_measurement(self):
        self.point(4)['per_call_nanos'] = 10 ** 310
        self.check('refuse')

    def test_wrong_parent_trial_index(self):
        self.point(4)['trial_index'] = 1
        self.check('refuse')

    def test_empty_schedule(self):
        for document in self.documents:
            result = document['results'][0]
            result['config']['param_schedule']['params'] = []
            result['points'] = []
        self.check('refuse')


if __name__ == '__main__':
    unittest.main()
