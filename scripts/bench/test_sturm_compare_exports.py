#!/usr/bin/env python3
"""Exercise the compiled export guard with synthetic parametric and fixed documents.

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

    def test_repeated_export_path_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            paths = []
            for index, document in enumerate(self.documents):
                path = out / f'{index}.json'
                path.write_text(json.dumps(document))
                paths.append(str(path))
            paths[1] = paths[0]
            report = out / 'report.json'
            result = subprocess.run([str(GUARD), str(report), *paths], capture_output=True)
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


class FixedExportGuardTest(unittest.TestCase):
    check = ExportGuardTest.check

    def setUp(self):
        template = ROOT / 'reports/data/sign-det-maximal/workflow-9c6565e68e/0-maximalOne.json'
        export = json.loads(template.read_text())
        result = export['results'][0]
        result['config'].update(repeats=2, min_total_seconds=0.01)
        point = result['points'][0]
        result['points'] = [dict(point, repeat_index=i, inner_repeats=1_000_000,
                                 total_nanos=100_000_000, status='ok') for i in range(2)]
        result['hashes_agree'] = True
        result['observed_hash'] = point['result_hash']
        # Supplied statistics must not replace statistics of the actual points.
        result.update(median_nanos=1, min_nanos=1, max_nanos=1)
        self.documents = [deepcopy(export) for _ in range(8)]

    def result(self, arm):
        return self.documents[arm]['results'][0]

    def test_stable_and_recomputed_summaries(self):
        report = self.check(0)
        self.assertEqual(report['kind'], 'fixed')
        self.assertEqual(report['baseline_median'], 100)
        self.assertEqual(report['current_median'], 100)

    def test_regression(self):
        for arm in range(4, 8):
            for point in self.result(arm)['points']:
                point['total_nanos'] = 112_000_000
        self.assertEqual(self.check(1)['regression_count'], 1)

    def test_improvement(self):
        for arm in range(4, 8):
            for point in self.result(arm)['points']:
                point['total_nanos'] = 80_000_000
        self.assertEqual(self.check(0)['improvement_count'], 1)

    def test_pinned_upper_middle_median(self):
        for arm in range(4, 8):
            for point in self.result(arm)['points']:
                point['total_nanos'] = 80_000_000 if arm < 6 else 140_000_000
        self.assertEqual(self.check(1)['current_median'], 140)

    def test_normalize_inner_repeats(self):
        for arm in range(4, 8):
            for point in self.result(arm)['points']:
                point.update(inner_repeats=10_000_000, total_nanos=1_000_000_000)
        self.check(0)

    def test_one_outlier_preserves_median(self):
        self.result(4)['points'][0]['total_nanos'] = 1_000_000_000
        self.check(0)

    def test_missing_repeat(self):
        self.result(4)['points'].pop()
        self.check('refuse')

    def test_empty_schedule(self):
        for arm in range(8):
            self.result(arm)['config']['repeats'] = 0
            self.result(arm)['points'] = []
        self.check('refuse')

    def test_duplicate_repeat(self):
        self.result(4)['points'][1]['repeat_index'] = 0
        self.check('refuse')

    def test_reordered_repeat(self):
        self.result(4)['points'].reverse()
        self.check('refuse')

    def test_failed_repeat(self):
        self.result(4)['points'][0]['status'] = 'timeout'
        self.check('refuse')

    def test_zero_repeat_count(self):
        self.result(4)['points'][0]['inner_repeats'] = 0
        self.check('refuse')

    def test_zero_per_call_time(self):
        self.result(4)['points'][0].update(total_nanos=20_000_000, inner_repeats=40_000_000)
        self.check('refuse')

    def test_unhashed_repeat(self):
        self.result(4)['points'][0]['result_hash'] = None
        self.check('refuse')

    def test_missing_observed_hash(self):
        self.result(4)['observed_hash'] = None
        self.check('refuse')

    def test_hash_disagreement(self):
        self.result(4)['hashes_agree'] = False
        self.check('refuse')

    def test_zero_result_hash_is_valid(self):
        for arm in range(8):
            self.result(arm)['observed_hash'] = '0x0'
            for point in self.result(arm)['points']:
                point['result_hash'] = '0x0'
        self.check(0)

    def test_source_hashes_differ(self):
        for arm in range(4, 8):
            self.result(arm)['observed_hash'] = '0x1'
            for point in self.result(arm)['points']:
                point['result_hash'] = '0x1'
        self.check('refuse')

    def test_expected_hash_is_checked(self):
        for arm in range(8):
            self.result(arm)['config']['expected_hash'] = '0x1'
        self.check('refuse')

    def test_source_configurations_differ(self):
        for arm in range(4, 8):
            self.result(arm)['config']['min_total_seconds'] *= 2
        self.check('refuse')

    def test_budget_truncation(self):
        self.result(4)['budget_truncated'] = True
        self.check('refuse')

    def test_result_kind_changes(self):
        self.documents[4] = json.loads(TEMPLATE.read_text())
        self.check('refuse')


    def test_below_tuning_floor(self):
        self.result(4)['points'][0]['total_nanos'] = 9_999_999
        self.check('refuse')

    def test_invalid_configuration(self):
        for arm in range(8):
            self.result(arm)['config']['min_total_seconds'] = -1
        self.check('refuse')

    def test_matching_expected_hash(self):
        for arm in range(8):
            self.result(arm)['config']['expected_hash'] = self.result(arm)['observed_hash']
        self.check(0)

    def test_integer_normalization_at_threshold(self):
        for arm in range(4, 8):
            for point in self.result(arm)['points']:
                point['total_nanos'] = 110_999_999
        self.assertEqual(self.check(0)['current_median'], 110)

    def test_one_repeat_per_block(self):
        for arm in range(8):
            self.result(arm)['config']['repeats'] = 1
            self.result(arm)['points'] = self.result(arm)['points'][:1]
        self.check(0)

    def test_pool_points_before_taking_median(self):
        for arm, times in zip(range(4, 8), [(50, 50), (50, 50), (50, 200), (200, 200)]):
            for point, time in zip(self.result(arm)['points'], times):
                point['total_nanos'] = time * 1_000_000
        self.assertEqual(self.check(0)['current_median'], 50)

    def test_unhashable_result(self):
        self.result(4)['hashable'] = False
        self.check('refuse')

    def test_one_block_configuration_differs(self):
        self.result(4)['config']['min_total_seconds'] *= 2
        self.check('refuse')

    def test_one_block_function_differs(self):
        self.result(4)['function'] = 'different'
        self.check('refuse')

    def test_multiple_results(self):
        self.documents[4]['results'].append(deepcopy(self.result(4)))
        self.check('refuse')

    def test_mixed_result_kinds(self):
        self.documents[4]['results'].append(json.loads(TEMPLATE.read_text())['results'][0])
        self.check('refuse')

if __name__ == '__main__':
    unittest.main()
