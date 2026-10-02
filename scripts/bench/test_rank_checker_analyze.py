"""Reject lost samples, incorrect answers and changed scientific protocols."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from scripts.bench.rank_checker_analyze import journal, measurement


class MeasurementValidation(unittest.TestCase):
    def setUp(self):
        self.result = {
            'function': 'Hex.RankBench.Quotient.checkFull', 'kind': 'parametric',
            'budget_truncated': False, 'verdict': 'inconclusive',
            'config': {'outer_trials': 6, 'target_inner_nanos': 2000000000,
                       'slope_tolerance': 0.15, 'signal_floor_multiplier': 10,
                       'verdict_warmup_fraction': 0.2, 'param_floor': 128,
                       'param_ceiling': 192, 'cache_mode': 'warm',
                       'param_schedule': {'kind': 'custom', 'params': [128, 192]}},
            'points': [{'trial_index': t, 'param': n, 'status': 'ok',
                        'result_hash': '0xb', 'per_call_nanos': 123.0}
                       for t in range(6) for n in (128, 192)],
        }

    def validate(self, result, case='checkFull'):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'case.json').write_text(json.dumps({'results': [result]}))
            return measurement(root, 'case', case, [128, 192], 6)

    def test_selector_output_must_agree_at_each_rung(self):
        result = copy.deepcopy(self.result)
        result['function'] = 'Hex.RankBench.Quotient.blockFull'
        for p in result['points']:
            p['result_hash'] = hex(p['param'] * 777)
        self.validate(result, 'blockFull')
        result['points'][-1]['result_hash'] = '0x0'
        with self.assertRaises(ValueError):
            self.validate(result, 'blockFull')

    def test_inconclusive_remains_inconclusive(self):
        self.assertEqual(self.validate(self.result)['verdict'], 'inconclusive')

    def test_missing_duplicate_or_reordered_samples(self):
        mutations = (lambda p: p[:-1], lambda p: p + [p[0]], lambda p: p[::-1])
        for mutate in mutations:
            result = copy.deepcopy(self.result)
            result['points'] = mutate(result['points'])
            with self.assertRaises(ValueError):
                self.validate(result)

    def test_wrong_output_and_nonfinite_time(self):
        for field, value in [('result_hash', '0x0'), ('per_call_nanos', float('inf')),
                             ('status', 'timeout')]:
            result = copy.deepcopy(self.result)
            result['points'][0][field] = value
            with self.assertRaises(ValueError):
                self.validate(result)

    def test_weakened_protocol(self):
        for field, value in [('slope_tolerance', 1), ('outer_trials', 1),
                             ('signal_floor_multiplier', 1)]:
            result = copy.deepcopy(self.result)
            result['config'][field] = value
            with self.assertRaises(ValueError):
                self.validate(result)

    def test_modified_raw_export_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            row = {'label': 'case', 'command': ['bench', 'run', 'case'],
                   'exit_code': 0, 'output_errors': []}
            records = {'commands.jsonl': row,
                       'metadata.json': {'schedule': [['case', row['command']]]},
                       'completion.json': {'scheduled': 1, 'completed': 1, 'failures': []},
                       'case.json': {'verdict': 'inconclusive'}}
            for name, value in records.items():
                (root / name).write_text(json.dumps(value) + '\n')
            (root / 'retention.json').write_text(json.dumps({
                'completed_commands': ['case'],
                'sha256': {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                           for name in records}}))
            journal(root, ['case'])
            (root / 'case.json').write_text('{"verdict":"consistent_with_declared_complexity"}\n')
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                journal(root, ['case'])


if __name__ == '__main__':
    unittest.main()
