"""Explicit declines remain failed proof attempts, with their raw timing retained."""
from contextlib import ExitStack
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from scripts.bench.det_symbolic_sweep import failed_build


class DeclineTests(unittest.TestCase):
    def sample(self, message, **extra):
        return dict(state='failed', returncode=1, wall_nanos=123,
                    compiler_output=f'error: Probe.lean:12:2: {message}\nerror: build failed\n', **extra)

    def test_budget_decline_retains_time_and_reason(self):
        reason = 'dimension budget exhausted (limit 16)'
        source = self.sample(f'det: symbolic determinant declined: {reason}')
        result = failed_build(source, RuntimeError('probe failed'))
        self.assertEqual(result['state'], 'declined')
        self.assertEqual(result['declines'], [dict(state='declined', reason=reason, kind='budget')])
        self.assertEqual(result['wall_nanos'], 123)
        self.assertEqual(result['compiler_output'], source['compiler_output'])
        self.assertEqual(source['state'], 'failed')

    def test_capability_and_inapplicability(self):
        result = failed_build(self.sample('det: declined: entry not evaluable'), 'failed')
        self.assertEqual(result['state'], 'declined')
        self.assertEqual(result['declines'][0]['kind'], 'capability')
        result = failed_build(self.sample('det: not applicable: unsupported literal'), 'failed')
        self.assertEqual(result['state'], 'not-applicable')

    def test_decline_trace_does_not_hide_other_failures(self):
        source = self.sample('det: symbolic determinant declined: budget exhausted')
        source['compiler_output'] += 'error: Other.lean:7:3: unknown identifier\n'
        self.assertEqual(failed_build(source, 'failed')['state'], 'failed')
        source = self.sample('det: symbolic determinant declined: budget exhausted')
        source['state'] = 'timeout'
        self.assertEqual(failed_build(source, 'failed')['state'], 'timeout')
        source['state'], source['returncode'] = 'failed', 137
        self.assertEqual(failed_build(source, 'failed')['state'], 'failed')
        source['returncode'] = 1
        source['compiler_output'] += 'error: Lean exited with code 137\n'
        self.assertEqual(failed_build(source, 'failed')['state'], 'failed')
        source = dict(state='complete', compiler_output=
            '[HexMatrix.certificate] {"route":"declined","reason":"an earlier attempt"}\n')
        self.assertEqual(failed_build(source, 'axiom audit failed')['state'], 'failed')


    def test_packed_sweep_never_counts_declines_as_completed_samples(self):
        from scripts.bench import det_packed_sweep as runner
        case = dict(stem='small', family='dense', carrier='Int', dimension=4,
                    atoms=2, degree=2, support=4)
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            directory = Path(directory)
            manifest = directory / 'manifest.json'
            manifest.write_text(json.dumps(dict(cases=[case], profiles={}, infeasible=[])))
            classification = directory / 'classification.json'
            classification.write_text(json.dumps(dict(schedule_complete=True, subset=False,
                classification={'small': dict(classification='closed-form')})))
            output = directory / 'forced.json'
            stack.enter_context(patch.object(runner, 'MANIFEST', manifest))
            stack.enter_context(patch.object(sys, 'argv', ['runner', 'forced', str(output),
                '--classification', str(classification)]))
            stack.enter_context(patch.object(runner, 'cpu_lease',
                return_value=(0, type('Lease', (), {'close': lambda _: None})())))
            stack.enter_context(patch.object(runner.os, 'sched_setaffinity'))
            for name, value in [('validate_spec', None), ('warm_imports', None), ('validate_axioms', None),
                                ('environment', dict(repository={}, dependency_checkouts={})),
                                ('source_hashes', {}), ('cpu_topology', {}), ('artifact_sizes', {}),
                                ('dirty_issues', [])]:
                stack.enter_context(patch.object(runner.sweep, name, return_value=value))
            def build(module, timeout, cpu, monitored, observer, **kw):
                if module.endswith('Baseline'):
                    return dict(state='complete', compiler_output='', wall_nanos=100)
                result = self.sample('det: symbolic determinant declined: proof nodes budget exhausted')
                observer(module, result)
                raise RuntimeError('probe failed')
            stack.enter_context(patch.object(runner.sweep, 'build_sample', side_effect=build))
            stack.enter_context(patch('builtins.print'))
            runner.main(time.monotonic() + 100)
            result = json.loads(output.read_text())
            self.assertEqual(len(result['samples']), 12)
            for sample in result['samples']:
                self.assertEqual(sample['candidate']['state'], 'declined')
                self.assertEqual(sample['candidate']['wall_nanos'], 123)
                self.assertIsNone(sample['delta_ns'])
            for arm in result['summary']['small']['arms'].values():
                self.assertIsNone(arm['median_delta_ns'])


if __name__ == '__main__':
    unittest.main()
