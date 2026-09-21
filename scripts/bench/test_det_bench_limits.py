"""Timeout pruning and hard workflow limits, using synthetic child processes only."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from contextlib import ExitStack
from scripts.bench.det_bench_limits import TimeoutFrontier, reserve, supervise, STAGE_SECONDS


def case(stem='small', **kw):
    return dict(stem=stem, family='dense', carrier='Int', dimension=4, atoms=2,
                degree=2, support=4) | kw


class LimitsTests(unittest.TestCase):
    def test_timeout_prunes_repeat_and_every_dominating_case(self):
        frontier = TimeoutFrontier()
        frontier.observe(case(), 'Dispatch', 'timeout')
        for c in [case(), case('dimension', dimension=8), case('degree', degree=4),
                  case('atoms', atoms=4), case('support', support=16)]:
            self.assertEqual(frontier.blocker(c, 'Dispatch')['blocked_by'], 'small')
        self.assertIsNone(frontier.blocker(case('incomparable', dimension=8, degree=1), 'Dispatch'))
        self.assertIsNone(frontier.blocker(case('smaller', dimension=2), 'Dispatch'))

    def test_no_censoring_another_arm_or_mathematical_family(self):
        frontier = TimeoutFrontier()
        frontier.observe(case(), 'Packed', 'timeout')
        self.assertIsNone(frontier.blocker(case(), 'Mathlib'))
        self.assertIsNone(frontier.blocker(case(family='singular'), 'Packed'))
        self.assertIsNone(frontier.blocker(case(carrier='Rat'), 'Packed'))
        self.assertIsNone(frontier.blocker(case(modulus=3), 'Packed'))

    def test_ordinary_failure_does_not_claim_timeout(self):
        frontier = TimeoutFrontier()
        frontier.observe(case(), 'Mathlib', 'failed')
        self.assertIsNone(frontier.blocker(case(), 'Mathlib'))

    def test_total_reservations_and_no_implicit_retry(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'budget.json'
            self.assertEqual(sum(reserve(path, stage) for stage in STAGE_SECONDS), 3600)
            with self.assertRaisesRegex(ValueError, 'already attempted'):
                reserve(path, 'dispatch')

    def test_deadline_kills_descendant_in_separate_session_and_keeps_records(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            def worker(_deadline):
                child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'],
                                         start_new_session=True)
                (directory / 'child').write_text(str(child.pid))
                (directory / 'samples').write_text('retained sample')
                child.wait()
            started = time.monotonic()
            code = supervise(worker, .3, directory / 'status.json')
            self.assertEqual(code, 124)
            self.assertLess(time.monotonic() - started, 3)
            self.assertEqual((directory / 'samples').read_text(), 'retained sample')
            pid = int((directory / 'child').read_text())
            stat = Path(f'/proc/{pid}/stat')
            # SIGKILL is asynchronous; allow the kernel to finish scheduling it.
            until = time.monotonic() + 1
            while stat.exists() and stat.read_text().rsplit(')', 1)[1].split()[0] != 'Z' and time.monotonic() < until:
                time.sleep(.01)
            self.assertTrue(not stat.exists() or stat.read_text().rsplit(')', 1)[1].split()[0] == 'Z')
            self.assertEqual(json.loads((directory / 'status.json').read_text())['state'], 'workflow-budget-exhausted')

    def test_runner_skips_larger_builds_and_retains_missing_medians(self):
        from scripts.bench import det_packed_sweep as runner
        cases = [case(), case('larger', dimension=8), case('independent', family='singular')]
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            directory = Path(directory)
            manifest = directory / 'manifest.json'
            manifest.write_text(json.dumps(dict(cases=cases, profiles={}, infeasible=[])))
            classification = directory / 'classification.json'
            classification.write_text(json.dumps(dict(schedule_complete=True, subset=False,
                classification={c['stem']: dict(classification='closed-form') for c in cases})))
            output = directory / 'forced.json'
            stack.enter_context(patch.object(runner, 'MANIFEST', manifest))
            stack.enter_context(patch.object(sys, 'argv', ['runner', 'forced', str(output), '--classification', str(classification)]))
            stack.enter_context(patch.object(runner, 'cpu_lease', return_value=(0, type('Lease', (), {'close': lambda _: None})())))
            stack.enter_context(patch.object(runner.os, 'sched_setaffinity'))
            for name, value in [('validate_spec', None), ('warm_imports', None), ('validate_axioms', None),
                                ('environment', dict(repository={}, dependency_checkouts={})),
                                ('source_hashes', {}), ('cpu_topology', {}), ('artifact_sizes', {}), ('dirty_issues', [])]:
                stack.enter_context(patch.object(runner.sweep, name, return_value=value))
            calls = []
            def build(module, timeout, cpu, monitored, observer, **kw):
                calls.append(module)
                if module.endswith('smallLists'):
                    observer(module, dict(state='timeout'))
                    raise RuntimeError('synthetic timeout')
                return dict(state='complete', compiler_output='', wall_nanos=100)
            stack.enter_context(patch.object(runner.sweep, 'build_sample', side_effect=build))
            stack.enter_context(patch('builtins.print'))
            runner.main(time.monotonic() + 100)
            r = json.loads(output.read_text())
            self.assertEqual(sum(name.endswith('smallLists') for name in calls), 1)
            self.assertFalse(any(name.endswith('largerLists') or name.endswith('largerListsBaseline') for name in calls))
            self.assertTrue(any(name.endswith('largerPacked') for name in calls))
            self.assertTrue(any(name.endswith('independentLists') for name in calls))
            self.assertIsNone(r['summary']['larger']['arms']['Lists']['median_delta_ns'])
            self.assertTrue(r['schedule_complete'])
            self.assertEqual(len(r['samples']), 36)
            self.assertEqual(sum(s.get('state') == 'skipped-timeout' for s in r['samples']), 11)
            calls.clear()
            runner.main(time.monotonic() - 1)
            r = json.loads(output.read_text())
            self.assertEqual(calls, [])
            self.assertEqual(len(r['samples']), 36)
            self.assertTrue(all(s['state'] == 'skipped-budget' and s['delta_ns'] is None for s in r['samples']))

    def test_success_preserves_exit_status(self):
        with tempfile.TemporaryDirectory() as directory:
            self.assertEqual(supervise(lambda _: None, 1, Path(directory) / 'status.json'), 0)


if __name__ == '__main__':
    unittest.main()
