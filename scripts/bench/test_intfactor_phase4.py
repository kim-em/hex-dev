"""Failure evidence must outlive every collector rejection."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from scripts.bench import intfactor_phase4 as collector


class PreservationTests(unittest.TestCase):
    def exercise(self, action, error):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'result.json'
            args = argparse.Namespace(output=output, dirty_status='')
            def collect(args, attempt):
                attempt.record['state_before'] = collector.host_state(0)
                attempt.save()
                (attempt.directory / 'bench.json').write_text('{"partial": true}')
                return action(attempt)
            with patch.object(collector, 'collect', collect):
                with self.assertRaises(error):
                    collector.collect_attempt(args)
            record = json.loads(output.read_text())
            self.assertEqual(record['status'], 'rejected')
            self.assertEqual(record['error_type'], error.__name__)
            self.assertIn('source_sha256', record)
            self.assertIn('commit', record)
            self.assertIn('state_before', record)
            self.assertIn('state_after', record)
            self.assertEqual(json.loads(Path(str(output) + '.attempt/bench.json').read_text()),
                             {'partial': True})
            with self.assertRaisesRegex(RuntimeError, 'unaccepted'):
                collector.render(record)
            with self.assertRaises(FileExistsError):
                collector.Attempt(output)
            return record

    def test_inconclusive(self):
        # Use a real previously accepted full export, changing just one verdict.
        fixture = collector.ROOT / 'reports/bench-results/hex-int-factor-phase4-f80afaec-chungus2-cpu7.json'
        export = json.loads(fixture.read_text())['benchmark_export']
        next(r for r in export['results'] if r['kind'] == 'parametric')['verdict'] = 'inconclusive'
        record = self.exercise(lambda _: collector.validate_export(export), RuntimeError)
        self.assertIn("verdict=inconclusive", record["error"])

    def test_malformed_export(self):
        self.exercise(lambda _: json.loads('{'), json.JSONDecodeError)

    def test_subprocess_failure(self):
        def action(attempt):
            try:
                collector.run([sys.executable, '-c',
                    'import sys; print("raw-out", flush=True); print("raw-err", file=sys.stderr); sys.exit(9)'])
            finally:
                entry = attempt.record['commands'][-1]
                self.assertEqual(Path(entry['stdout']).read_text(), 'raw-out\n')
                self.assertEqual(Path(entry['stderr']).read_text(), 'raw-err\n')
                self.assertTrue(entry['executable_sha256'])
        record = self.exercise(action, subprocess.CalledProcessError)
        self.assertEqual(record['commands'][-1]['returncode'], 9)

    def test_timeout(self):
        def action(attempt):
            try:
                collector.run([sys.executable, '-c',
                    'import time, sys; print("partial-out", flush=True); print("partial-err", file=sys.stderr, flush=True); time.sleep(30)'], timeout=0.2)
            finally:
                entry = attempt.record['commands'][-1]
                self.assertEqual(Path(entry['stdout']).read_text(), 'partial-out\n')
                self.assertEqual(Path(entry['stderr']).read_text(), 'partial-err\n')
        self.exercise(action, subprocess.TimeoutExpired)

    def test_missing_executable(self):
        self.exercise(lambda _: collector.run(['/nonexistent/hex-benchmark']), FileNotFoundError)

    def test_build_failure_keeps_context(self):
        def action(attempt):
            collector.run([sys.executable, '-c', 'import sys; print("build failed"); sys.exit(1)'])
        record = self.exercise(action, subprocess.CalledProcessError)
        self.assertIn('bench/HexIntFactor/Bench.lean', record['source_sha256'])

    def test_benchmark_hash_precedes_wrapped_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            executable = Path(directory) / 'bench'
            executable.write_bytes(b'benchmark binary')
            attempt = collector.Attempt(Path(directory) / 'result.json')
            args = argparse.Namespace(dirty_status='')
            def run(command, **kwargs):
                if command[0] == 'lake':
                    return subprocess.CompletedProcess(command, 0, '', '')
                raise RuntimeError('audit failed')
            with patch.object(collector, 'BENCH', executable), \
                 patch.object(collector, 'run', run), \
                 patch.object(collector.socket, 'gethostname', return_value='chungus2'), \
                 patch.object(collector, 'host_state', return_value={}):
                with self.assertRaisesRegex(RuntimeError, 'audit failed'):
                    collector.collect_divisors(args, attempt, 7)
            record = json.loads(attempt.output.read_text())
            self.assertEqual(record['benchmark_executable_sha256'], collector.sha256(executable))

    def test_ecm_excludes_evidence_bookkeeping(self):
        result = subprocess.CompletedProcess(['ecm'], 0, '3 5\n' * collector.ECM_BATCH, '')
        result.elapsed_nanos = 256000
        with patch.object(collector, 'run', return_value=result), \
             patch.object(collector.time, 'monotonic_ns', side_effect=AssertionError('outer timing')):
            elapsed, rows = collector.ecm_batch('ecm', 15, 1)
        self.assertEqual(elapsed, 1000)
        self.assertEqual(rows, [[3, 5]] * collector.ECM_BATCH)

    def test_external_failure_preserves_export(self):
        self.exercise(lambda _: collector.ecm_batch('/nonexistent/ecm', 15, 1), FileNotFoundError)


class DivisorValidationTests(unittest.TestCase):
    def fixture(self):
        audit = []
        points = []
        for count in collector.DIVISOR_COUNTS:
            values = [1]
            for prime in collector.DIVISOR_PRIMES[:count.bit_length() - 1]:
                values += [d * prime for d in values]
            values.sort()
            audit.append(','.join(map(str, [count, values[-1], 42, *values])))
            points.extend(dict(param=count, trial_index=i, status='ok', result_hash='000000000000002a')
                          for i in range(7))
        export = {'results': [dict(function='Hex.IntFactorBench.runDivisors',
            config=dict(outer_trials=7, param_floor=64, param_ceiling=32768,
                target_inner_nanos=1000000000, max_seconds_per_call=10,
                signal_floor_multiplier=1, slope_tolerance=0.15, cache_mode='warm',
                verdict_warmup_fraction=.2, narrow_range_noise_floor=1.5,
                param_schedule=dict(kind='custom', params=list(collector.DIVISOR_COUNTS))),
            points=points, verdict_dropped_leading=1, verdict='consistent_with_declared_complexity')]}
        return export, '\n'.join(audit)

    def test_committed_operation_counts(self):
        from scripts.bench.divisor_model import census
        expected = json.loads((collector.ROOT /
            'reports/bench-results/hex-int-factor-divisor-operation-counts.json').read_text())
        self.assertEqual([census(n) for n in collector.DIVISOR_COUNTS], expected)

    def test_rejected_run_still_records_validation(self):
        export, audit = self.fixture()
        with tempfile.TemporaryDirectory() as directory:
            attempt = collector.Attempt(Path(directory) / 'result.json')
            attempt.record['status'] = 'rejected'
            (attempt.directory / 'bench.json').write_text(json.dumps(export))
            (attempt.directory / 'telemetry.json').write_text(json.dumps({'summary': {'contaminated': True}}))
            collector.inspect_divisors(attempt, attempt.directory, audit)
            record = json.loads(attempt.output.read_text())
            self.assertEqual(record['status'], 'rejected')
            self.assertEqual(record['scientific_validation']['status'], 'passed')
            self.assertTrue(record['telemetry']['summary']['contaminated'])
            self.assertEqual(record['benchmark_export'], export)

    def test_malformed_retained_export(self):
        with tempfile.TemporaryDirectory() as directory:
            attempt = collector.Attempt(Path(directory) / 'result.json')
            attempt.record['status'] = 'rejected'
            (attempt.directory / 'bench.json').write_text('{')
            collector.inspect_divisors(attempt, attempt.directory, '')
            self.assertEqual(attempt.record['status'], 'rejected')
            self.assertEqual(attempt.record['scientific_validation']['status'], 'failed')
            self.assertIn('benchmark_export', attempt.record['ingestion_errors'])

    def test_complete_output_and_trials(self):
        collector.validate_divisors(*self.fixture())

    def test_corrupt_middle_divisor(self):
        export, audit = self.fixture()
        rows = audit.splitlines()
        values = rows[-1].split(',')
        values[100] = '999'
        rows[-1] = ','.join(values)
        with self.assertRaisesRegex(ValueError, 'audit mismatch'):
            collector.validate_divisors(export, '\n'.join(rows))

    def test_missing_trial(self):
        export, audit = self.fixture()
        export['results'][0]['points'].pop()
        with self.assertRaisesRegex(ValueError, 'missing or extra'):
            collector.validate_divisors(export, audit)

    def test_changed_tolerance(self):
        export, audit = self.fixture()
        export['results'][0]['config']['slope_tolerance'] = .3
        with self.assertRaisesRegex(ValueError, 'configuration'):
            collector.validate_divisors(export, audit)

    def test_bad_hash(self):
        export, audit = self.fixture()
        export['results'][0]['points'][-1]['result_hash'] = '0000000000000000'
        with self.assertRaisesRegex(ValueError, 'hash failure'):
            collector.validate_divisors(export, audit)

    def test_inconclusive(self):
        export, audit = self.fixture()
        export['results'][0]['verdict'] = 'inconclusive'
        with self.assertRaisesRegex(RuntimeError, 'inconclusive'):
            collector.validate_divisors(export, audit)


if __name__ == '__main__':
    unittest.main()
