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
        self.exercise(lambda _: collector.validate_export(export), RuntimeError)

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

    def test_external_failure_preserves_export(self):
        self.exercise(lambda _: collector.ecm_batch('/nonexistent/ecm', 15, 1), FileNotFoundError)


if __name__ == '__main__':
    unittest.main()
