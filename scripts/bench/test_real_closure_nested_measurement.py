"""Reject mismatched raw evidence before producing a comparison summary."""
import copy
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from analyze_real_closure_nested import summarize
from real_closure_nested_measurement import ROOT, PARAMETERS, TRIALS, TARGET_NANOS, benchmark, digest, retained_command, schedule


class AnalysisTests(unittest.TestCase):
    def fixture(self, folder):
        binary = folder / 'hexrealclosure_nested_normalization'
        binary.write_bytes(b'synthetic executable')
        manifest = dict(status='completed', trials=TRIALS, parameters=[list(p) for p in PARAMETERS],
                        target_inner_nanos=TARGET_NANOS, commit='synthetic', cpu=0,
                        executable_sha256=digest(binary), snapshot_argv0=str(binary), oracle_python=sys.executable,
                        oracle_argv1=str(ROOT / 'scripts/oracle/real_closure_nested_normalization.py'),
                        analyzer_sha256=digest(ROOT / 'scripts/bench/analyze_real_closure_nested.py'),
                        capture_script_sha256=digest(ROOT / 'scripts/bench/real_closure_nested_measurement.py'),
                        protocol_sha256=digest(ROOT / 'reports/bench-results/real-closure-nested-protocol.md'),
                        oracle_sha256=digest(ROOT / 'scripts/oracle/real_closure_nested_normalization.py'),
                        expected_hashes={}, commands=[], measurements=[], functional_checks=[])
        def command(argv, output):
            manifest['commands'].append(dict(stdout=output, exit_code=0, incomplete=False, argv=argv))
        for depth, steps in PARAMETERS:
            manifest['expected_hashes'][f'{depth}:{steps}'] = dict(A='0x1', B='0x2')
            check = dict(depth=depth, steps=steps, outputs={})
            oracle_results = []
            for arm in 'AB':
                output = f'functional-{depth}-{steps}-{arm}.stdout'
                row = dict(depth=depth, steps=steps, eager=arm == 'B', hash=1 if arm == 'A' else 2,
                           value_roundtrip=True, roots_replayed=True, query_replayed=True)
                (folder / output).write_text(json.dumps(row)+'\n')
                check['outputs'][arm] = output
                command([str(binary), str(depth), str(steps), 'clean' if arm == 'A' else 'eager', 'plain'], output)
                oracle_results.append(dict(depth=depth, steps=steps, eager=arm == 'B', exact_value_checked=True, field_residue=[[1, 1]]))
            output = f'oracle-{depth}-{steps}.stdout'
            (folder / output).write_text(json.dumps(dict(oracle='python-flint', version='0.9.0', results=oracle_results))+'\n')
            check['oracle_output'] = output
            command([sys.executable, str(ROOT / 'scripts/oracle/real_closure_nested_normalization.py')]
                    + [str(folder / check['outputs'][arm]) for arm in 'AB'], output)
            manifest['functional_checks'].append(check)
        manifest['verify_output'] = 'verify.stdout'
        (folder / 'verify.stdout').write_text('synthetic successful verification\n')
        command([str(binary), 'verify'], 'verify.stdout')
        for index, (trial, depth, steps, arm) in enumerate(schedule()):
            name = benchmark(depth, steps, arm)
            row = dict(status='ok', kind='fixed', function=name, result_hash='0x1' if arm == 'A' else '0x2',
                       env=dict(git_commit='synthetic', git_dirty=False),
                       total_nanos=TARGET_NANOS, inner_repeats=1 if arm == 'A' else 2)
            output = f'{index}.stdout'
            (folder / output).write_text(json.dumps(row) + '\n')
            manifest['commands'].append(dict(stdout=output, exit_code=0, incomplete=False,
                argv=[str(binary), '_child', '--bench', name, '--fixed', '--min-total-nanos', str(TARGET_NANOS)]))
            manifest['measurements'].append(dict(trial=trial, depth=depth, steps=steps, arm=arm,
                                                output=output, rows=[row], exit_code=0))
        self.save(folder, manifest)
        return manifest

    def save(self, folder, manifest):
        manifest['artifacts'] = {p.name: digest(p) for p in folder.iterdir() if p.name != 'manifest.json'}
        (folder / 'manifest.json').write_text(json.dumps(manifest))

    def test_complete_synthetic_schedule_and_missing_arm(self):
        with tempfile.TemporaryDirectory() as name:
            folder = Path(name)
            manifest = self.fixture(folder)
            result = summarize(folder)
            self.assertEqual(result['complete_arms'], 96)
            self.assertTrue(all(r['paired_eager_over_clean_median'] == 0.5 for r in result['summary']))
            manifest['measurements'].pop()
            self.save(folder, manifest)
            with self.assertRaisesRegex(ValueError, 'order differs'):
                summarize(folder)

    def test_raw_and_command_mutations(self):
        mutations = [
            lambda m: m['commands'][0]['argv'].__setitem__(-1, '0'),
            lambda m: m['commands'][0].__setitem__('exit_code', 1),
            lambda m: m['commands'][0].__setitem__('incomplete', True),
            lambda m: m['measurements'][0]['rows'][0].__setitem__('inner_repeats', 17),
        ]
        for mutate in mutations:
            with self.subTest(mutation=mutate), tempfile.TemporaryDirectory() as name:
                folder = Path(name)
                manifest = self.fixture(folder)
                mutate(manifest)
                self.save(folder, manifest)
                with self.assertRaises(ValueError):
                    summarize(folder)

    def test_invalid_source_result_and_timing_even_after_rehash(self):
        mutations = [lambda r: r['env'].__setitem__('git_dirty', True),
                     lambda r: r.__setitem__('result_hash', '0xdead'),
                     lambda r: r.__setitem__('total_nanos', TARGET_NANOS-1),
                     lambda r: r.__setitem__('function', 'other')]
        for mutate in mutations:
            with self.subTest(mutation=mutate), tempfile.TemporaryDirectory() as name:
                folder = Path(name)
                manifest = self.fixture(folder)
                row = copy.deepcopy(manifest['measurements'][0]['rows'][0])
                mutate(row)
                manifest['measurements'][0]['rows'] = [row]
                (folder / '0.stdout').write_text(json.dumps(row) + '\n')
                self.save(folder, manifest)
                with self.assertRaisesRegex(ValueError, 'binding failed'):
                    summarize(folder)

    def test_ties_and_mixed_directions(self):
        with tempfile.TemporaryDirectory() as name:
            folder = Path(name)
            manifest = self.fixture(folder)
            for attempt in manifest['measurements']:
                row = attempt['rows'][0]
                row['inner_repeats'] = 1
                (folder / attempt['output']).write_text(json.dumps(row)+'\n')
            self.save(folder, manifest)
            self.assertTrue(all(r['direction'] == 'mixed/inconclusive' for r in summarize(folder)['summary']))
            attempt = manifest['measurements'][1]
            attempt['rows'][0]['inner_repeats'] = 2
            (folder / attempt['output']).write_text(json.dumps(attempt['rows'][0])+'\n')
            self.save(folder, manifest)
            self.assertEqual(summarize(folder)['summary'][0]['direction'], 'mixed/inconclusive')

    def test_functional_binary_and_source_binding_mutations(self):
        mutations = [lambda m: m['expected_hashes']['1:2'].__setitem__('A', '0xdead'),
                     lambda m: m.__setitem__('executable_sha256', 'wrong'),
                     lambda m: m.__setitem__('analyzer_sha256', 'wrong'),
                     lambda m: m['commands'][0]['argv'].__setitem__(0, 'other'),
                     lambda m: m['functional_checks'][0].__setitem__('oracle_output', 'verify.stdout'),
                     lambda m: m['commands'][2]['argv'].__setitem__(2, '/other/functional-1-2-A.stdout')]
        for mutate in mutations:
            with self.subTest(mutation=mutate), tempfile.TemporaryDirectory() as name:
                folder = Path(name)
                manifest = self.fixture(folder)
                mutate(manifest)
                self.save(folder, manifest)
                with self.assertRaises(ValueError): summarize(folder)
        with tempfile.TemporaryDirectory() as name:
            folder = Path(name)
            self.fixture(folder)
            (folder / '0.stdout').write_text('changed')
            with self.assertRaisesRegex(ValueError, 'artifact changed'): summarize(folder)


class RetentionTests(unittest.TestCase):
    def test_fake_success_timeout_and_spawn_failure(self):
        with tempfile.TemporaryDirectory() as name:
            folder = Path(name)
            output, errors = folder / '0.stdout', folder / '0.stderr'
            record = retained_command([sys.executable, '-c', 'print("fake endpoint")'], output, errors, timeout=5)
            self.assertEqual(record['exit_code'], 0)
            self.assertEqual(output.read_text(), 'fake endpoint\n')
            with self.assertRaises(subprocess.TimeoutExpired):
                retained_command([sys.executable, '-c', 'import time; print("attempt", flush=True); time.sleep(60)'],
                                 output, errors, timeout=0.1)
            record = json.loads(output.with_suffix('.command.json').read_text())
            self.assertTrue(record['incomplete'])
            self.assertLess(record['exit_code'], 0)
            self.assertEqual(output.read_text(), 'attempt\n')
            with self.assertRaises(FileNotFoundError):
                retained_command([str(folder / 'missing')], output, errors, timeout=5)
            record = json.loads(output.with_suffix('.command.json').read_text())
            self.assertTrue(record['incomplete'])
            self.assertIsNone(record['exit_code'])


if __name__ == '__main__':
    unittest.main()
