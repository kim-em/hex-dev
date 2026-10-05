"""Reject mismatched raw evidence before producing a comparison summary."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from analyze_real_closure_nested import summarize
from real_closure_nested_measurement import PARAMETERS, TRIALS, TARGET_NANOS, benchmark, digest, schedule


class AnalysisTests(unittest.TestCase):
    def fixture(self, folder):
        manifest = dict(status='completed', trials=TRIALS, parameters=[list(p) for p in PARAMETERS],
                        target_inner_nanos=TARGET_NANOS, commit='synthetic', cpu=0,
                        executable_sha256='synthetic', expected_hashes={}, commands=[], measurements=[])
        for depth, steps in PARAMETERS:
            manifest['expected_hashes'][f'{depth}:{steps}'] = dict(A='0x1', B='0x2')
        for index, (trial, depth, steps, arm) in enumerate(schedule()):
            name = benchmark(depth, steps, arm)
            row = dict(status='ok', kind='fixed', function=name, result_hash='0x1' if arm == 'A' else '0x2',
                       env=dict(git_commit='synthetic', git_dirty=False),
                       total_nanos=TARGET_NANOS, inner_repeats=1 if arm == 'A' else 2)
            output = f'{index}.stdout'
            (folder / output).write_text(json.dumps(row) + '\n')
            manifest['commands'].append(dict(stdout=output, exit_code=0, incomplete=False,
                argv=['synthetic', '_child', '--bench', name, '--fixed', '--min-total-nanos', str(TARGET_NANOS)]))
            manifest['measurements'].append(dict(trial=trial, depth=depth, steps=steps, arm=arm,
                                                output=output, rows=[row], exit_code=0))
        self.save(folder, manifest)
        return manifest

    def save(self, folder, manifest):
        manifest['artifacts'] = {p.name: digest(p) for p in folder.glob('*.stdout')}
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


if __name__ == '__main__':
    unittest.main()
