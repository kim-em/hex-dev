"""Admission rules for serial determinant proof measurements."""
import unittest
from pathlib import Path
from contextlib import ExitStack
from collections import Counter
import shutil
import tempfile
from unittest.mock import Mock, patch
from scripts.bench import det_general
from scripts.bench.det_general import Admission, Case, CASES, PAIRS, PROCESS_SECONDS, TOTAL_SECONDS


class AdmissionTests(unittest.TestCase):
    def test_limits(self):
        self.assertEqual((PAIRS, PROCESS_SECONDS, TOTAL_SECONDS), (6, 60, 1800))
        small = Case('small', 'quotient', 2, 2)
        a = Admission(started=0)
        self.assertEqual(a.admit(small, 'Hex', 1), (True, None))
        a.observe(small, 'Hex', 'timeout')
        self.assertFalse(a.admit(Case('large', 'quotient', 4, 3), 'Hex', 2)[0])
        self.assertTrue(a.admit(small, 'Mathlib', 2)[0])
        self.assertTrue(a.admit(Case('other', 'numeric', 4, 3), 'Hex', 2)[0])
        self.assertTrue(a.admit(Case('incomparable', 'quotient', 4, 1), 'Hex', 2)[0])
        self.assertFalse(a.admit(small, 'Mathlib', TOTAL_SECONDS)[0])

    def test_only_timeout_blocks(self):
        a = Admission(started=0)
        a.observe(Case('failed', 'generic', 2, 2), 'Hex', 'failed')
        self.assertTrue(a.admit(Case('larger', 'generic', 4, 4), 'Hex', 1)[0])

    def test_smaller_allowance(self):
        a = Admission(started=10, seconds=30)
        self.assertTrue(a.admit(CASES[0], 'Hex', 39)[0])
        self.assertFalse(a.admit(CASES[0], 'Hex', 40)[0])


class ProbeTests(unittest.TestCase):
    root = Path(__file__).resolve().parents[2]

    def test_corpus(self):
        det_general.validate_sources(self.root, list(CASES))
        self.assertIn('OriginalQuadratic4', [c.name for c in CASES])
        self.assertIn('Tridiagonal4', [c.name for c in CASES])

    def test_audit_is_bound_to_the_exported_proof(self):
        unrelated = "'Other.result' depends on axioms: [propext, Classical.choice, Quot.sound]"
        module = f'{det_general.PREFIX}.Numeric2HexAudit'
        with self.assertRaises(RuntimeError):
            det_general.audited_axioms(module, unrelated)
        output = unrelated + f"\n'{det_general.PREFIX}.Numeric2Hex.result' depends on axioms: [sorryAx]"
        self.assertEqual(det_general.audited_axioms(module, output), ['sorryAx'])
        module = f'{det_general.PREFIX}.ResultNumeric2HexAudit'
        output = f"'{det_general.PREFIX}.ResultNumeric2Hex.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(det_general.audited_axioms(module, output), list(det_general.AXIOMS))

    def test_reject_diagnostics_mismatched_imports_and_wrong_audit(self):
        for suffix, extra in (
            ('Hex', '\n#print axioms False.elim\n'),
            ('Hex', '\nset_option trace.Meta.synthInstance true\n'),
            ('Hex', '\nset_option diagnostics true\n'),
            ('HexBaseline', '\nimport Mathlib\n'),
            ('HexAudit', '\n#print axioms False.elim\n'),
        ):
            with self.subTest(suffix=suffix, extra=extra), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                directory = root / 'bench/HexPolyDetMathlib/ProofProbe'
                directory.mkdir(parents=True)
                for source in (self.root / directory.relative_to(root)).glob('Numeric2*.lean'):
                    shutil.copy(source, directory)
                target = directory / f'Numeric2{suffix}.lean'
                target.write_text(target.read_text() + extra)
                with self.assertRaises(ValueError):
                    det_general.validate_sources(root, [CASES[0]])

    def test_reject_different_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            directory = root / 'bench/HexPolyDetMathlib/ProofProbe'
            directory.mkdir(parents=True)
            for source in (self.root / directory.relative_to(root)).glob('Numeric2*.lean'):
                shutil.copy(source, directory)
            target = directory / 'Numeric2Hex.lean'
            target.write_text(target.read_text().replace('= -2 := by', '= -3 := by'))
            with self.assertRaisesRegex(ValueError, 'same theorem'):
                det_general.validate_sources(root, [CASES[0]])

    @staticmethod
    def sample(module, *_args, **_kwargs):
        audit = module.endswith('Audit')
        output = f"'{module.removesuffix('Audit')}.result' depends on axioms: [propext, Classical.choice, Quot.sound]" if audit else ''
        result = {'wall_nanos': 10 if module.endswith('Baseline') else 30,
                  'compiler_output': output, 'axioms': list(det_general.AXIOMS) if audit else None}
        _args[3](module, result)  # The successful observer result has no state key.
        return result

    def run_mock(self, build=None, warm_error=None, **kwargs):
        from scripts.bench import fresh_module_sweep as sweep
        with tempfile.TemporaryDirectory() as tmp, ExitStack() as stack:
            for name, value in [('source_hashes', {}), ('environment', {})]:
                stack.enter_context(patch.object(sweep, name, return_value=value))
            stack.enter_context(patch.object(sweep, 'warm_imports', side_effect=warm_error))
            sample = stack.enter_context(patch.object(sweep, 'build_sample', side_effect=build or self.sample))
            stack.enter_context(patch('scripts.bench.cpu_lease.cpu_lease', return_value=(0, Mock())))
            stack.enter_context(patch('os.sched_setaffinity'))
            stack.enter_context(patch.dict('os.environ'))
            stack.enter_context(patch('builtins.print'))
            output = Path(tmp) / 'out.json'
            result = det_general.run(output, {'Numeric2'}, **kwargs)
            self.assertTrue(output.exists())
            return result, sample.call_args_list

    def test_complete_run_and_untimed_preparation(self):
        result, calls = self.run_mock()
        self.assertTrue(result['measurement_complete'])
        self.assertEqual(len(result['proof_preparation']), 2)
        self.assertEqual(len(result['audits']), 2)
        self.assertEqual(len(result['samples']), 12)
        self.assertTrue(all(r['net_nanos'] == 20 for r in result['samples']))
        self.assertEqual(result['summary']['Numeric2']['arms']['Hex']['median_net_nanos'], 20)
        modules = [call.args[0] for call in calls]
        self.assertLess(modules.index(f'{det_general.PREFIX}.Numeric2Hex'),
                        modules.index(f'{det_general.PREFIX}.Numeric2HexAudit'))

    def test_warmup_failure_is_retained(self):
        result, calls = self.run_mock(warm_error=RuntimeError('warm-up failed'))
        self.assertFalse(result['measurement_complete'])
        self.assertEqual(result['warmup']['state'], 'failed')
        self.assertIn('warm-up failed', result['warmup']['error'])
        self.assertEqual(calls, [])

    def test_process_timeout_and_aggregate_truncation_are_distinct(self):
        for seconds, state in [(1800, 'timeout'), (30, 'truncated')]:
            with self.subTest(state=state):
                counts = Counter()
                def build(module, *args, **kwargs):
                    counts[module] += 1
                    if module == f'{det_general.PREFIX}.Numeric2Hex' and counts[module] == 2:
                        args[3](module, {'state': 'timeout', 'timeout_seconds': args[0]})
                        raise RuntimeError('timed out')
                    return self.sample(module, *args, **kwargs)
                result, _ = self.run_mock(build, seconds=seconds)
                self.assertFalse(result['measurement_complete'])
                hex_rows = [r for r in result['samples'] if r['arm'] == 'Hex']
                self.assertEqual(hex_rows[0]['state'], state)
                if state == 'timeout':
                    self.assertTrue(all(r['state'] == 'skipped' for r in hex_rows[1:]))
                else:
                    self.assertTrue(all(r['state'] == 'complete' for r in hex_rows[1:]))

    def test_observed_success_with_bad_audit_becomes_failure(self):
        def build(module, *args, **kwargs):
            result = self.sample(module, *args, **kwargs)
            if module.endswith('Audit'):
                result['compiler_output'] = result['compiler_output'].replace('propext, Classical.choice, Quot.sound', 'sorryAx')
            return result
        result, _ = self.run_mock(build)
        self.assertFalse(result['measurement_complete'])
        self.assertTrue(all(r['state'] == 'failed' for r in result['audits']))
        self.assertTrue(all('audit failed' in r['proof']['reason'] for r in result['samples']))

    def test_failed_or_missing_audit_cannot_be_successful_timing(self):
        from scripts.bench import fresh_module_sweep as sweep
        for axioms in (None, ['sorryAx']):
            with self.subTest(axioms=axioms), tempfile.TemporaryDirectory() as tmp:
                def build(module, *_args, **_kwargs):
                    output = '' if axioms is None else f"'{module.removesuffix('Audit')}.result' depends on axioms: [{', '.join(axioms)}]"
                    return {'wall_nanos': 1, 'compiler_output': output,
                            'axioms': axioms if module.endswith('Audit') else None}
                with patch.object(sweep, 'warm_imports'), \
                     patch.object(sweep, 'source_hashes', return_value={}), \
                     patch.object(sweep, 'environment', return_value={}), \
                     patch.object(sweep, 'build_sample', side_effect=build) as sample, \
                     patch('scripts.bench.cpu_lease.cpu_lease', return_value=(0, Mock())), \
                     patch('os.sched_setaffinity'), patch.dict('os.environ'), \
                     patch('builtins.print'):
                    result = det_general.run(Path(tmp) / 'out.json', {'Numeric2'})
                self.assertFalse(result['measurement_complete'])
                self.assertTrue(all(r['state'] == 'failed' for r in result['audits']))
                self.assertTrue(all(r['state'] == 'skipped' for r in result['samples']))
                modules = [c.args[0] for c in sample.call_args_list]
                self.assertEqual(modules.count(f'{det_general.PREFIX}.Numeric2Hex'), 1)
                self.assertEqual(modules.count(f'{det_general.PREFIX}.Numeric2Mathlib'), 1)


if __name__ == '__main__':
    unittest.main()
