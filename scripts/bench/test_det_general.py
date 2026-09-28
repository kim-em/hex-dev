"""Admission rules for serial determinant proof measurements."""
import unittest
from pathlib import Path
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

    def test_reject_diagnostics_mismatched_imports_and_wrong_audit(self):
        for suffix, extra in (
            ('Hex', '\n#print axioms False.elim\n'),
            ('Hex', '\nset_option trace.Meta.synthInstance true\n'),
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
                self.assertNotIn(f'{det_general.PREFIX}.Numeric2Hex', modules)
                self.assertNotIn(f'{det_general.PREFIX}.Numeric2Mathlib', modules)


if __name__ == '__main__':
    unittest.main()
