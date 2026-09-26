"""Guard the experimental runner's shared allowance and timeout ordering."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from adversarial import dominates

RUNNER = Path(__file__).with_name('adversarial.py').resolve()


class Limits(unittest.TestCase):
    def test_admission_does_not_start_a_measurement(self):
        with tempfile.TemporaryDirectory(prefix='det-runner-guard-') as directory:
            destination = Path(directory) / 'variant' / 'case'
            result = subprocess.run([sys.executable, str(RUNNER), '--admission-only',
                str(destination), '--candidate', 'bounded'], capture_output=True,
                text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(destination.exists())

    def test_timeout_order(self):
        old = dict(family='dense', target='expanded', modulus=0, seed=10320,
                   rational=True, n=4, atoms=2, degree=2, support=3, bits=2)
        newer = dict(old, n=5, cleaned_target=None, quotient_entries=False)
        self.assertTrue(dominates(newer, old))
        self.assertFalse(dominates(dict(newer, transpose=True), old))
        self.assertFalse(dominates(dict(newer, denominator_bits=2), old))
        self.assertFalse(dominates(dict(newer, quotient_entries=True), old))
        self.assertTrue(dominates(dict(newer, denominator_bits=6), old))

    def refused(self, previous, elapsed, expected):
        with tempfile.TemporaryDirectory(prefix='det-runner-guard-') as directory:
            parent = Path(directory)
            old = parent / 'old' / 'case'
            old.mkdir(parents=True)
            (old / 'case.json').write_text(json.dumps(previous))
            (old / 'status.json').write_text(json.dumps(dict(elapsed_seconds=elapsed)))
            destination = parent / 'new' / 'case'
            result = subprocess.run([sys.executable, str(RUNNER), '--admission-only', str(destination),
                '--candidate', 'coeff', '--search-seconds', '3600'],
                capture_output=True, text=True, timeout=10)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(expected, result.stdout + result.stderr)
            self.assertFalse(destination.exists())

    def test_larger_timeout_is_refused(self):
        with tempfile.TemporaryDirectory(prefix='det-runner-guard-') as directory:
            root = Path(directory)
            old = root / 'small'
            old.mkdir()
            case = dict(candidate='coeff', reference='mathlib', family='dense',
                        target='expanded', modulus=0, seed=10320, rational=False,
                        n=3, atoms=2, degree=1, support=3, bits=2)
            (old / 'case.json').write_text(json.dumps(case))
            (old / 'status.json').write_text(json.dumps(dict(elapsed_seconds=10)))
            (old / 'failure.json').write_text(json.dumps(dict(state='timeout')))
            destination = root / 'larger'
            result = subprocess.run([sys.executable, str(RUNNER), '--admission-only', str(destination),
                '--candidate', 'coeff', '--n', '4'], capture_output=True,
                text=True, timeout=10)
            self.assertIn('larger than timeout', result.stderr)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(destination.exists())

    def test_mathlib_timeout_crosses_variant_roots(self):
        with tempfile.TemporaryDirectory(prefix='det-runner-guard-') as directory:
            parent = Path(directory)
            old = parent / 'old-variant' / 'small'
            old.mkdir(parents=True)
            case = dict(candidate='fused', reference='mathlib', family='dense',
                        target='expanded', modulus=0, seed=10320, rational=False,
                        n=3, atoms=2, degree=1, support=3, bits=2)
            (old / 'case.json').write_text(json.dumps(case))
            (old / 'status.json').write_text(json.dumps(dict(elapsed_seconds=10)))
            (old / 'failure.json').write_text(json.dumps(dict(state='timeout',
                command=['lake', 'build', '+Determinant.AdversarialSampleMathlib:olean'])))
            destination = parent / 'new-variant' / 'larger'
            result = subprocess.run([sys.executable, str(RUNNER), '--admission-only', str(destination),
                '--candidate', 'coeff', '--n', '4'], capture_output=True,
                text=True, timeout=10)
            self.assertIn('larger than Mathlib timeout', result.stderr)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(destination.exists())

    def test_relations_share_prior_allowance(self):
        self.refused(dict(candidate='relations', search_seconds=600), 500,
                     'insufficient remaining allowance')

    def test_variants_share_hour(self):
        self.refused(dict(candidate='intern', search_seconds=3600), 3500,
                     'insufficient remaining allowance')

    def test_lower_recorded_cap_persists(self):
        self.refused(dict(candidate='staged', search_seconds=600), 500,
                     'within 10 minutes')

    def test_unfinished_sibling_blocks(self):
        with tempfile.TemporaryDirectory(prefix='det-runner-guard-') as directory:
            parent = Path(directory)
            old = parent / 'old' / 'case'
            old.mkdir(parents=True)
            (old / 'case.json').write_text(json.dumps(dict(candidate='coeff')))
            result = subprocess.run([sys.executable, str(RUNNER), '--admission-only', str(parent/'new'/'case'),
                '--candidate', 'staged'], capture_output=True, text=True, timeout=10)
            self.assertIn('unfinished prior normalization case', result.stderr)
            self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main()
