"""Admission rules for serial determinant proof measurements."""
import unittest
from scripts.bench.det_general import Admission, Case, PAIRS, PROCESS_SECONDS, TOTAL_SECONDS


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


if __name__ == '__main__':
    unittest.main()
