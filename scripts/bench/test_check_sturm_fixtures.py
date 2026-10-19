from fractions import Fraction
import unittest

from scripts.bench.check_sturm_fixtures import center_query
from scripts.oracle.realroots_flint import _tarski_expected


class CenterQueryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            import flint  # noqa: F401
        except ImportError:
            raise unittest.SkipTest("python-flint is unavailable")

    def check_sum(self, head, query, lower, upper, expected):
        p, q, endpoints = center_query(
            dict(head=head, query=query, lower=lower, upper=upper))
        self.assertEqual(_tarski_expected(p, q, endpoints), expected)

    def test_nonconstant_queries(self):
        # Roots 1 and 2: opposite signs of 2x-3, positive signs of x.
        self.check_sum([2, -3, 1], [-3, 2], [0, 0], [3, 0], 0)
        self.check_sum([2, -3, 1], [0, 1], [0, 0], [3, 0], 2)

    def test_negative_offset_and_negative_precision(self):
        # Roots -3 and -2 are both negative, inside (-4, 0).
        self.check_sum([6, 5, 1], [0, 1], [-2, -1], [0, 0], -2)

    def test_huge_offset_preserves_query(self):
        z = 2**2048 + 1
        self.check_sum([z*z - 2, -2*z, 1], [-z, 1], [z-2, 0], [z+2, 0], 0)

    def test_rejected_domains(self):
        self.check_sum([1, -2, 1], [1], [0, 0], [4, 0], None)
        self.check_sum([2, -3, 1], [1], [1, 0], [3, 0], None)

    def test_fractional_endpoint_translation(self):
        p, q, endpoints = center_query(dict(
            head=[2, -3, 1], query=[0, 1], lower=[1, 2], upper=[13, 2]))
        self.assertEqual(p, [0, -1, 1])
        self.assertEqual(q, [1, 1])
        self.assertEqual([Fraction(n, 2**k) for n, k in endpoints],
                         [Fraction(-3, 4), Fraction(9, 4)])
        self.assertEqual(_tarski_expected(p, q, endpoints), 2)


if __name__ == "__main__":
    unittest.main()
