"""Regression checks for oracle rejection, exact root identity, and capability modes."""
import contextlib
import copy
import io
import unittest
from unittest import mock

from scripts.oracle import real_algebraic_flint as oracle
from scripts.oracle.real_algebraic_qqbar import QQBar, Unavailable


def rat(n, d=1):
    from fractions import Fraction
    q = Fraction(n, d)
    return {"poly": [-q.numerator, q.denominator], "re": [q.numerator, q.denominator],
            "im": [0, 1], "prec": 8}


class Modes(unittest.TestCase):
    def test_missing_component_modes(self):
        with mock.patch.object(oracle, "probe_scalar", side_effect=Unavailable("missing")), \
             mock.patch.object(oracle, "probe_integer"), mock.patch.object(oracle, "probe_algebraic"), \
             contextlib.redirect_stderr(io.StringIO()) as output:
            self.assertEqual(oracle.preflight(False), {"scalar": False, "integer": True, "algebraic": True})
            self.assertIn("SKIP scalar", output.getvalue())
            with self.assertRaises(Unavailable):
                oracle.preflight(True)

    def test_available_mismatch_never_skips(self):
        with mock.patch.object(oracle, "probe_scalar", side_effect=oracle.OracleMismatch("wrong")):
            with self.assertRaises(oracle.OracleMismatch):
                oracle.preflight(False)

    def test_fixture_coverage_is_required(self):
        with self.assertRaises(oracle.OracleMismatch):
            oracle.validate_records([])
        with self.assertRaises(oracle.OracleMismatch):
            oracle.validate_records([{"kind": "result", "lib": "HexRealAlgebraic", "case": "zero",
                                      "op": "order", "value": {"schema": 1}}])


class ExactOracle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            oracle.probe_algebraic()
        except Unavailable as exc:
            raise unittest.SkipTest(str(exc)) from exc

    def setUp(self):
        self.q = QQBar()
        self.checker = oracle.Checker(self.q)
        self.addCleanup(self.q.close)

    def test_missing_general_roots_preserves_scalar_identity(self):
        self.q.general_roots = None
        self.assertEqual(self.q.compare(self.checker.value(rat(1)), self.q.number(1)), 0)
        with self.assertRaises(Unavailable):
            self.q.roots([self.q.number(-2), self.q.number(0), self.q.number(1)])

    def test_versions_are_pinned(self):
        import flint
        with mock.patch.object(flint, "__FLINT_VERSION__", "unsupported"):
            with self.assertRaises(Unavailable):
                QQBar()

    def test_order_mismatch_and_invalid_identity(self):
        d = {"a": rat(-3, 2), "b": rat(0), "compare": -1, "reverse": 1,
             "eq": False, "lt": True, "le": True, "gt": False, "ge": False,
             "min": rat(-3, 2), "max": rat(0)}
        self.checker.check("order", d)
        for key, value in (("compare", 0), ("lt", False), ("min", rat(0))):
            wrong = copy.deepcopy(d)
            wrong[key] = value
            with self.subTest(key=key), self.assertRaises(oracle.OracleMismatch):
                self.checker.check("order", wrong)
        wrong = rat(0)
        wrong["re"] = [10, 1]
        with self.assertRaises(oracle.OracleMismatch):
            self.checker.value(wrong)

    def test_nonreal_input_is_rejected(self):
        imaginary = {"poly": [1, 0, 1], "re": [0, 1], "im": [1, 1], "prec": 8}
        self.checker.check("reject", {"a": imaginary, "accepted": False})
        with self.assertRaises(oracle.OracleMismatch):
            self.checker.check("reject", {"a": imaginary, "accepted": True})
        with self.assertRaises(oracle.OracleMismatch):
            self.checker.value(imaginary)

    def test_complex_branch_and_order_mismatches(self):
        i = {"poly": [1, 0, 1], "re": [0, 1], "im": [1, 1], "prec": 8}
        minus_i = {**i, "im": [-1, 1]}
        d = {"a": rat(-1), "b": i, "conj": rat(-1), "re": rat(-1), "im": rat(0),
             "sqrt": i, "n": 2, "nthRoot": i, "lt": False, "le": False}
        self.checker.check("complex", d)
        for key, value in (("sqrt", minus_i), ("nthRoot", minus_i), ("le", True)):
            wrong = copy.deepcopy(d)
            wrong[key] = value
            with self.subTest(key=key), self.assertRaises(oracle.OracleMismatch):
                self.checker.check("complex", wrong)

    def test_general_algebraic_coefficients(self):
        sqrt2 = {"poly": [-2, 0, 1], "re": [3, 2], "im": [0, 1], "prec": 2}
        neg_sqrt2 = dict(sqrt2, re=[-3, 2])
        fourth = {"poly": [-2, 0, 0, 0, 1], "re": [5, 4], "im": [0, 1], "prec": 3}
        negative = dict(fourth, re=[-5, 4])
        d = {"coefficients": [neg_sqrt2, rat(0), rat(1)],
             "roots": [{"root": negative, "multiplicity": 1}, {"root": fourth, "multiplicity": 1}]}
        self.checker.check("algebraicRoots", d)
        wrong = copy.deepcopy(d)
        wrong["roots"].reverse()
        with self.assertRaises(oracle.OracleMismatch):
            self.checker.check("algebraicRoots", wrong)
        wrong = copy.deepcopy(d)
        wrong["roots"][0]["root"] = sqrt2
        with self.assertRaises(oracle.OracleMismatch):
            self.checker.check("algebraicRoots", wrong)

    def test_repeated_root_multiplicity(self):
        d = {"coefficients": [rat(1), rat(-2), rat(1)],
             "roots": [{"root": rat(1), "multiplicity": 2}]}
        self.checker.check("algebraicRoots", d)
        d["roots"][0]["multiplicity"] = 1
        with self.assertRaises(oracle.OracleMismatch):
            self.checker.check("algebraicRoots", d)
        with self.assertRaises(oracle.OracleMismatch):
            oracle.integer_roots({"poly": [1, -2, 1], "roots": [rat(1)], "multiplicities": [1]})

    def test_integer_root_disc_and_polynomial(self):
        d = {"poly": [-1, 0, 1], "roots": [rat(-1), rat(1)]}
        oracle.integer_roots(d)
        wrong = copy.deepcopy(d)
        wrong["roots"][0]["im"] = [1, 1]
        with self.assertRaises(oracle.OracleMismatch):
            oracle.integer_roots(wrong)
        wrong = copy.deepcopy(d)
        wrong["roots"][0]["poly"] = [2, 1]
        with self.assertRaises(oracle.OracleMismatch):
            oracle.integer_roots(wrong)

    def test_approximation_and_zero_root_set(self):
        d = {"a": rat(1, 2), "prec": 0, "center": [1, 2], "radius": [1, 1]}
        self.checker.check("approx", d)
        for key, value in (("center", [100, 1]), ("radius", [2, 1])):
            wrong = dict(d, **{key: value})
            with self.subTest(key=key), self.assertRaises(oracle.OracleMismatch):
                self.checker.check("approx", wrong)
        self.checker.check("algebraicRoots", {"coefficients": [], "roots": None})
        with self.assertRaises(oracle.OracleMismatch):
            self.checker.check("algebraicRoots", {"coefficients": [], "roots": []})


if __name__ == "__main__":
    unittest.main()
