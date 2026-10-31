"""Regression checks that the independent division oracle rejects false results."""
import copy
import unittest

from scripts.oracle.groebner_division import check


class DivisionOracleTests(unittest.TestCase):
    def setUp(self):
        self.value = dict(p=2, variables=1, order="grevlex",
                          generators=[[[[2], 1], [[1], 1]]], dividend=[[[2], 1]],
                          quotients=[[[[0], 1]]], remainder=[[[1], 1]])

    def test_ordinary_characteristic_two(self):
        check(self.value)

    def test_false_boolean_quotient(self):
        self.value["remainder"] = []
        with self.assertRaises(ValueError):
            check(self.value)

    def test_reconstruction_failure(self):
        self.value["quotients"] = [[]]
        with self.assertRaises(ValueError):
            check(self.value)

    def test_reducible_remainder(self):
        self.value["quotients"] = [[]]
        self.value["remainder"] = self.value["dividend"]
        with self.assertRaises(ValueError):
            check(self.value)

    def test_invalid_arity_and_residue(self):
        for term in ([[0, 0], 1], [[0], 2], [[0], 0]):
            value = copy.deepcopy(self.value)
            value["quotients"] = [[term]]
            with self.assertRaises(AssertionError):
                check(value)

    def test_zero_and_empty_divisors(self):
        for divisors in ([], [[]], [[], []]):
            value = dict(self.value, generators=divisors,
                         quotients=[[] for _ in divisors], remainder=self.value["dividend"])
            check(value)

    def test_zero_variables_nonmonic(self):
        check(dict(p=7, variables=0, order="lex", generators=[[], [[[], 3]]],
                   dividend=[[[], 5]], quotients=[[], [[[], 4]]], remainder=[]))


if __name__ == "__main__":
    unittest.main()
