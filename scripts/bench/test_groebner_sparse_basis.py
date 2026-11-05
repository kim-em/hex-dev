"""Exact, multiplicity and forced-hash-collision checks for basis comparison."""
import copy
import unittest
from unittest.mock import patch
from scripts.bench.groebner_sparse_basis import same_basis


class BasisTests(unittest.TestCase):
    def basis(self):
        return [[[[1,0],1],[[0,0],2]],[[[0,1],1],[[0,0],3]]]

    def test_permuted_complete_basis(self):
        self.assertTrue(same_basis(self.basis(),'[x1+3,x0+2]:',2,5))

    def test_wrong_coefficient(self):
        self.assertFalse(same_basis(self.basis(),'[x0+2,x1+4]:',2,5))

    def test_missing_polynomial(self):
        self.assertFalse(same_basis(self.basis(),'[x0+2]:',2,5))

    def test_duplicate_polynomial(self):
        rows=self.basis();rows.append(copy.deepcopy(rows[0]))
        self.assertFalse(same_basis(rows,'[x0+2,x1+3]:',2,5))

    def test_forced_collision(self):
        with patch('scripts.bench.groebner_sparse_basis.fingerprint',return_value=b'collision'):
            self.assertTrue(same_basis(self.basis(),'[x1+3,x0+2]:',2,5))
            self.assertFalse(same_basis(self.basis(),'[x1+4,x0+2]:',2,5))

    def test_ordinary_binary_exponents(self):
        self.assertTrue(same_basis([[[[2],1]]],'[x0^2]:',1,2))
        self.assertFalse(same_basis([[[[2],1]]],'[x0]:',1,2))

    def test_rejects_boolean_coefficient(self):
        self.assertFalse(same_basis([[[[1],True]]],'[x0]:',1,2))

    def test_zero_ideal(self):
        self.assertTrue(same_basis([],'[]:',2,5))


if __name__=='__main__':unittest.main()
