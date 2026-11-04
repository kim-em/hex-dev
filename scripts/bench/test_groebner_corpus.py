"""Representation and field-boundary checks for the fixed F4 inputs."""
import unittest
from pathlib import Path
import re

import sympy

from scripts.bench.groebner_corpus import BATCH_SIZE, canonical, generated, public_input


class CorpusTests(unittest.TestCase):
    def test_library_batch_default(self):
        runtime = Path(__file__).resolve().parents[2] / 'HexGroebner/Runtime.lean'
        match = re.search(r'^\s+batchSize : Nat := (\d+)$', runtime.read_text(), re.MULTILINE)
        self.assertIsNotNone(match)
        self.assertEqual(BATCH_SIZE, int(match[1]))

    def test_characteristic_header(self):
        # The public -2 filename suffix means a two-bit prime, namely 3.
        data = b'x,y,\n3\nx^2+x+y,\n'
        with self.assertRaisesRegex(AssertionError, 'coefficient-field'):
            public_input(data, 2)
        lifted = public_input(data, 2, integer_lift=True)
        self.assertEqual(lifted['generators'], [[[[2, 0], 1], [[1, 0], 1], [[0, 1], 1]]])

    def test_integer_header_and_variable_precedence(self):
        data = b'z,a,\n0,\nz^2-a,\na^2-1,\n'
        value = public_input(data, 7)
        self.assertEqual(value['generators'], [[[[2, 0], 1], [[0, 1], 6]],
                                               [[[0, 2], 1], [[0, 0], 6]]])

    def test_canonical_ordinary_f2(self):
        # Combine coefficients and duplicate generators without x^2 = x.
        raw = [[([2], 1), ([1], 1), ([0], 2)], [([2], 3), ([1], 1)],
               [([4], 1), ([4], 1)]]
        self.assertEqual(canonical(raw, 2, 1), [[[[2], 1], [[1], 1]]])

    def test_seeded_dense_support(self):
        for p in [2, 32003, 2147483647]:
            a = generated('dense-quadratic', 4, p, 10987)
            self.assertEqual(a, generated('dense-quadratic', 4, p, 10987))
            self.assertNotEqual(a, generated('dense-quadratic', 4, p, 10988))
            self.assertEqual(len(a['generators']), 4)
            for polynomial in a['generators']:
                self.assertTrue(all(1 <= sum(e) <= 2 and 0 < c < p for e, c in polynomial))
            self.assertTrue(any(max(e) == 2 for polynomial in a['generators'] for e, _ in polynomial))

    def test_positive_dimension_substitution(self):
        # The first n-2 variables are polynomial expressions in the final two.
        for p in [2, 7]:
            value = generated('positive-dimensional', 5, p, 0)
            x = sympy.symbols('x:5')
            expressions = list(x)
            for i in reversed(range(3)):
                expressions[i] = sympy.expand(expressions[i+1] * expressions[i+2])
            for polynomial in value['generators']:
                expression = sum(c * sympy.prod(v**e for v, e in zip(x, powers))
                                 for powers, c in polynomial)
                substituted = expression.subs(dict(zip(x, expressions)), simultaneous=True)
                self.assertTrue(sympy.Poly(substituted, x[-2], x[-1], modulus=p).is_zero)


if __name__ == '__main__':
    unittest.main()
