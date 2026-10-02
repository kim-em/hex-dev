#!/usr/bin/env python3
"""Guard the attribution's exponent convention and repeated-base accounting."""
import unittest
from scripts.bench.primality_replay_attribution import parse_certificate, render, components, match_bases


class ReplayAttributionTests(unittest.TestCase):
    def test_nested_off_by_one_exponents(self):
        source = ('Hex.Nat.PrimeCert.pock3Sieve 199 9 2 8 4 '
                  '[(3, 2, Hex.Nat.PrimeCert.small 2), '
                  '(3, 0, Hex.Nat.PrimeCert.pock 7 [(2, 0, Hex.Nat.PrimeCert.small 3)])]')
        tree = parse_certificate(source)
        self.assertEqual(parse_certificate(render(tree)), tree)
        terms, counts = components(tree)
        self.assertIn('.beq 56', terms['product'])  # 2^(2+1) * 7^(0+1)
        self.assertEqual(counts['powers'], 5)  # 3 at root, 2 at child
        self.assertEqual(counts['divisor_tests'], 3)
        self.assertEqual(counts['repeated_bases'], 1)

    def test_changed_base_restarts_fermat(self):
        tree = parse_certificate('Hex.Nat.PrimeCert.pock3 199 9 2 8 '
                                 '[(3, 0, Hex.Nat.PrimeCert.small 2), '
                                 '(2, 0, Hex.Nat.PrimeCert.small 3)]')
        terms, counts = components(tree)
        self.assertEqual(counts['powers'], 4)
        self.assertIn('powModNat 3 198 199', terms['powers'])
        self.assertIn('powModNat 2 198 199', terms['powers'])
        self.assertEqual(counts['divisor_tests'], 0)

    def test_matching_preserves_factor_data(self):
        tree = parse_certificate('Hex.Nat.PrimeCert.pock3 199 9 2 8 '
                                 '[(3, 0, Hex.Nat.PrimeCert.small 2), '
                                 '(2, 0, Hex.Nat.PrimeCert.small 3)]')
        factors = [(e, child.copy()) for _, e, child in tree['fs']]
        match_bases(tree)
        self.assertEqual([(e, child) for _, e, child in tree['fs']], factors)
        self.assertEqual(tree['extra'], [9, 2, 8])
        self.assertEqual([a for a, _, _ in tree['fs']], [3, 3])
        self.assertEqual(components(tree)[1]['powers'], 3)

    def test_reject_trailing_node(self):
        with self.assertRaises(ValueError):
            parse_certificate('Hex.Nat.PrimeCert.small 2 Hex.Nat.PrimeCert.small 3')


if __name__ == '__main__': unittest.main()
