#!/usr/bin/env python3
"""Unit tests for sampling-profile symbol classification."""

import unittest

from factor_sampling_profile import categorise


class CategoriseTest(unittest.TestCase):
    def test_public_hex_symbol_is_own_code(self) -> None:
        self.assertEqual(categorise("Hex.Nat.factor?"), "lean-own-code")

    def test_private_hex_symbol_is_own_code(self) -> None:
        self.assertEqual(
            categorise("_private.HexPrimality.Order.orderOfAux"),
            "lean-own-code",
        )

    def test_non_hex_private_symbol_is_not_own_code(self) -> None:
        self.assertNotEqual(categorise("_private.Init.Data.List.loop"),
                            "lean-own-code")


if __name__ == "__main__":
    unittest.main()
