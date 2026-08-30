#!/usr/bin/env python3
"""Manifest checks for the ``Nat.Prime`` negative-result policy sweep."""

from __future__ import annotations

import unittest

from scripts.bench import primality_negative_sweep as negative


class NegativePolicySweepTests(unittest.TestCase):
    def test_ladder_spans_supported_range_and_both_outcomes(self) -> None:
        rows = [pair.metadata for pair in negative.SPEC.pairs if not pair.null_control]
        self.assertEqual(min(row["bits"] for row in rows), 25)
        self.assertEqual(max(row["bits"] for row in rows), 512)
        self.assertEqual({row["outcome"] for row in rows}, {"factor-found", "exhausted"})

    def test_every_policy_row_replays_one_seeded_restart(self) -> None:
        rows = [pair.metadata for pair in negative.SPEC.pairs if not pair.null_control]
        self.assertTrue(all(row["rho_restarts"] == 1 for row in rows))
        self.assertTrue(all(row["seed"] == "numeral" for row in rows))

    def test_null_controls_are_first_and_distinct(self) -> None:
        first, second = negative.SPEC.pairs[:2]
        self.assertTrue(first.null_control and second.null_control)
        self.assertNotEqual(first.reference.module, second.reference.module)


if __name__ == "__main__":
    unittest.main()
