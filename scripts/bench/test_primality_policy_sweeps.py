#!/usr/bin/env python3
"""Regression tests for the primality policy measurement runners."""

from __future__ import annotations

import unittest

from scripts.bench import primality_policy_sweep as policy
from scripts.bench import primality_table_sweep as table


class TableSweepTests(unittest.TestCase):
    def test_candidate_plan(self) -> None:
        self.assertEqual(table.plan(10_000), (100, 4))
        self.assertEqual(table.plan(100_000), (317, 14))

    def test_extract_emission_ignores_lean_prefix(self) -> None:
        emission = "@[expose]\ndef primeTableBound : Nat := 10\n"
        output = f"scratch.lean:2:0: info: {emission}"
        self.assertEqual(table.extract_emission(output), emission)

    def test_failed_generation_is_not_reported_as_zero_replay(self) -> None:
        record = {"candidates": [{
            "bound": 10_000_000,
            "sqrt_bound": 3163,
            "batches": 132,
            "samples": [{
                "status": "generation-timeout",
                "generation_wall_nanos": 300_000_000_000,
            }],
        }]}
        row = table.summarize(record)[0]
        self.assertIsNone(row["replay_median_nanos"])
        self.assertEqual(row["sample_count"], 1)


class DecisionSweepTests(unittest.TestCase):
    def test_independent_oracle_classifies_committed_ladder(self) -> None:
        for name, n, expected, _family in policy.CASES:
            with self.subTest(name=name):
                self.assertEqual(policy.is_prime_64(n), expected)

    def test_ladder_has_both_outcomes_and_adversarial_primes(self) -> None:
        self.assertEqual({expected for _, _, expected, _ in policy.CASES}, {False, True})
        chains = [n for _, n, expected, family in policy.CASES
                  if expected and family == "cunningham-chain"]
        self.assertGreaterEqual(len(chains), 2)
        self.assertLess(min(chains), 2_000_000)
        self.assertGreater(max(chains), 10_000_000)


if __name__ == "__main__":
    unittest.main()
