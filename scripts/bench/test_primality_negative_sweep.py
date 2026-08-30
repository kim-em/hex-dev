#!/usr/bin/env python3
"""Manifest checks for the ``Nat.Prime`` negative-result policy sweep."""

from __future__ import annotations

import unittest

from scripts.bench import fresh_module_sweep
from scripts.bench import primality_negative_sweep as negative


class NegativePolicySweepTests(unittest.TestCase):
    def test_ladder_spans_supported_range_and_both_outcomes(self) -> None:
        rows = [pair.metadata for pair in negative.SPEC.pairs if not pair.null_control]
        self.assertEqual(min(row["bits"] for row in rows), 25)
        self.assertEqual(max(row["bits"] for row in rows), 512)
        self.assertEqual(
            {row["outcome"] for row in rows},
            {"factor-found", "parity-factor-found", "exhausted"},
        )

    def test_policy_rows_record_seed_and_fixed_work_budget(self) -> None:
        rows = [pair.metadata for pair in negative.SPEC.pairs if not pair.null_control]
        self.assertTrue(all(row["seed"] == "numeral" for row in rows))
        self.assertEqual({row["rho_restarts"] for row in rows}, {1})
        self.assertEqual({row["rho_step_budget"] for row in rows}, {65536})

    def test_release_measurement_protocol_is_preregistered(self) -> None:
        self.assertEqual(negative.SPEC.required_samples, 6)
        self.assertEqual(negative.SPEC.max_pair_retries, 32)
        self.assertTrue(negative.SPEC.absolute_only)
        fresh_module_sweep.validate_spec(negative.SPEC)

    def test_every_probe_is_wired_into_lake(self) -> None:
        lakefile = (negative.ROOT / "lakefile.lean").read_text(encoding="utf-8")
        for module in fresh_module_sweep.probe_modules(negative.SPEC):
            self.assertIn(f"`{module}", lakefile, module)


if __name__ == "__main__":
    unittest.main()
