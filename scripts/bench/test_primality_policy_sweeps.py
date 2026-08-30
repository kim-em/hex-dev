#!/usr/bin/env python3
"""Regression tests for the primality policy measurement runners."""

from __future__ import annotations

import unittest

from scripts.bench import fresh_module_sweep
from scripts.bench import primality_elab_sweep as elab
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

    def test_static_array_header_size(self) -> None:
        generated = b".m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*9592"
        self.assertEqual(table.static_array_object_bytes(generated), 76_760)


class DecisionSweepTests(unittest.TestCase):
    def test_independent_oracle_classifies_committed_ladder(self) -> None:
        for name, n, expected, _family in policy.CASES:
            with self.subTest(name=name):
                self.assertEqual(policy.is_prime_64(n), expected)

    def test_ladder_has_both_outcomes_and_adversarial_primes(self) -> None:
        self.assertEqual({expected for _, _, expected, _ in policy.CASES}, {False, True})
        self.assertGreaterEqual(min(n for _, n, _, _ in policy.CASES), 100_000)
        chains = [n for _, n, expected, family in policy.CASES
                  if expected and family == "cunningham-chain"]
        self.assertGreaterEqual(len(chains), 2)
        self.assertLess(min(chains), 2_000_000)
        self.assertGreater(max(chains), 10_000_000)


class ElaboratorSweepTests(unittest.TestCase):
    def test_manifest_covers_both_routes_and_policy_outcomes(self) -> None:
        substantive = [pair for pair in elab.SPEC.pairs if not pair.null_control]
        self.assertEqual(
            {(pair.metadata["route"], pair.metadata["outcome"])
             for pair in substantive},
            {
                ("core", "accepted"),
                ("mathlib", "accepted"),
                ("core", "exhausted"),
                ("mathlib", "exhausted"),
                ("core", "over-budget"),
                ("mathlib", "over-budget"),
            },
        )
        self.assertEqual(
            {pair.metadata["fresh_module_budget_ms"] for pair in substantive},
            {10_000},
        )

    def test_boundary_is_accepted_at_512_and_rejected_at_513(self) -> None:
        by_name = {pair.name: pair for pair in elab.SPEC.pairs}
        self.assertEqual(by_name["core-512"].metadata["bits"], 512)
        self.assertEqual(by_name["mathlib-512"].metadata["bits"], 512)
        self.assertEqual(by_name["core-over-budget"].metadata["bits"], 513)
        self.assertEqual(by_name["mathlib-over-budget"].metadata["bits"], 513)
        self.assertEqual(by_name["core-exhausted"].metadata["bits"], 512)
        self.assertEqual(by_name["mathlib-exhausted"].metadata["bits"], 512)

    def test_each_route_has_a_null_control(self) -> None:
        self.assertEqual(
            {pair.metadata["route"] for pair in elab.SPEC.pairs
             if pair.null_control},
            {"core", "mathlib"},
        )

    def test_release_measurement_protocol_is_preregistered(self) -> None:
        self.assertEqual(elab.SPEC.required_samples, 6)
        self.assertEqual(elab.SPEC.max_pair_retries, 32)
        self.assertEqual(
            elab.SPEC.measurement,
            "paired-fresh-module-olean-wall-robust-null-v2",
        )
        fresh_module_sweep.validate_spec(elab.SPEC)

    def test_every_probe_is_wired_into_lake(self) -> None:
        lakefile = (elab.ROOT / "lakefile.lean").read_text(encoding="utf-8")
        for module in fresh_module_sweep.probe_modules(elab.SPEC):
            self.assertIn(f"`{module}", lakefile, module)

    def test_handlers_share_the_bounded_policy(self) -> None:
        core = (elab.ROOT / "HexPrimality/Elab.lean").read_text(encoding="utf-8")
        companion = (elab.ROOT / "HexPrimalityMathlib/NormNum.lean").read_text(
            encoding="utf-8"
        )
        self.assertIn("meta def primalityBitBudget : Nat := 512", core)
        self.assertIn("meta def primalityFuelBudget : Nat := 1040", core)
        self.assertIn("meta def primalityRhoRestartBudget : Nat := 2", core)
        self.assertIn("meta def primalityRhoStepBudget : Nat := 1 <<< 15", core)
        self.assertIn("let fuel := primalityFuel n", core)
        self.assertIn("unless withinPrimalityBudget n' do failure", companion)
        self.assertIn("unless withinPrimalityBudget n do", core)
        self.assertIn("let fuel := primalityFuel n'", companion)
        self.assertNotRegex(core, r"\b(?:Hex\.Nat\.)?isPrime\s")
        self.assertNotRegex(companion, r"\b(?:Hex\.Nat\.)?isPrime\s")


if __name__ == "__main__":
    unittest.main()
