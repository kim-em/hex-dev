#!/usr/bin/env python3
"""Structural tests for the HexPrimalityMathlib proof-probe matrix."""

from __future__ import annotations

import unittest

from scripts.bench import fresh_module_sweep
from scripts.bench import primality_mathlib_proof_sweep as proof


class PrimalityMathlibProofSweepTests(unittest.TestCase):
    def test_components_and_routes_are_explicit(self) -> None:
        rows = [pair.metadata for pair in proof.SPEC.pairs if not pair.null_control]
        self.assertEqual(
            {row["component"] for row in rows},
            {"input", "certificate-literal", "reification", "kernel-replay", "full-tactic"},
        )
        self.assertEqual(
            {row["route"] for row in rows if row["component"] == "full-tactic"},
            {"primality", "norm-num-trial", "norm-num-certificate"},
        )

    def test_matrix_covers_typical_threshold_and_ceiling(self) -> None:
        by_name = {pair.name: pair for pair in proof.SPEC.pairs}
        self.assertEqual(by_name["primality-31"].metadata["bits"], 31)
        self.assertEqual(by_name["norm-num-trial"].metadata["bits"], 24)
        self.assertEqual(by_name["norm-num-threshold"].metadata["bits"], 25)
        self.assertEqual(by_name["primality-512"].metadata["bits"], 512)
        self.assertEqual(by_name["norm-num-512"].metadata["bits"], 512)

    def test_search_is_owned_by_core_and_not_duplicated(self) -> None:
        self.assertNotIn(
            "core-search",
            {pair.metadata["component"] for pair in proof.SPEC.pairs},
        )
        text = proof.__doc__ or ""
        self.assertIn("identical core computation", text)

    def test_release_protocol_and_lake_wiring(self) -> None:
        self.assertEqual(proof.SPEC.required_samples, 6)
        self.assertEqual(proof.SPEC.max_pair_retries, 32)
        self.assertTrue(proof.SPEC.absolute_only)
        fresh_module_sweep.validate_spec(proof.SPEC)
        lakefile = (proof.ROOT / "lakefile.lean").read_text(encoding="utf-8")
        for module in fresh_module_sweep.probe_modules(proof.SPEC):
            self.assertIn(f"`{module}", lakefile, module)

    def test_measured_modules_are_pairwise_import_isolated(self) -> None:
        for module in fresh_module_sweep.probe_modules(proof.SPEC):
            source = fresh_module_sweep.probe_source(module, proof.SPEC.src_dir)
            imports = [
                line for line in source.read_text(encoding="utf-8").splitlines()
                if line.startswith("import ")
            ]
            self.assertEqual(
                imports,
                ["import HexPrimalityMathlib.ProofProbe.Support"],
                module,
            )


if __name__ == "__main__":
    unittest.main()
