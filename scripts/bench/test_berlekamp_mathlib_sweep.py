#!/usr/bin/env python3
"""Manifest checks for the ``factor_poly`` fresh-module suite."""

from __future__ import annotations

import unittest

from scripts.bench import berlekamp_mathlib_sweep as berlekamp
from scripts.bench import fresh_module_sweep as sweep


class ManifestTests(unittest.TestCase):
    def test_declared_cases_and_shared_baseline(self) -> None:
        self.assertEqual(
            [pair.name for pair in berlekamp.SPEC.pairs],
            [
                "fresh-build-null",
                "irreducible-16-null",
                "factor-4",
                "factor-8",
                "factor-12",
                "irreducible-4",
                "irreducible-8",
                "irreducible-16",
                "multiplicity-8",
            ],
        )
        substantive = [
            pair for pair in berlekamp.SPEC.pairs if not pair.null_control
        ]
        self.assertEqual(
            {pair.reference.module for pair in substantive},
            {
                "HexBerlekampMathlib.ProofProbe.Baseline",
                "HexBerlekampMathlib.ProofProbe.Factor8",
            },
        )
        self.assertEqual(
            len({pair.candidate.module for pair in substantive}), 7
        )

    def test_shared_host_controls_and_sample_count(self) -> None:
        controls = berlekamp.SPEC.pairs[:2]
        self.assertTrue(all(pair.null_control for pair in controls))
        self.assertTrue(
            all(pair.reference == pair.candidate for pair in controls)
        )
        self.assertEqual(berlekamp.SPEC.required_samples, 6)

    def test_every_measured_module_has_identical_imports(self) -> None:
        imports = {
            tuple(sweep._parse_imports(
                sweep.probe_source(module, berlekamp.SPEC.src_dir)
            ))
            for module in sweep.probe_modules(berlekamp.SPEC)
        }
        self.assertEqual(
            imports,
            {(
                "HexBerlekamp.IrreducibilityElab",
                "HexBerlekampMathlib.FactorTactic",
                "HexBerlekamp.IrreducibilityElab",
                "HexBerlekampMathlib.FactorTactic",
            )},
        )

    def test_case_metadata_matches_probe_sources(self) -> None:
        cases = [
            pair for pair in berlekamp.SPEC.pairs
            if pair.metadata.get("family") in {
                "factor-distinct", "irreducibility", "multiplicity-attribution"
            }
        ]
        for pair in cases:
            with self.subTest(pair=pair.name):
                source = sweep.probe_source(
                    pair.candidate.module, berlekamp.SPEC.src_dir
                ).read_text(encoding="utf-8")
                if pair.metadata["family"] == "irreducibility":
                    self.assertIn(
                        f"X ^ {pair.metadata['degree']} + 2", source
                    )
                    self.assertIn("irreducibility", source)
                else:
                    self.assertEqual(
                        source.count("(X ^ 2 +"),
                        pair.metadata["factors"],
                    )
                    self.assertIn("factor_poly", source)

    def test_manifest_is_structurally_valid(self) -> None:
        sweep.validate_spec(berlekamp.SPEC)


if __name__ == "__main__":
    unittest.main()
