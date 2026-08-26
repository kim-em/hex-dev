#!/usr/bin/env python3
"""Manifest checks for the integer ``factor_poly`` fresh-module suite."""

from __future__ import annotations

import unittest

from scripts.bench import bz_mathlib_sweep as bz
from scripts.bench import fresh_module_sweep as sweep


class ManifestTests(unittest.TestCase):
    def test_declared_cases_and_shared_baseline(self) -> None:
        self.assertEqual(
            [pair.name for pair in bz.SPEC.pairs],
            [
                "fresh-build-null",
                "kernel-8-null",
                "factor-4",
                "factor-8",
                "factor-12",
                "irreducible-4",
                "irreducible-8",
                "irreducible-16",
                "kernel-4",
                "kernel-8",
                "multiplicity-8",
            ],
        )
        substantive = [
            pair for pair in bz.SPEC.pairs if not pair.null_control
        ]
        self.assertEqual(
            {pair.reference.module for pair in substantive},
            {
                "HexBerlekampZassenhausMathlib.ProofProbe.Baseline",
                "HexBerlekampZassenhausMathlib.ProofProbe.Factor8",
            },
        )
        self.assertEqual(
            len({pair.candidate.module for pair in substantive}), 9
        )

    def test_shared_host_controls_and_sample_count(self) -> None:
        controls = bz.SPEC.pairs[:2]
        self.assertTrue(all(pair.null_control for pair in controls))
        self.assertTrue(
            all(pair.reference == pair.candidate for pair in controls)
        )
        self.assertEqual(bz.SPEC.required_samples, 6)

    def test_kernel8_is_control_and_substantive_candidate(self) -> None:
        # Every probe carries the same large `import all` closure, so only the
        # costliest module is a distinct enough build magnitude to serve as the
        # expensive control (see the `KERNEL8` comment in the sweep manifest).
        # Pinning it here keeps a cheaper module from silently regressing the
        # controls back under the harness's 2.0x distinctness requirement.
        # This is the structural half of that contract: whether the control
        # really is 2.0x the baseline, and really is the costliest arm, is a
        # property of a measured artifact, and the harness enforces it there.
        cheap, expensive = bz.SPEC.pairs[:2]
        self.assertEqual(
            cheap.reference.module,
            "HexBerlekampZassenhausMathlib.ProofProbe.Baseline",
        )
        self.assertEqual(
            expensive.reference.module,
            "HexBerlekampZassenhausMathlib.ProofProbe.Kernel8",
        )
        substantive = {
            pair.candidate.module
            for pair in bz.SPEC.pairs
            if not pair.null_control
        }
        self.assertIn(expensive.reference.module, substantive)

    def test_every_measured_module_has_identical_imports(self) -> None:
        imports = {
            tuple(sweep._parse_imports(
                sweep.probe_source(module, bz.SPEC.src_dir)
            ))
            for module in sweep.probe_modules(bz.SPEC)
        }
        self.assertEqual(len(imports), 1)
        (shared,) = imports
        for module in (
            "HexBerlekampZassenhausMathlib.FactorTactic",
            "HexBerlekampZassenhausMathlib.KernelFactorTactic",
            "HexBasic.ArrayDecEq",
        ):
            self.assertIn(module, shared)

    def test_case_metadata_matches_probe_sources(self) -> None:
        cases = [
            pair for pair in bz.SPEC.pairs
            if pair.metadata.get("family") in {
                "factor-distinct",
                "irreducibility",
                "kernel-fallback",
                "multiplicity-attribution",
            }
        ]
        for pair in cases:
            with self.subTest(pair=pair.name):
                source = sweep.probe_source(
                    pair.candidate.module, bz.SPEC.src_dir
                ).read_text(encoding="utf-8")
                family = pair.metadata["family"]
                if family == "irreducibility":
                    self.assertIn(
                        f"X ^ {pair.metadata['degree']} - 2", source
                    )
                    self.assertIn("irreducibility", source)
                elif family == "kernel-fallback":
                    self.assertIn(f"X ^ {pair.metadata['degree']}", source)
                    self.assertIn("irreducibility!", source)
                else:
                    self.assertEqual(
                        source.count("(X ^ 2 +"),
                        pair.metadata["factors"],
                    )
                    self.assertIn("factor_poly", source)

    def test_manifest_is_structurally_valid(self) -> None:
        sweep.validate_spec(bz.SPEC)


if __name__ == "__main__":
    unittest.main()
