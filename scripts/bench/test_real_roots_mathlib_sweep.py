#!/usr/bin/env python3
"""Manifest checks for the ``isolate_roots`` fresh-module suite."""

from __future__ import annotations

import unittest

from scripts.bench import fresh_module_sweep as sweep
from scripts.bench import real_roots_mathlib_sweep as real_roots


class ManifestTests(unittest.TestCase):
    def test_declared_cases_and_shared_baseline(self) -> None:
        self.assertEqual(
            [pair.name for pair in real_roots.SPEC.pairs],
            [
                "fresh-build-null",
                "natural-10-null",
                "natural-6",
                "natural-8",
                "natural-10",
                "refined-2",
                "refined-4",
                "refined-6",
                "refine-6",
            ],
        )
        substantive = [
            pair for pair in real_roots.SPEC.pairs if not pair.null_control
        ]
        self.assertEqual(
            {pair.reference.module for pair in substantive},
            {
                "HexRealRootsMathlib.ProofProbe.Baseline",
                "HexRealRootsMathlib.ProofProbe.Natural6",
            },
        )
        self.assertEqual(
            len({pair.candidate.module for pair in substantive}), 6
        )

    def test_shared_host_controls_and_sample_count(self) -> None:
        controls = real_roots.SPEC.pairs[:2]
        self.assertTrue(all(pair.null_control for pair in controls))
        self.assertTrue(
            all(pair.reference == pair.candidate for pair in controls)
        )
        self.assertEqual(real_roots.SPEC.required_samples, 6)

    def test_every_measured_module_has_identical_imports(self) -> None:
        imports = {
            tuple(sweep._parse_imports(
                sweep.probe_source(module, real_roots.SPEC.src_dir)
            ))
            for module in sweep.probe_modules(real_roots.SPEC)
        }
        self.assertEqual(
            imports, {("HexRealRootsMathlib.IsolateRootsElab",)}
        )

    def test_case_metadata_matches_probe_sources(self) -> None:
        cases = [
            pair for pair in real_roots.SPEC.pairs
            if pair.metadata.get("family") in {
                "natural-width", "width-2^-20"
            }
        ]
        for pair in cases:
            with self.subTest(pair=pair.name):
                source = sweep.probe_source(
                    pair.candidate.module, real_roots.SPEC.src_dir
                ).read_text(encoding="utf-8")
                type_source = source.split(":=", 1)[0]
                self.assertEqual(
                    type_source.count("(X - "),
                    pair.metadata["degree"],
                )
                width = "width := 2 ^ (-20 : ℤ)" in source
                self.assertEqual(
                    width, pair.metadata["width_bits"] == 20
                )

    def test_manifest_is_structurally_valid(self) -> None:
        sweep.validate_spec(real_roots.SPEC)


if __name__ == "__main__":
    unittest.main()
