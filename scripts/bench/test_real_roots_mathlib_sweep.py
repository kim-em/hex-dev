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
                "natural-6",
                "natural-8",
                "natural-10",
                "refined-2",
                "refined-4",
                "refined-6",
            ],
        )
        self.assertEqual(
            {pair.reference.module for pair in real_roots.SPEC.pairs},
            {"HexRealRootsMathlib.Baseline"},
        )
        self.assertEqual(
            len({pair.candidate.module for pair in real_roots.SPEC.pairs}), 6
        )

    def test_manifest_is_structurally_valid(self) -> None:
        sweep.validate_spec(real_roots.SPEC)


if __name__ == "__main__":
    unittest.main()
