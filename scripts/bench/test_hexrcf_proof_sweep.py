#!/usr/bin/env python3
"""Structural tests for the HexRCF fresh-module probe manifest."""

from __future__ import annotations

import unittest

from scripts.bench import fresh_module_sweep as sweep
from scripts.bench import hexrcf_proof_sweep as rcf


class ManifestTests(unittest.TestCase):
    def test_five_pairs_per_fixed_case(self) -> None:
        self.assertEqual(len(rcf.SPEC.pairs), 15)
        self.assertEqual(
            [pair.name for pair in rcf.SPEC.pairs],
            [
                f"{case}-{component}"
                for case in ("quadratic", "degree10", "degree50")
                for component in ("reify", "search", "literal", "replay", "tactic")
            ],
        )

    def test_only_replay_and_tactic_report_axioms(self) -> None:
        for pair in rcf.SPEC.pairs:
            self.assertIsNone(pair.reference.expected_axioms, pair.name)
            expected = (
                rcf.ALLOWED_AXIOMS
                if pair.name.endswith(("-replay", "-tactic"))
                else None
            )
            self.assertEqual(pair.candidate.expected_axioms, expected, pair.name)

    def test_no_measured_import_path(self) -> None:
        sweep.validate_spec(rcf.SPEC)

    def test_every_measured_module_has_identical_imports(self) -> None:
        imports = {
            tuple(sweep._parse_imports(sweep.probe_source(module, rcf.SPEC.src_dir)))
            for module in sweep.probe_modules(rcf.SPEC)
        }
        self.assertEqual(
            imports,
            {(
                "HexRCF.ProofProbe.Generated",
                "HexRCF.ProofProbe.Generated",
            )},
        )

    def test_literal_and_replay_use_the_same_generated_macro(self) -> None:
        for module_case, macro in (
            ("Quadratic", "rcfQuadraticCertificate"),
            ("Degree10", "rcfDegree10Certificate"),
            ("Degree50", "rcfDegree50Certificate"),
        ):
            for variant in ("Literal", "Replay"):
                source = sweep.probe_source(
                    f"HexRCF.ProofProbe.{module_case}.{variant}",
                    rcf.SPEC.src_dir,
                ).read_text(encoding="utf-8")
                self.assertIn(f"def certificate : Certificate := {macro}", source)
                self.assertNotIn("build?", source)
                self.assertNotIn("certificateExpr", source)


if __name__ == "__main__":
    unittest.main()
