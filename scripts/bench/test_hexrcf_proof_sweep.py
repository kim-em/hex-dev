#!/usr/bin/env python3
"""Structural tests for the HexRCF fresh-module probe manifest."""

from __future__ import annotations

import unittest

from scripts.bench import fresh_module_sweep as sweep
from scripts.bench import hexrcf_proof_sweep as rcf


class ManifestTests(unittest.TestCase):
    def test_manifest_is_two_nulls_plus_five_pairs_per_case(self) -> None:
        self.assertEqual(len(rcf.SPEC.pairs), 17)
        self.assertEqual(
            [pair.name for pair in rcf.SPEC.pairs],
            ["fresh-build-null", "degree50-tactic-null", *[
                f"{case}-{component}"
                for case in ("quadratic", "degree10", "degree50")
                for component in ("reify", "search", "literal", "replay", "tactic")
            ]],
        )

    def test_null_controls_are_first_and_use_exact_module_identity(self) -> None:
        baseline, expensive = rcf.SPEC.pairs[:2]
        self.assertTrue(baseline.null_control)
        self.assertIs(baseline.reference, rcf.BASELINE)
        self.assertIs(baseline.candidate, rcf.BASELINE)
        self.assertEqual(baseline.metadata["interpretation"], "calibration-only")
        self.assertTrue(expensive.null_control)
        self.assertEqual(expensive.reference, expensive.candidate)
        self.assertEqual(expensive.reference.expected_axioms, rcf.ALLOWED_AXIOMS)
        self.assertEqual(expensive.metadata["magnitude"], "degree50-tactic")

    def test_sample_count_is_preregistered_and_balanced(self) -> None:
        self.assertEqual(rcf.SPEC.required_samples, 6)

    def test_substantive_pairs_remain_five_per_case(self) -> None:
        substantive = [pair for pair in rcf.SPEC.pairs if not pair.null_control]
        self.assertEqual(len(substantive), 15)
        for case in ("quadratic", "degree10", "degree50"):
            self.assertEqual(
                len([pair for pair in substantive if pair.name.startswith(case)]),
                5,
            )

    def test_only_replay_and_tactic_report_axioms(self) -> None:
        for pair in rcf.SPEC.pairs:
            if pair.null_control:
                self.assertEqual(pair.reference, pair.candidate, pair.name)
                continue
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

    def test_search_and_input_declare_the_same_literal(self) -> None:
        for module_case, macro in (
            ("Quadratic", "rcfQuadraticSentence"),
            ("Degree10", "rcfDegree10Sentence"),
            ("Degree50", "rcfDegree50Sentence"),
        ):
            expected = f"def input : Sentence := {macro}"
            for variant in ("Input", "Search"):
                source = sweep.probe_source(
                    f"HexRCF.ProofProbe.{module_case}.{variant}",
                    rcf.SPEC.src_dir,
                ).read_text(encoding="utf-8")
                self.assertIn(expected, source)

    def test_unmeasured_validation_covers_every_case(self) -> None:
        source = sweep.probe_source(
            "HexRCF.ProofProbe.Validate", rcf.SPEC.src_dir
        ).read_text(encoding="utf-8")
        for case, goal, certificate in (
            ("quadratic", "rcfQuadraticGoal", "rcfQuadraticCertificate"),
            ("degree10", "rcfDegree10Goal", "rcfDegree10Certificate"),
            ("degree50", "rcfDegree50Goal", "rcfDegree50Certificate"),
        ):
            self.assertIn(f"rcf_reify_probe {case} : {goal}", source)
            self.assertIn(f"rcf_literal_probe {case} : {certificate}", source)


if __name__ == "__main__":
    unittest.main()
