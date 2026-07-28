#!/usr/bin/env python3
"""Structural tests for the HexRCF fresh-module probe manifest."""

from __future__ import annotations

import re
import unittest
from pathlib import Path

from scripts.bench import fresh_module_sweep as sweep
from scripts.bench import hexrcf_proof_sweep as rcf


class ManifestTests(unittest.TestCase):
    def test_manifest_is_four_nulls_plus_five_pairs_per_case(self) -> None:
        self.assertEqual(len(rcf.SPEC.pairs), 19)
        self.assertEqual(
            [pair.name for pair in rcf.SPEC.pairs],
            [
                "fresh-build-null",
                "degree10-tactic-null",
                "degree50-tactic-null",
                "double-degree50-null",
                *[
                f"{case}-{component}"
                for case in ("quadratic", "degree10", "degree50")
                for component in ("reify", "search", "literal", "replay", "tactic")
                ],
            ],
        )

    def test_null_controls_are_first_and_use_exact_module_identity(self) -> None:
        baseline, intermediate, matched, expensive = rcf.SPEC.pairs[:4]
        self.assertTrue(baseline.null_control)
        self.assertIs(baseline.reference, rcf.BASELINE)
        self.assertIs(baseline.candidate, rcf.BASELINE)
        self.assertEqual(baseline.metadata["interpretation"], "calibration-only")
        self.assertTrue(intermediate.null_control)
        self.assertEqual(intermediate.reference, intermediate.candidate)
        self.assertEqual(
            intermediate.reference.expected_axioms, rcf.ALLOWED_AXIOMS
        )
        self.assertEqual(
            intermediate.metadata["magnitude"], "degree10-tactic"
        )
        self.assertTrue(matched.null_control)
        self.assertEqual(matched.reference, matched.candidate)
        self.assertEqual(
            matched.reference.module, "HexRCF.ProofProbe.Degree50.Tactic"
        )
        self.assertEqual(matched.reference.expected_axioms, rcf.ALLOWED_AXIOMS)
        self.assertEqual(matched.metadata["magnitude"], "degree50-tactic")
        self.assertTrue(expensive.null_control)
        self.assertEqual(expensive.reference, expensive.candidate)
        self.assertEqual(
            expensive.reference.module, "HexRCF.ProofProbe.DoubleDegree50"
        )
        self.assertEqual(expensive.reference.expected_axioms, rcf.ALLOWED_AXIOMS)
        self.assertEqual(
            expensive.metadata["magnitude"], "double-degree50-tactic"
        )

    def test_double_degree50_runs_two_tactics(self) -> None:
        source = sweep.probe_source(
            "HexRCF.ProofProbe.DoubleDegree50", rcf.SPEC.src_dir
        ).read_text(encoding="utf-8")
        tactics = re.findall(
            r"theorem (left|right) : rcfDegree50Goal :=\s*by\s+rcf\b",
            source,
        )
        self.assertEqual(tactics, ["left", "right"])
        self.assertIn(
            "theorem result : rcfDegree50Goal ∧ rcfDegree50Goal := "
            "⟨left, right⟩",
            source,
        )

    def test_sample_count_is_preregistered_and_balanced(self) -> None:
        self.assertEqual(rcf.SPEC.required_samples, 6)

    def test_schema_tracks_contract_change(self) -> None:
        self.assertEqual(rcf.SPEC.schema, "hexrcf-proof-probes-v6")

    def test_substantive_pairs_remain_five_per_case(self) -> None:
        substantive = [pair for pair in rcf.SPEC.pairs if not pair.null_control]
        self.assertEqual(len(substantive), 15)
        for case in ("quadratic", "degree10", "degree50"):
            self.assertEqual(
                len([pair for pair in substantive if pair.name.startswith(case)]),
                5,
            )

    def test_only_whole_tactic_pairs_have_acceptance_budgets(self) -> None:
        budgets = {}
        for pair in rcf.SPEC.pairs:
            has_budget = "tactic_budget_ms" in pair.metadata
            self.assertEqual(
                has_budget,
                not pair.null_control and pair.name.endswith("-tactic"),
                pair.name,
            )
            if has_budget:
                budgets[pair.name] = pair.metadata["tactic_budget_ms"]
        self.assertEqual(
            budgets,
            {
                "quadratic-tactic": 2_000,
                "degree10-tactic": 12_000,
                "degree50-tactic": 30_000,
            },
        )

    def test_axiom_reports_match_probe_roles(self) -> None:
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

    def test_every_measured_module_is_wired_into_lake(self) -> None:
        lakefile = Path("lakefile.lean").read_text(encoding="utf-8")
        for module in sweep.probe_modules(rcf.SPEC):
            self.assertIn(f"`{module}", lakefile, module)

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
