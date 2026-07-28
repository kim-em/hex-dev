#!/usr/bin/env python3
"""Structural tests for the HexRCF fresh-module probe manifest."""

from __future__ import annotations

import re
import shlex
import unittest

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

    def test_shared_host_recipe_requests_retry_headroom(self) -> None:
        source = (sweep.ROOT / "SPEC/Libraries/hex-rcf.md").read_text(
            encoding="utf-8"
        )
        match = re.search(
            r"```bash\n(?P<command>python3 "
            r"scripts/bench/hexrcf_proof_sweep\.py.*?\n)```",
            source,
            re.DOTALL,
        )
        self.assertIsNotNone(match)
        assert match is not None
        command = match.group("command").replace("\\\n", " ")
        argv = shlex.split(command)[2:]
        args = sweep.parse_args(rcf.SPEC.description, argv)
        self.assertEqual(args.samples, rcf.SPEC.required_samples)
        self.assertTrue(args.shared_host)
        self.assertEqual(args.expected_host, "chungus2")
        self.assertEqual(args.cpu, 22)
        self.assertEqual(args.timeout, 300)
        self.assertEqual(args.warm_timeout, 600)
        self.assertEqual(args.max_pair_retries, rcf.SPEC.max_pair_retries)
        self.assertEqual(rcf.SPEC.max_pair_retries, 32)

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
        budget_kinds = {}
        for pair in rcf.SPEC.pairs:
            has_budget = "tactic_budget_ms" in pair.metadata
            has_kind = "budget_kind" in pair.metadata
            self.assertEqual(
                has_budget,
                not pair.null_control and pair.name.endswith("-tactic"),
                pair.name,
            )
            self.assertEqual(has_kind, has_budget, pair.name)
            if has_budget:
                budgets[pair.name] = pair.metadata["tactic_budget_ms"]
                budget_kinds[pair.name] = pair.metadata["budget_kind"]
        self.assertEqual(
            budgets,
            {
                "quadratic-tactic": 2_000,
                "degree10-tactic": 12_000,
                "degree50-tactic": 30_000,
            },
        )
        self.assertEqual(
            budget_kinds,
            {
                "quadratic-tactic": "regression-bound",
                "degree10-tactic": "regression-bound",
                "degree50-tactic": "adversarial-ceiling",
            },
        )

    def test_spec_budgets_match_manifest(self) -> None:
        source = (sweep.ROOT / "SPEC/Libraries/hex-rcf.md").read_text(
            encoding="utf-8"
        )
        labels = {
            "quadratic-tactic": "Quadratic goals, one atom",
            "degree10-tactic": "Degree ≤ 10, up to 3 atoms",
            "degree50-tactic": "Adversarial degree-50, one atom",
        }
        pairs = {pair.name: pair for pair in rcf.SPEC.pairs}
        for name, label in labels.items():
            match = re.search(
                rf"^- {re.escape(label)}: under ([0-9]+) seconds\.$",
                source,
                re.MULTILINE,
            )
            self.assertIsNotNone(match, name)
            assert match is not None
            self.assertEqual(
                int(match.group(1)) * 1_000,
                pairs[name].metadata["tactic_budget_ms"],
                name,
            )

    def test_axiom_reports_match_probe_roles(self) -> None:
        for pair in rcf.SPEC.pairs:
            if pair.null_control:
                self.assertEqual(pair.reference, pair.candidate, pair.name)
                expected = (
                    None
                    if pair.name == "fresh-build-null"
                    else rcf.ALLOWED_AXIOMS
                )
                self.assertEqual(
                    pair.reference.expected_axioms, expected, pair.name
                )
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
        lakefile = (sweep.ROOT / "lakefile.lean").read_text(encoding="utf-8")

        def target_modules(target: str) -> set[str]:
            header = re.search(
                rf"^lean_lib {re.escape(target)} where$", lakefile, re.MULTILINE
            )
            self.assertIsNotNone(header, target)
            assert header is not None
            tail = lakefile[header.end():]
            end = re.search(r"\n(?=\S)", tail)
            body = tail if end is None else tail[:end.start()]
            return set(re.findall(r"`([A-Za-z0-9_.]+)", body))

        reduced = target_modules("HexRCFProofProbe")
        scientific = target_modules("HexRCFProofProbeScientific")
        for module in sweep.probe_modules(rcf.SPEC):
            is_scientific = (
                ".Degree10." in module
                or ".Degree50." in module
                or module.endswith(".DoubleDegree50")
            )
            expected = scientific if is_scientific else reduced
            unexpected = reduced if is_scientific else scientific
            self.assertIn(module, expected, module)
            self.assertNotIn(module, unexpected, module)

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
