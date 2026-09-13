#!/usr/bin/env python3
"""Coverage and evidence parsing for the structural tactic sweep."""
import json
from pathlib import Path
import unittest

from scripts.bench import fresh_module_sweep as sweep
from scripts.bench import structural_tactic_probes as probes
from scripts.bench import structural_tactic_sweep as runner


class StructuralProbesTest(unittest.TestCase):
    def test_committed_manifest_matches_generator(self):
        expected = [{k: v for k, v in row.items() if k != "proposition"}
                    for row in probes.fixture_cases()]
        self.assertEqual(json.loads(runner.MANIFEST.read_text()), expected)
        self.assertEqual(len({row["module"] for row in expected}), len(expected))
        self.assertEqual(len(expected), 193)

    def test_complete_named_ladders(self):
        cases = probes.fixture_cases()
        families = {
            "HexMinPolyMathlib": {
                name: (8, 32) for name in ("cyclic", "repeated-block", "nilpotent", "rational-dense")},
            "HexSmithMathlib": {
                "chain-conjugate": (8, 32), "rectangular-presentation": (8, 32),
                "rank-deficient": (8, 32), "large-coefficients": (8, 32, 64, 256)},
            "HexHermiteMathlib": {
                name: (8, 32, 128) for name in ("unimodular-conjugate", "tall-hermite",
                                               "rank-deficient-hermite", "membership-residual")}}
        for owner, groups in families.items():
            for family, heights in groups.items():
                actual = {(row["n"], row["configured_input_bits"]) for row in cases
                          if row["owner"] == owner and row["family"] == family}
                self.assertEqual(actual, {(n, bits) for n in (2, 4, 8, 16) for bits in heights})
        rectangular = [row for row in cases if row["family"] == "rectangular-presentation"]
        self.assertEqual(len(rectangular), 16)
        self.assertTrue(all(row["rows"] == 2 * row["columns"] or
                            row["columns"] == 2 * row["rows"] for row in rectangular))
        residual = [row for row in cases if row["family"] == "membership-residual"]
        self.assertEqual({row["component"] for row in residual}, {"basis", "member", "nonmember"})
        self.assertEqual(len(residual), 36)
        self.assertTrue(all(row["actual_input_numerator_bits"] <= row["configured_input_bits"]
                            for row in cases))

    def test_absolute_protocol_and_sources(self):
        spec = runner.specification()
        sweep.validate_spec(spec)
        self.assertEqual(spec.required_samples, 6)
        self.assertTrue(spec.absolute_only)
        for pair in spec.pairs:
            self.assertEqual(pair.metadata["fresh_module_budget_ms"], 60000)
            self.assertEqual(pair.metadata["comparator_status"],
                             "no-comparable-surface-in-named-comparator")
            source = probes.ROOT / "bench" / Path(*pair.candidate.module.split(".")).with_suffix(".lean")
            self.assertIn("#print axioms result", source.read_text())

    def test_profiles_and_certificate_counts(self):
        output = 'info: fixture.lean:1:1: [HexMatrix.certificate] {"integer_entries":7}\n'
        output += '\ttype checking 79.9ms\n\ttype checking 2.3s\n'
        parsed = runner.compiler_metrics(output)
        self.assertAlmostEqual(parsed["kernel_seconds"], 2.3799)
        self.assertEqual(parsed["certificates"], [{"integer_entries": 7}])


if __name__ == "__main__":
    unittest.main()
