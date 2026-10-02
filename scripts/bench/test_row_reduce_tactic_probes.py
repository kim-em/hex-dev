#!/usr/bin/env python3
"""Check the required grids, matched systems, and fresh-proof evidence protocol."""
import json
from pathlib import Path
import unittest

from scripts.bench import fresh_module_sweep as sweep
from scripts.bench import row_reduce_tactic_probes as probes
from scripts.bench import row_reduce_tactic_sweep as runner


class RowReduceProbesTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = probes.fixtures()

    def test_committed_manifest_and_sources(self):
        expected = [{k: v for k, v in row.items() if k not in ("proposition", "term")}
                    for row in self.cases]
        self.assertEqual(json.loads(runner.MANIFEST.read_text()), expected)
        self.assertEqual(len({row["module"] for row in expected}), 200)
        for case in self.cases:
            path = probes.ROOT / "bench" / Path(*case["module"].split(".")).with_suffix(".lean")
            self.assertEqual(path.read_text(), probes.source(case), case["module"])

    def test_complete_named_ladders(self):
        families = {
            **{name: (8, 32) for name in ("dense-invertible", "pivot-swaps", "singular-kernel")},
            "rational-height": (8, 32, 64, 256),
            **{name: (8, 32, 128) for name in ("square-unique", "tall-consistent", "wide-affine",
                                              "deficient-affine", "inconsistent-separator")}}
        for family, heights in families.items():
            actual = {(row["n"], row["configured_input_bits"]) for row in self.cases
                      if row["family"] == family}
            self.assertEqual(actual, {(n, bits) for n in probes.DIMENSIONS for bits in heights})
        for row in self.cases:
            self.assertLessEqual(row["actual_input_numerator_bits"], row["configured_input_bits"])
            self.assertLessEqual(row["actual_input_denominator_bits"], row["configured_input_bits"])
            if row["family"] == "tall-consistent":
                self.assertEqual(row["rows"], 2 * row["columns"])
            if row["family"] == "wide-affine":
                self.assertEqual(row["columns"], 2 * row["rows"])

    def test_matched_deficient_systems(self):
        # Compare the actual matrix text, not only the family metadata.
        complete = {(row["family"], row["n"], row["configured_input_bits"]): row["term"]
                    for row in self.cases if row["component"] == "complete"}
        for n in probes.DIMENSIONS:
            for bits in (8, 32, 128):
                positive = complete["deficient-affine", n, bits].split("ℚ)")[0]
                negative = complete["inconsistent-separator", n, bits].split("ℚ)")[0]
                self.assertEqual(positive, negative)

    def test_absolute_protocol_and_informational_normalization(self):
        for normalization, count in ((False, 200), (True, 14)):
            spec = runner.specification(normalization)
            sweep.validate_spec(spec)
            self.assertEqual(len(spec.pairs), count)
            self.assertEqual(spec.required_samples, 6)
            self.assertTrue(spec.absolute_only)
            self.assertTrue(spec.retain_compiler_output)
            for pair in spec.pairs:
                self.assertEqual(pair.metadata["fresh_module_budget_ms"], 60000)
                self.assertEqual(pair.candidate.expected_axioms, runner.AXIOMS)
                if normalization:
                    original = next(row for row in self.cases if row["module"] == pair.metadata["compares_to"])
                    path = probes.ROOT / "bench" / Path(*pair.candidate.module.split(".")).with_suffix(".lean")
                    self.assertIn(original["proposition"], path.read_text())


if __name__ == "__main__":
    unittest.main()
