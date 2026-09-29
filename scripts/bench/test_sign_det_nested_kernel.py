"""Check retention and output paths for the nested-field sweep."""
from pathlib import Path
import unittest

from scripts.bench import sign_det_nested_kernel as runner
from scripts.bench.fresh_module_sweep import validate_spec
from scripts.bench import test_sign_det_semantics as retention


class NestedOutputTests(retention.OutputTests):
    runner = runner


class ProbeInventoryTests(unittest.TestCase):
    def test_spec_and_metadata(self):
        validate_spec(runner.SPEC)
        self.assertEqual(len(runner.PAIRS), 20)
        keys = set(runner.PAIRS[0].metadata)
        self.assertTrue(all(set(p.metadata) == keys for p in runner.PAIRS))
        self.assertIn(runner.ROOT / "scripts/bench/test_sign_det_nested_kernel.py",
                      [runner.ROOT / p for p in runner.SPEC.extra_sources])

    def test_every_proof_module_is_registered(self):
        source = runner.ROOT / "bench/HexSignDetMathlib"
        files = [*source.glob("ProofProbe/Nested/N*/*.lean"),
                 *source.glob("NestedProofProbe/N3/*.lean")]
        proofs = {"HexSignDetMathlib." + ".".join(p.relative_to(source).with_suffix("").parts)
                  for p in files if not p.stem.endswith("Baseline")}
        self.assertEqual({p.candidate.module for p in runner.PAIRS}, proofs)

    def test_fraction_imports_match_baselines(self):
        for p in runner.PAIRS:
            def imports(module):
                path = runner.ROOT / "bench" / Path(*module.split(".")).with_suffix(".lean")
                return [line for line in path.read_text().splitlines()
                        if line.startswith(("public import ", "public meta import "))]
            self.assertEqual(imports(p.reference.module), imports(p.candidate.module), p.name)


if __name__ == "__main__":
    unittest.main()
