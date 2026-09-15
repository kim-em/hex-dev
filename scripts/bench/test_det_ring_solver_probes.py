#!/usr/bin/env python3
"""Coverage, source synchronization, and parsing for the ring-solver probes."""
import contextlib
import io
import unittest
from unittest.mock import patch

from scripts.bench import det_ring_solver_probes as probes
from scripts.bench import det_ring_solver_sweep as runner
from scripts.bench import fresh_module_sweep as sweep


class RingSolverProbesTest(unittest.TestCase):
    def test_committed_sources_match_generator(self):
        sources = probes.probe_sources()
        self.assertEqual(len(sources), 20)
        for name, source in sources.items():
            self.assertEqual((probes.DEST / name).read_text(), source, name)
            self.assertIn("#print axioms result", source)
        self.assertIn("fail_if_success (solve | ring)", sources["RingSolverAlgebraic.lean"])
        self.assertIn("fail_if_success grobner\n  ring", sources["RingSolverVariableExponent.lean"])

    def test_protocol_and_capability_provenance(self):
        self.assertEqual(set(probes.RING_AXIOMS), {stem for stem, _, _ in probes.CASES})
        sweep.validate_spec(runner.SPEC)
        self.assertEqual(runner.SPEC.required_samples, 6)
        self.assertTrue(runner.SPEC.retain_compiler_output)
        self.assertEqual({(p.metadata["family"], p.metadata["dimension"])
                          for p in runner.SPEC.pairs},
                         {(family, n) for family in ("integer", "rational", "power")
                          for n in (1, 2, 3)})
        hashes = sweep.source_hashes(runner.SPEC, runner.Path(runner.__file__))
        for module in runner.CAPABILITIES:
            self.assertIn("bench/" + module.module.replace(".", "/") + ".lean", hashes)

    def test_cumulative_profile_units(self):
        for unit, expected in (("s", 2000), ("ms", 2), ("us", .002),
                               ("μs", .002), ("ns", .000002)):
            output = f"type checking 99s\ncumulative profiling times:\n\ttype checking 2{unit}\n"
            self.assertAlmostEqual(runner.profile_milliseconds(output, "type checking"), expected)
        with self.assertRaises(ValueError):
            runner.profile_milliseconds("type checking 2ms", "type checking")
        with self.assertRaises(ValueError):
            runner.profile_milliseconds("cumulative profiling times:\n", "elaboration")

    def test_argument_forwarding_does_not_mutate_argv(self):
        with patch.object(runner, "run_cli", return_value=0) as run:
            self.assertEqual(runner.main(["--shared-host", "--cpu=4", "--samples", "6"]), 0)
            self.assertEqual(run.call_args.args[2], ["--shared-host", "--cpu", "4", "--samples", "6"])

    def test_recorded_table_matches_report(self):
        path = probes.ROOT / "reports/bench-results/hex-poly-det-ring-solver-cd82ae658bde-chungus2.json.gz"
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            runner.print_table(path)
        report = (probes.ROOT / "reports/hex-poly-det-mathlib-performance.md").read_text()
        self.assertIn(output.getvalue().strip(), report)


if __name__ == "__main__":
    unittest.main()
