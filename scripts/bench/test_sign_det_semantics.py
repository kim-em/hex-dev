"""Regression tests for semantic measurement output and failure retention."""
from contextlib import chdir
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.bench import sign_det_semantics as runner


class OutputTests(unittest.TestCase):
    def run_mocked(self, argv, action):
        with patch.object(runner.sys, "argv", ["runner", *argv]), \
             patch.object(runner, "acquire_cpu", return_value=(0, open("/dev/null"))), \
             patch.object(runner, "environment", return_value={}), \
             patch.object(runner, "source_hashes", return_value={}), \
             patch.object(runner, "run_cli", side_effect=action) as run:
            return runner.main(), run

    def test_in_repo_output_rejected_before_creating_sidecar(self):
        path = runner.ROOT / "semantic-probe-test-output.json"
        with self.assertRaisesRegex(RuntimeError, "outside the repository"):
            self.run_mocked(["--output", str(path)], AssertionError("must not measure"))
        self.assertFalse(Path(str(path) + ".samples.jsonl").exists())

    def test_default_output_is_external_and_marks_completion(self):
        with tempfile.TemporaryDirectory() as tmp, \
             patch.object(runner.Path, "home", return_value=Path(tmp)), \
             patch.object(runner, "default_output", return_value=Path("reports/default.json")):
            code, run = self.run_mocked([], lambda *a, **k: 0)
            output = Path(tmp) / ".local/state/hex/proof-probes/default.json"
            self.assertEqual(code, 0)
            self.assertIn(str(output), run.call_args.args[2])
            records = [json.loads(line) for line in Path(str(output) + ".samples.jsonl").read_text().splitlines()]
            self.assertEqual(records[-1], {"type": "complete", "code": 0})

    def test_failed_arm_and_exception_retained_at_chosen_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "failed.json"

            def fail(*args, **kwargs):
                kwargs["sample_observer"]("probe", {"state": "failed", "returncode": 1})
                raise RuntimeError("injected measurement failure")

            with self.assertRaisesRegex(RuntimeError, "injected measurement failure"):
                self.run_mocked(["--output", str(output)], fail)
            records = [json.loads(line) for line in Path(str(output) + ".samples.jsonl").read_text().splitlines()]
            self.assertEqual(records[-2]["state"], "failed")
            self.assertEqual(records[-1]["type"], "failure")
            self.assertEqual(records[-1]["error"], "injected measurement failure")

    def test_relative_output_resolves_from_current_directory(self):
        with tempfile.TemporaryDirectory() as tmp, chdir(tmp):
            code, run = self.run_mocked(["--output", "relative.json"], lambda *a, **k: 0)
            output = Path(tmp) / "relative.json"
            self.assertEqual(code, 0)
            self.assertIn(str(output), run.call_args.args[2])
            self.assertTrue(Path(str(output) + ".samples.jsonl").exists())


if __name__ == "__main__":
    unittest.main()
