# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from scripts.bench import graphiso_sweep


class SweepTest(unittest.TestCase):
    def test_timeout_kills_descendants(self):
        program = (
            "import subprocess, sys, time; "
            "p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
            "print(p.pid, flush=True); time.sleep(60)"
        )
        with self.assertRaises(subprocess.TimeoutExpired) as caught:
            graphiso_sweep.run_group([sys.executable, "-c", program], timeout=0.5)
        pid = int(caught.exception.stdout.strip())
        stat = Path(f"/proc/{pid}/stat")
        try:
            self.assertEqual(stat.read_text().split()[2], "Z")
        except (FileNotFoundError, ProcessLookupError):
            with self.assertRaises(ProcessLookupError):
                os.kill(pid, 0)

    def sweep(self, result, status):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = dict(name="g", family="f", n=4, lit_ns=20, fast_ns=30, nodes=2)
            (root / "old.jsonl").write_text(json.dumps(original) + "\n")
            (root / "index.jsonl").write_text(json.dumps(
                dict(name="g", family="f", n=4, path="unused")) + "\n")
            argv = ["graphiso_sweep", "--corpus", str(root), "--isograph", "unused",
                    "--out", str(root / "new.jsonl"), "--merge-into", str(root / "old.jsonl"),
                    "--only", "hex-sparse-canon:f", "--passes", "1", "--no-pin"]
            with patch("sys.argv", argv), patch.object(graphiso_sweep, "_run", return_value=(result, status)), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(graphiso_sweep.main(), 0)
            merged = json.loads((root / "new.jsonl").read_text())
            raw = [json.loads(line) for line in (root / "new.runs.jsonl").read_text().splitlines()]
            self.assertEqual(json.loads((root / "old.jsonl").read_text()), original)
            for key, value in original.items():
                self.assertEqual(merged[key], value)
            return merged, raw

    def test_legacy_search_column_survives_merge(self):
        merged, raw = self.sweep(dict(hex_sparse_ns=10, hex_sparse_nodes=2), "ok")
        self.assertEqual(merged["search_ns"], 20)
        self.assertEqual(merged["search_column"], "lit_ns")
        self.assertEqual(merged["hex_sparse_ns"], 10)
        self.assertEqual(raw[1]["result"]["hex_sparse_ns"], 10)

    def test_over_budget_measurement_is_retained(self):
        merged, raw = self.sweep(dict(hex_sparse_ns=9_000_000_000, hex_sparse_nodes=2,
                                      samples_ns=[9_000_000_000]), "over budget")
        self.assertIsNone(merged["hex_sparse_ns"])
        self.assertEqual(raw[1]["status"], "over budget")
        self.assertEqual(raw[1]["result"]["samples_ns"], [9_000_000_000])


if __name__ == "__main__":
    unittest.main()
