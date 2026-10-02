#!/usr/bin/env python3
"""Regression tests for tactic process ownership and timeout cleanup."""
# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison

import importlib.util
import os
from pathlib import Path
import signal
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "hexgraphiso_cactus", Path(__file__).with_name("hexgraphiso-cactus.py"))
assert SPEC and SPEC.loader
cactus = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cactus)


class TacticProcessTests(unittest.TestCase):
    def test_inherited_environment_and_output(self):
        result = cactus._run_tactic(
            [sys.executable, "-c", "import os; print(os.environ.get('LEAN_NUM_THREADS'))"], 5)
        self.assertIsNotNone(result)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout.strip(), str(os.environ.get("LEAN_NUM_THREADS")))

    def test_failure_status(self):
        result = cactus._run_tactic([sys.executable, "-c", "raise SystemExit(7)"], 5)
        self.assertIsNotNone(result)
        self.assertEqual(result.returncode, 7)

    @unittest.skipUnless(sys.platform == "linux", "uses /proc to check descendant exit")
    def test_timeout_kills_descendant(self):
        with tempfile.TemporaryDirectory() as tmp:
            pidfile = Path(tmp) / "child.pid"
            code = """import os, pathlib, sys, time
pid = os.fork()
if pid == 0:
    pathlib.Path(sys.argv[1]).write_text(str(os.getpid()))
time.sleep(60)
"""
            try:
                result = cactus._run_tactic([sys.executable, "-c", code, str(pidfile)], 1)
                self.assertIsNone(result)
                self.assertTrue(pidfile.exists(), "test child did not start")
                child = int(pidfile.read_text())
                status = Path(f"/proc/{child}/stat")
                try:
                    state = status.read_text().rsplit(") ", 1)[1].split()[0]
                except (FileNotFoundError, ProcessLookupError):
                    pass
                else:
                    self.assertEqual(state, "Z")
            finally:
                if pidfile.exists():
                    try:
                        os.kill(int(pidfile.read_text()), signal.SIGKILL)
                    except ProcessLookupError:
                        pass


if __name__ == "__main__":
    unittest.main()
