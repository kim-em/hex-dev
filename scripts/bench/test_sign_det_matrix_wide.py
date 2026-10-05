"""Protect full-support checker subjects, fixed schedules and raw declarations."""
import copy
import json
import os
import select
import signal
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest
from scripts.bench import sign_det_matrix_wide as bench


class WideMatrix(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.path = Path(self.temporary.name) / "records.json"
        self.rows = [{"queries": s, "matrixSize": 3**s, "supportSize": 3**s,
                      "countSum": 3**s, "inverseIdentityScalarPairs": 27**s,
                      "inverseBits": s+1, "denominatorBits": s+1,
                      "valuesBits": (3**s).bit_length(), "literalOrders": True,
                      "finiteMoments": True, "inputHash": 1, "checkResultHash": 2}
                     for s in bench.ARITIES]

    def inputs(self, rows):
        self.path.write_text("\n".join(map(json.dumps, rows)))
        return bench.validate_inputs(self.path)

    def test_subject_and_complete_schedule(self):
        self.inputs(self.rows)
        for key, value in (("queries", 5.0), ("countSum", 1), ("inverseBits", True),
                           ("denominatorBits", 1), ("finiteMoments", False), ("literalOrders", False),
                           ("checkResultHash", -1)):
            changed = copy.deepcopy(self.rows)
            changed[0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.inputs(changed)
        changed = copy.deepcopy(self.rows); changed[0]["checkResultHash"] = 3
        with self.assertRaises(ValueError):
            self.inputs(changed)
        with self.assertRaises(ValueError):
            self.inputs(self.rows[:-1])
        with self.assertRaises(ValueError):
            self.inputs(list(reversed(self.rows)))

    def test_unchanged_declaration_and_exact_observations(self):
        expected = self.inputs(self.rows)
        result = {"function": bench.FUNCTION, "kind": "parametric", "hashable": True,
                  "budget_truncated": False, "complexity_formula": "r^3", "config": bench.CONFIG,
                  "env": {"git_commit": "source", "git_dirty": False}, "verdict": "inconclusive",
                  "slope": 1, "advisories": [], "points": [
                      {"trial_index": trial, "param": r, "status": "ok", "result_hash": "0x2",
                       "part_of_verdict": True, "below_signal_floor": False,
                       "per_call_nanos": r**3, "inner_repeats": 1, "peak_rss_kb": 100, "alloc_bytes": None}
                      for trial in range(6) for r in bench.PARAMS]}
        def check(value):
            self.path.write_text(json.dumps({"export_schema_version": 1, "results": [value]}))
            return bench.validate_result(self.path, expected, "source")
        self.assertEqual(check(result)["verdict"], "inconclusive")
        for key, value in (("complexity_formula", "r^2"), ("budget_truncated", True),
                           ("function", "oldChecker")):
            changed = copy.deepcopy(result); changed[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check(changed)
        for key, value in (("status", "killed_at_cap"), ("per_call_nanos", float("nan")),
                           ("result_hash", "0x0"), ("part_of_verdict", False),
                           ("alloc_bytes", 12)):
            changed = copy.deepcopy(result); changed["points"][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check(changed)
        changed = copy.deepcopy(result); changed["points"].pop()
        with self.assertRaises(ValueError):
            check(changed)

        for key, value in (("git_commit", "foreign"), ("git_dirty", True)):
            changed = copy.deepcopy(result); changed["env"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check(changed)
        for key, value in (("max_seconds_per_call", 180), ("outer_trials", 5)):
            changed = copy.deepcopy(result); changed["config"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check(changed)
        changed = copy.deepcopy(result)
        changed["points"][0], changed["points"][1] = changed["points"][1], changed["points"][0]
        with self.assertRaises(ValueError):
            check(changed)

    def test_retained_overlap_is_complete(self):
        expected = [f"tensor matrix {3**s}: complete witness matches ordinary solve" for s in range(7)]
        self.path.write_text("\n".join(expected)+"\n")
        bench.validate_overlap(self.path)
        for changed in (expected[:-1], list(reversed(expected)), expected + ["extra"]):
            self.path.write_text("\n".join(changed)+"\n")
            with self.assertRaises(ValueError):
                bench.validate_overlap(self.path)

    def test_retained_outcomes(self):
        for verdict, code in (("consistent_with_declared_complexity", 0), ("inconclusive", 1)):
            self.assertEqual(bench.outcome(verdict),
                             {"state": "complete", "collector_exit_code": code})
            changed = bench.outcome(verdict, identity_error=RuntimeError("changed binary"))
            self.assertEqual((changed["state"], changed["collector_exit_code"]), ("failed", 2))
            self.assertEqual(changed["error"], "changed binary")
        self.assertEqual(bench.outcome(error=ValueError("bad observation"))["collector_exit_code"], 2)
        interrupted = bench.outcome(error=KeyboardInterrupt())
        self.assertEqual((interrupted["state"], interrupted["collector_exit_code"]), ("interrupted", 130))
        self.assertTrue(interrupted["error"])
        self.assertEqual(bench.outcome(error=KeyboardInterrupt(), identity_error=RuntimeError("changed")),
                         interrupted)
        failed = bench.outcome(error=ValueError("original"), identity_error=RuntimeError("changed"))
        self.assertEqual(failed["error"], "original")
        terminated = bench.outcome(error=SystemExit(143))
        self.assertEqual((terminated["state"], terminated["collector_exit_code"]), ("interrupted", 143))
        with self.assertRaises(ValueError):
            bench.outcome("unknown")


@unittest.skipUnless(sys.platform.startswith("linux"), "Linux process-group cleanup")
class InterruptedProfiles(unittest.TestCase):
    def test_termination_stops_child_and_descendant(self):
        child = ("import os, subprocess, sys, time; "
                 "p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
                 "print(os.getpid(), p.pid, flush=True); time.sleep(60)")
        program = ("import signal, sys; "
                   "from scripts.bench.sign_det_matrix_wide import run_owned, stop_signal; "
                   "signal.signal(signal.SIGTERM, stop_signal); "
                   f"run_owned([sys.executable, '-c', {child!r}], sys.stdout, sys.stderr)")
        process = subprocess.Popen([sys.executable, "-c", program], cwd=bench.ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        children = []
        try:
            self.assertTrue(select.select([process.stdout], [], [], 5)[0], "child did not start")
            children = list(map(int, process.stdout.readline().split()))
            self.assertEqual(len(children), 2)
            process.send_signal(signal.SIGTERM)
            process.communicate(timeout=5)
            self.assertEqual(process.returncode, 128 + signal.SIGTERM)
            for pid in children:
                status = Path(f"/proc/{pid}/status")
                if status.exists():
                    state = next(line for line in status.read_text().splitlines()
                                 if line.startswith("State:"))
                    self.assertIn("Z", state, "profile process survived termination")
        finally:
            if process.poll() is None:
                process.kill()
            process.communicate()
            if children:
                try:
                    os.killpg(children[0], signal.SIGKILL)
                except ProcessLookupError:
                    pass

    def test_exited_runner_stops_its_descendant(self):
        child = ("import subprocess, sys; "
                 "p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
                 "print(p.pid, flush=True); sys.exit(7)")
        with tempfile.TemporaryFile(mode="w+") as stdout, tempfile.TemporaryFile(mode="w+") as stderr:
            self.assertEqual(bench.run_owned([sys.executable, "-c", child], stdout, stderr), 7)
            stdout.seek(0)
            pid = int(stdout.read().strip())
            status = Path(f"/proc/{pid}/status")
            if status.exists():
                state = next(line for line in status.read_text().splitlines() if line.startswith("State:"))
                self.assertIn("Z", state, "descendant survived its failed runner")

    def test_inherited_ignored_signal_is_preserved(self):
        previous = signal.signal(signal.SIGHUP, signal.SIG_IGN)
        installed = {}
        try:
            installed = bench.install_signals()
            self.assertNotIn(signal.SIGHUP, installed)
            if signal.SIGTERM in installed:
                self.assertIs(signal.getsignal(signal.SIGTERM), bench.stop_signal)
            self.assertEqual(signal.getsignal(signal.SIGHUP), signal.SIG_IGN)
        finally:
            for number, handler in installed.items():
                signal.signal(number, handler)
            signal.signal(signal.SIGHUP, previous)
