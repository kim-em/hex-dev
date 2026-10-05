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

    def test_archived_points_and_summary_tampering(self):
        from scripts.bench.sign_det_matrix_archive import validate
        import shutil, hashlib
        directory = bench.ROOT/"reports/data/sign-det-matrix-wide/6b977999bc-first"
        self.assertEqual(len(validate(directory, reconstruct=True)), 2)
        target = Path(self.temporary.name)/"archive"
        shutil.copytree(directory, target)
        path = target/"derived-rerun-summary.json"
        value = json.loads(path.read_text()); value["rows"][-1]["median_seconds"] += 1
        path.write_text(json.dumps(value))
        manifest = json.loads((target/"archive.json").read_text())
        manifest["files_sha256"]["derived-rerun-summary.json"] = hashlib.sha256(path.read_bytes()).hexdigest()
        (target/"archive.json").write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "summary disagrees with raw points"):
            validate(target)


@unittest.skipUnless(sys.platform.startswith("linux"), "Linux process-group cleanup")
class InterruptedProfiles(unittest.TestCase):
    def assert_stopped(self, pid):
        try:
            fd = os.pidfd_open(pid)
        except ProcessLookupError:
            return
        try:
            waiter = select.poll()
            waiter.register(fd, select.POLLIN)
            self.assertTrue(waiter.poll(5000), "descendant survived cleanup")
        finally:
            os.close(fd)

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
        child_fds = []
        try:
            self.assertTrue(select.select([process.stdout], [], [], 5)[0], "child did not start")
            children = list(map(int, process.stdout.readline().split()))
            self.assertEqual(len(children), 2)
            for pid in children:
                try:
                    child_fds.append(os.pidfd_open(pid))
                except ProcessLookupError:
                    pass
            process.send_signal(signal.SIGTERM)
            process.communicate(timeout=5)
            self.assertEqual(process.returncode, 128 + signal.SIGTERM)
            for pid in children:
                self.assert_stopped(pid)
        finally:
            if process.poll() is None:
                process.kill()
            process.communicate()
            for fd in child_fds:
                try:
                    signal.pidfd_send_signal(fd, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                finally:
                    os.close(fd)

    def test_exited_runner_stops_its_descendant(self):
        child = ("import subprocess, sys; "
                 "p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
                 "print(p.pid, flush=True); sys.exit(7)")
        with tempfile.TemporaryFile(mode="w+") as stdout, tempfile.TemporaryFile(mode="w+") as stderr:
            self.assertEqual(bench.run_owned([sys.executable, "-c", child], stdout, stderr), 7)
            stdout.seek(0)
            pid = int(stdout.read().strip())
            self.assert_stopped(pid)

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


class MatrixAttribution(unittest.TestCase):
    def setUp(self):
        from scripts.bench.sign_det_matrix_attribution import validate
        self.validate = validate
        root = Path(__file__).resolve().parents[2]/"reports/data"
        self.source = root/"sign-det-matrix-attribution/6b977999bc"
        self.matrix = root/"sign-det-matrix-wide/6b977999bc-first"

    def test_complete_operation_windows(self):
        rows = self.validate(self.source)
        self.assertEqual((rows["243"]["samples"], rows["243"]["dense_loop"]), (119, 66))
        self.assertEqual((rows["729"]["samples"], rows["729"]["dense_loop"]), (2711, 1960))

    def test_corrupted_profile_bytes(self):
        import shutil
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary)/"archive"; shutil.copytree(self.source, target)
            path = target/"729/perf.data.gz"; path.write_bytes(path.read_bytes()+b"changed")
            with self.assertRaisesRegex(ValueError, "stored bytes changed"):
                self.validate(target, matrix_directory=self.matrix)

    def test_rehashed_summary_is_not_the_evidence(self):
        import shutil, hashlib
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary)/"archive"; shutil.copytree(self.source, target)
            path = target/"summary.json"; summary = json.loads(path.read_text())
            summary["729"]["dense_loop"] += 1; path.write_text(json.dumps(summary))
            manifest = json.loads((target/"archive.json").read_text())
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            manifest["files"]["summary.json"].update(sha256=digest, stored_sha256=digest)
            (target/"archive.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "summary disagrees"):
                self.validate(target, matrix_directory=self.matrix)

    def test_rehashed_window_thread_and_source_mismatches(self):
        import shutil, hashlib, gzip
        def replace(target, name, value):
            manifest = json.loads((target/"archive.json").read_text())
            binding = manifest["files"][name]
            data = value.encode()
            payload = gzip.compress(data, mtime=0) if binding["stored"].endswith(".gz") else data
            (target/binding["stored"]).write_bytes(payload)
            binding.update(sha256=hashlib.sha256(data).hexdigest(),
                           stored_sha256=hashlib.sha256(payload).hexdigest())
            (target/"archive.json").write_text(json.dumps(manifest))
        for case in ("window", "thread", "source"):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as temporary:
                target = Path(temporary)/"archive"; shutil.copytree(self.source, target)
                manifest = json.loads((target/"archive.json").read_text())
                if case == "source":
                    metadata = json.loads((target/"metadata.json").read_text())
                    key = next(iter(metadata["source_sha256"]))
                    metadata["source_sha256"][key] = "0"*64
                    replace(target, "metadata.json", json.dumps(metadata))
                elif case == "window":
                    name = next(name for name in manifest["files"] if name.startswith("729/regions-"))
                    rows = list(map(json.loads, gzip.decompress((target/manifest["files"][name]["stored"]).read_bytes()).decode().splitlines()))
                    rows[1]["mono_t1_ns"] += 1
                    replace(target, name, "\n".join(map(json.dumps, rows)))
                else:
                    name = "729/perf-leaves.txt"
                    text = gzip.decompress((target/manifest["files"][name]["stored"]).read_bytes()).decode()
                    metadata = json.loads((target/"metadata.json").read_text())
                    region = metadata["captures"][1]["region"]
                    from scripts.bench.sign_det_matrix_attribution import HEADER
                    lines = text.splitlines()
                    for index, line in enumerate(lines):
                        match = HEADER.fullmatch(line)
                        stamp = int(match[3])*10**9+int(match[4])
                        if region["mono_t0_ns"] <= stamp <= region["mono_t1_ns"]:
                            lines[index] = line.replace(match[1]+"/"+match[2], match[1]+"/"+str(int(match[2])+1), 1)
                            break
                    replace(target, name, "\n".join(lines)+"\n")
                with self.assertRaises(ValueError):
                    self.validate(target, matrix_directory=self.matrix)

    def test_unlisted_profile_artifact(self):
        import shutil
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary)/"archive"; shutil.copytree(self.source, target)
            (target/"extra").write_text("unlisted")
            with self.assertRaisesRegex(ValueError, "unlisted"):
                self.validate(target, matrix_directory=self.matrix)

    def test_retained_power_comparison_and_false_ratio(self):
        from scripts.bench.sign_det_matrix_attribution import validate_comparison
        import shutil, hashlib
        source = Path(__file__).resolve().parents[2]/"reports/data/sign-det-matrix-power/7d21b4083f"
        ratios = validate_comparison(source)
        controlled = source.parent/"cold-246bc73c38"
        self.assertGreater(validate_comparison(controlled)["243"]["median_before_after_ratio"], 1)
        self.assertGreater(ratios["243"]["median_before_after_ratio"], 1)
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary)/"archive"; shutil.copytree(controlled, target)
            path = target/"metadata.json"; meta = json.loads(path.read_text())
            meta["summary"]["243"]["median_before_after_ratio"] = 100
            path.write_text(json.dumps(meta))
            manifest = json.loads((target/"archive.json").read_text())
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            manifest["files"]["metadata.json"].update(sha256=digest, stored_sha256=digest)
            (target/"archive.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "ratios disagree"):
                validate_comparison(target)
