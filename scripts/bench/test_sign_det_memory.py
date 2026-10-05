"""Reject memory captures with mismatched source, operation or measurement mode."""
import json
import gzip
import hashlib
import os
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts.bench.sign_det_memory import child_record, page_peak, validate_retained, install_signals, stop_signal


class MemoryRecords(unittest.TestCase):
    def setUp(self):
        self.row = {"schema_version": 1, "kind": "parametric", "function": "f",
                    "param": 3, "inner_repeats": 1, "cache_mode": "cold",
                    "status": "ok", "error": None, "profile_kernel": True,
                    "env": {"git_commit": "revision", "git_dirty": False},
                    "peak_rss_kb": 100, "result_hash": "0xb"}

    def check(self, row):
        return child_record(json.dumps(row), "f", 3, "revision")

    def test_inherited_ignored_hangup_is_preserved(self):
        original = signal.signal(signal.SIGHUP, signal.SIG_IGN)
        term = signal.signal(signal.SIGTERM, signal.SIG_DFL)
        previous = {}
        try:
            previous = install_signals()
            self.assertEqual(signal.getsignal(signal.SIGHUP), signal.SIG_IGN)
            self.assertNotIn(signal.SIGHUP, previous)
            self.assertEqual(signal.getsignal(signal.SIGTERM), stop_signal)
        finally:
            for number, handler in previous.items():
                signal.signal(number, handler)
            signal.signal(signal.SIGHUP, original)
            signal.signal(signal.SIGTERM, term)

    def test_wrong_subject_and_source(self):
        self.check(self.row)
        for key, value in (("function", "other"), ("param", 7),
                           ("env", {"git_commit": "other", "git_dirty": False}),
                           ("env", {"git_commit": "revision", "git_dirty": True})):
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                self.check(dict(self.row, **{key: value}))

    def test_failed_or_repeated_callback(self):
        for key, value in (("status", "error"), ("error", "failed"),
                           ("inner_repeats", 2), ("cache_mode", "warm"),
                           ("profile_kernel", False), ("result_hash", None)):
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                self.check(dict(self.row, **{key: value}))

    def test_missing_memory_and_duplicate_rows(self):
        for value in (None, 0, -1, True):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.check(dict(self.row, peak_rss_kb=value))
        with self.assertRaises(ValueError):
            child_record(json.dumps(self.row) + "\n" + json.dumps(self.row), "f", 3, "revision")

    def test_page_subject_binding(self):
        text = ("desc: --pages-as-heap=yes\ntime_unit: B\n"
                "cmd: /bench _child --bench f --param 3\n"
                "snapshot=0\ntime=1\nmem_heap_B=100\nmem_heap_extra_B=0\nmem_stacks_B=0\n")
        page_peak(text, "f", 3)
        for function, parameter in (("g", 3), ("f", 7)):
            with self.subTest(function=function, parameter=parameter), self.assertRaises(ValueError):
                page_peak(text, function, parameter)

    def test_page_peak_uses_all_retained_snapshots(self):
        text = "desc: --pages-as-heap=yes\ntime_unit: B\n"
        for i, size in enumerate((100, 500, 200)):
            text += (f"snapshot={i}\ntime={i * 1000}\nmem_heap_B={size}\n"
                     "mem_heap_extra_B=0\nmem_stacks_B=0\nheap_tree=empty\n")
        self.assertEqual(page_peak(text), {"mapped_page_peak_bytes": 500, "snapshots": 3})
        for changed in (text.replace("--pages-as-heap=yes", "--pages-as-heap=no"),
                        text.replace("mem_heap_B=500", "mem_heap_B=-500"),
                        text.replace("mem_heap_extra_B=0", "mem_heap_extra_B=1"),
                        text.replace("mem_stacks_B=0\n", "")):
            with self.subTest(text=changed), self.assertRaises(ValueError):
                page_peak(changed)
        with self.assertRaises(ValueError):
            page_peak("desc: --pages-as-heap=yes\ntime_unit: B\n")


class RetainedMemory(unittest.TestCase):
    def test_all_completed_captures(self):
        root = Path(__file__).resolve().parents[2] / "reports/data/sign-det-process-memory/4c790b883d"
        joint = validate_retained(root / "joint")
        other = validate_retained(root / "other")
        self.assertEqual(len(joint["runs"]), 36)
        self.assertEqual(len(other["runs"]), 126)
        self.assertEqual(set(joint["groups"]) | set(other["groups"]),
                         {"joint", "sparse", "matrix", "height"})
        self.assertEqual(joint["revision"], other["revision"])
        self.assertEqual(joint["binary_sha256"], other["binary_sha256"])


    def test_packaging_preserves_original_metadata(self):
        from scripts.bench.sign_det_memory_archive import package
        source = Path(__file__).resolve().parents[2] / "reports/data/sign-det-process-memory/4c790b883d/joint"
        archive = json.loads((source / "archive.json").read_text())
        with tempfile.TemporaryDirectory() as temporary:
            raw = Path(temporary) / "raw"
            raw.mkdir()
            for name, binding in archive["files"].items():
                data = (source / binding["stored"]).read_bytes()
                (raw / name).write_bytes(gzip.decompress(data) if binding["stored"].endswith(".gz") else data)
            target = Path(temporary) / "archive"
            with self.assertRaisesRegex(ValueError, "outside"):
                package(raw, raw / "archive")
            (raw / "extra").write_text("extra")
            with self.assertRaisesRegex(ValueError, "additional"):
                package(raw, target)
            (raw / "extra").unlink()
            self.assertFalse(target.exists())
            self.assertEqual(len(package(raw, target)["runs"]), 36)
            self.assertEqual((target / "metadata.json").read_bytes(), (raw / "metadata.json").read_bytes())
            with self.assertRaisesRegex(ValueError, "must be new"):
                package(raw, target)

    def test_self_consistent_forged_answers_reject(self):
        source = Path(__file__).resolve().parents[2] / "reports/data/sign-det-process-memory/4c790b883d/joint"
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / "capture"
            shutil.copytree(source, target)
            metadata = json.loads((target / "metadata.json").read_text())
            archive = json.loads((target / "archive.json").read_text())
            def replace(name, data):
                binding = archive["files"][name]
                stored = gzip.compress(data, mtime=0) if binding["stored"].endswith(".gz") else data
                (target / binding["stored"]).write_bytes(stored)
                binding["raw_sha256"] = hashlib.sha256(data).hexdigest()
                binding["stored_sha256"] = hashlib.sha256(stored).hexdigest()
                if name != "metadata.json":
                    metadata["file_sha256"][name] = binding["raw_sha256"]
            function = "Hex.SignDetBench.Joint.runComparison"
            metadata["expected_result_hashes"][function + ":3"] = "0xdeadbeef"
            for record in metadata["runs"]:
                if record["function"] == function and record["parameter"] == 3:
                    record["result_hash"] = "0xdeadbeef"
                    name = record["label"] + ".stdout"
                    data = gzip.decompress((target / archive["files"][name]["stored"]).read_bytes())
                    row = json.loads(data)
                    row["result_hash"] = "0xdeadbeef"
                    replace(name, (json.dumps(row) + "\n").encode())
            replace("metadata.json", (json.dumps(metadata) + "\n").encode())
            (target / "archive.json").write_text(json.dumps(archive))
            with self.assertRaisesRegex(ValueError, "validated input checks"):
                validate_retained(target)


@unittest.skipUnless(sys.platform.startswith("linux"), "Linux process-group cleanup")
class InterruptedProfiles(unittest.TestCase):
    def test_termination_stops_child_and_descendant(self):
        child = ("import os, subprocess, sys, time; "
                 "p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
                 "print(os.getpid(), p.pid, flush=True); time.sleep(60)")
        program = ("import signal, sys; from scripts.bench.sign_det_memory import run_owned, stop_signal; "
                   "signal.signal(signal.SIGTERM, stop_signal); "
                   f"run_owned([sys.executable, '-c', {child!r}], sys.stdout, sys.stderr)")
        root = Path(__file__).resolve().parents[2]
        process = subprocess.Popen([sys.executable, "-c", program], cwd=root,
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
                    state = next(line for line in status.read_text().splitlines() if line.startswith("State:"))
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


class MemorySchedules(unittest.TestCase):
    def test_current_catalog_checked_before_capture(self):
        from scripts.bench.sign_det_memory import require_registered, CURRENT_GROUPS
        from unittest.mock import patch
        names = {"Hex.SignDetBench."+name for _, functions in CURRENT_GROUPS.values() for name in functions}
        catalog = "\n".join("  "+name+" expected complexity: n" for name in names)
        with patch('subprocess.check_output', return_value=catalog):
            require_registered(Path('/bench'), CURRENT_GROUPS)
        for missing in names:
            changed = "\n".join(line for line in catalog.splitlines() if missing not in line)
            with self.subTest(missing=missing), patch('subprocess.check_output', return_value=changed):
                with self.assertRaisesRegex(ValueError, 'unregistered memory callbacks'):
                    require_registered(Path('/bench'), CURRENT_GROUPS)

    def test_current_matrix_answers_and_historical_schedule(self):
        from scripts.bench.sign_det_memory import expected_results, CURRENT_GROUPS, GROUPS, capture_schedule
        root = Path(__file__).resolve().parents[2]
        archive = root/'reports/data/sign-det-process-memory/4c790b883d/other'
        bindings = json.loads((archive/'archive.json').read_text())['files']
        record = bindings['inputs-matrix.stdout']
        stored = (archive/record['stored']).read_bytes()
        raw = gzip.decompress(stored) if record['stored'].endswith('.gz') else stored
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)/'inputs'; path.write_bytes(raw)
            answers = expected_results({'matrix': CURRENT_GROUPS['matrix']}, lambda label, args: path)
        self.assertEqual(answers, {('Hex.SignDetBench.MaximalMatrix.runCheckDimension', n): '0xb'
                                   for n in (9, 27, 81)})
        self.assertEqual(capture_schedule('hex-sign-det-process-memory-v1'), GROUPS)
        self.assertEqual(capture_schedule('hex-sign-det-process-memory-v2'), CURRENT_GROUPS)
        self.assertNotEqual(GROUPS['matrix'], CURRENT_GROUPS['matrix'])
        with self.assertRaisesRegex(ValueError, 'unknown memory collection schema'):
            capture_schedule('unknown')
