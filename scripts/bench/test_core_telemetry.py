#!/usr/bin/env python3

import unittest
import json
import os
import signal
import select
import subprocess
import sys
import time
from pathlib import Path
import tempfile

from scripts.bench import core_telemetry


class CoreTelemetryTest(unittest.TestCase):
    def test_busy_percent(self):
        self.assertEqual(core_telemetry.busy_percent((2, 10), (4, 20)), 20.0)
        self.assertEqual(core_telemetry.busy_percent((2, 10), (2, 10)), 0.0)

    def test_busy_seconds(self):
        self.assertEqual(core_telemetry.busy_seconds((2, 10), (4, 20), 100), 0.02)

    def test_cpu_counters_do_not_double_count_guest(self):
        # user nice system idle iowait irq softirq steal guest guest_nice
        self.assertEqual(
            core_telemetry.cpu_counter([10, 2, 3, 20, 5, 1, 2, 4, 7, 1]),
            (22, 47),
        )

    def test_atomic_task_identity(self):
        fields = ["R", "10", "99"] + ["0"] * 34
        fields[36] = "7"
        task = core_telemetry.parse_task(12, "13 (name with ) parentheses) " + " ".join(fields))
        self.assertEqual(task, dict(tgid=12, tid=13, state="R", pgrp=99,
                                   cpu=7, comm="name with ) parentheses"))

    def test_child_born_during_scan_is_owned(self):
        # No process ancestry snapshot is needed for a newly born child/thread.
        tasks = [dict(tgid=12, tid=13, state="R", pgrp=99, cpu=7, comm="bench"),
                 dict(tgid=20, tid=21, state="R", pgrp=20, cpu=7, comm="bench"),
                 dict(tgid=30, tid=31, state="S", pgrp=30, cpu=7, comm="idle"),
                 dict(tgid=40, tid=41, state="R", pgrp=40, cpu=55, comm="sibling")]
        self.assertEqual(core_telemetry.foreign_tasks(tasks, [7, 55], 99),
                         [tasks[1], tasks[3]])

    def test_group_ownership_and_failure_cleanup(self):
        if not sys.platform.startswith("linux") or len(os.sched_getaffinity(0)) < 2:
            self.skipTest("Linux with at least two eligible CPUs is required")
        cpu = min(os.sched_getaffinity(0))
        # Synthetic ownership test, not performance evidence. The monitor creates
        # its own group in standalone mode and reuses the collector's session
        # group in collector mode. Inject a monitor failure after a grandchild
        # has started and require both processes to be dead after rejection.
        for mode in ("success", "success-leak", "success-leak-thread", "proc-error", "signal", "runner-error"):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "telemetry.json"
                identities = Path(directory) / "identities.json"
                child_code = """
import json, os, subprocess, sys, time
from pathlib import Path
grandchild_code = 'import time; time.sleep(60)'
if sys.argv[2] == 'success-leak-thread':
    grandchild_code = 'import ctypes, threading, time; threading.Thread(target=time.sleep, args=(60,)).start(); ctypes.CDLL(None).pthread_exit(None)'
child = subprocess.Popen([sys.executable, '-c', grandchild_code])
if sys.argv[2] == 'success-leak-thread':
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        stat = Path(f'/proc/{child.pid}/stat').read_text()
        if stat[stat.rfind(')') + 2:].split()[0] == 'Z': break
        time.sleep(0.01)
    else: raise RuntimeError('grandchild leader did not exit')
temporary = Path(sys.argv[1] + ".tmp")
temporary.write_text(json.dumps(dict(pid=os.getpid(), grandchild=child.pid, pgrp=os.getpgrp())))
temporary.replace(sys.argv[1])
if sys.argv[2] == 'runner-error': sys.exit(3)
if sys.argv[2] in ('success-leak', 'success-leak-thread'): sys.exit(0)
if sys.argv[2] == 'success':
    child.terminate(); child.wait(); time.sleep(0.1)
else: time.sleep(60)
"""
                monitor_code = """
import os, signal, sys, time
from pathlib import Path
from scripts.bench import core_telemetry as m
cpu, output, identities, mode, child_code = sys.argv[1:]
m.sibling_set = lambda _: {int(cpu)}
original = m.cpu_counters
calls = 0
def counters():
    global calls
    calls += 1
    if calls > 1 and mode in ('proc-error', 'signal'):
        deadline = time.monotonic() + 5
        while not Path(identities).exists() and time.monotonic() < deadline: time.sleep(0.01)
        if mode == 'signal': os.kill(os.getpid(), signal.SIGTERM)
        raise OSError('injected proc failure')
    return original()
m.cpu_counters = counters
sys.argv = ['core_telemetry.py', '--cpu', cpu, '--output', output, '--interval', '0.05',
            '--', sys.executable, '-c', child_code, identities, mode]
raise SystemExit(m.main())
"""
                for dedicated in (False, True):
                    with self.subTest(dedicated_session=dedicated):
                        identities.unlink(missing_ok=True)
                        result = subprocess.run([sys.executable, "-c", monitor_code,
                            str(cpu), str(output), str(identities), mode, child_code],
                            capture_output=True, text=True, timeout=15,
                            start_new_session=dedicated)
                        record = json.loads(output.read_text())
                        identity = json.loads(identities.read_text())
                        self.assertEqual(record["owned_process_group"], identity["pgrp"])
                        self.assertEqual(record["session_id"], identity["pgrp"])
                        self.assertEqual(record["child_pid"], identity["pid"])
                        self.assertEqual(record["ownership"], "dedicated-process-group")
                        self.assertEqual(result.returncode, {"success": 0, "success-leak": 0, "success-leak-thread": 0,
                            "proc-error": 1, "signal": 128 + signal.SIGTERM, "runner-error": 3}[mode])
                        if mode in ("proc-error", "signal"):
                            self.assertEqual(record["status"], "rejected")
                            self.assertIn("monitor_error", record)
                        if mode != "success":
                            for pid in (identity["pid"], identity["grandchild"]):
                                deadline = time.monotonic() + 2
                                while time.monotonic() < deadline:
                                    descriptor = None
                                    try:
                                        descriptor = os.pidfd_open(pid)
                                        poller = select.poll()
                                        poller.register(descriptor, select.POLLIN)
                                        if poller.poll(0):
                                            break
                                    except (FileNotFoundError, ProcessLookupError):
                                        break
                                    finally:
                                        if descriptor is not None:
                                            os.close(descriptor)
                                    time.sleep(0.01)
                                else:
                                    self.fail(f"owned process {pid} survived monitor failure")

    def test_existing_pipeline_group_is_rejected(self):
        if not sys.platform.startswith("linux") or len(os.sched_getaffinity(0)) < 2:
            self.skipTest("Linux with at least two eligible CPUs is required")
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "telemetry.json"
            child_marker = Path(directory) / "child-started"
            code = """
import sys
from scripts.bench import core_telemetry as m
m.sibling_set = lambda cpu: {cpu}
sys.argv = ['core_telemetry.py', '--cpu', sys.argv[1], '--output', sys.argv[2],
            '--', sys.executable, '-c', 'import sys; from pathlib import Path; Path(sys.argv[1]).touch()', sys.argv[3]]
raise SystemExit(m.main())
"""
            result = subprocess.run([sys.executable, "-c", code,
                str(min(os.sched_getaffinity(0))), str(output), str(child_marker)],
                process_group=0, capture_output=True, text=True, timeout=15)
            self.assertEqual(result.returncode, 2)
            self.assertIn("setsid --wait", result.stderr)
            self.assertFalse(child_marker.exists())

    def test_merge_regions(self):
        self.assertEqual(
            core_telemetry.merge_regions([(30, 40), (10, 20), (15, 25)]),
            [(10, 25), (30, 40)],
        )
        with self.assertRaises(ValueError):
            core_telemetry.merge_regions([(20, 10)])

    def test_overlap_ns(self):
        regions = [(10, 20), (30, 50)]
        self.assertEqual(core_telemetry.overlap_ns(0, 60, regions), 30)
        self.assertEqual(core_telemetry.overlap_ns(15, 35, regions), 10)
        self.assertEqual(core_telemetry.overlap_ns(20, 30, regions), 0)

    def test_load_timed_regions(self):
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.jsonl"
            second = Path(directory) / "second.jsonl"
            first.write_text(
                '{"kind":"header","pid":1}\n'
                '{"kind":"region","label":"warm-loop",'
                '"mono_t0_ns":10,"mono_t1_ns":20}\n'
                '{"kind":"region","label":"setup",'
                '"mono_t0_ns":0,"mono_t1_ns":100}\n'
            )
            second.write_text(
                '{"kind":"header","pid":2}\n'
                '{"kind":"region","label":"cold-loop",'
                '"mono_t0_ns":15,"mono_t1_ns":30}\n'
            )
            regions, count = core_telemetry.load_timed_regions([first, second])
            self.assertEqual(count, 2)
            self.assertEqual(regions, [(10, 30)])

    def test_malformed_sidecar_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "truncated.jsonl"
            path.write_text('{"kind":"header"}\n{"kind":"region"')
            with self.assertRaises(ValueError):
                core_telemetry.load_timed_regions([path])

    def test_interference_context(self):
        samples = [
            {
                "busy_seconds": {"3": 0.9, "51": 0.01},
                "timed_fraction": 0.5,
                "timed_overlap_seconds": 5.0,
                "foreign_runnable": [],
            },
            {
                "busy_seconds": {"3": 0.8, "51": 0.0},
                "timed_fraction": 1.0,
                "timed_overlap_seconds": 5.0,
                "foreign_runnable": [
                    {"tgid": 20, "tid": 21, "cpu": 3, "comm": "worker"}
                ],
            },
        ]
        summary = core_telemetry.interference_summary(
            samples, 3, [51]
        )
        self.assertEqual(summary["smt_sibling_busy_seconds"], 0.005)
        self.assertEqual(summary["measurement_cpu_foreign_seconds_estimate"], 5.0)
        self.assertEqual(summary["aggregate_core_interference_ratio"], 0.5005)
        self.assertNotIn("contaminated", summary)


if __name__ == "__main__":
    unittest.main()
