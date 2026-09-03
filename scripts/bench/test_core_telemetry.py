#!/usr/bin/env python3

import unittest
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

    def test_descendants(self):
        snapshot = {
            10: (1, "S", 0, "root"),
            11: (10, "S", 0, "child"),
            12: (11, "R", 1, "grandchild"),
            20: (1, "R", 1, "foreign"),
        }
        self.assertEqual(core_telemetry.descendants(10, snapshot), {10, 11, 12})

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

    def test_interference_verdict(self):
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
            samples, 3, [51], True, 0.6
        )
        self.assertEqual(summary["smt_sibling_busy_seconds"], 0.005)
        self.assertEqual(summary["measurement_cpu_foreign_seconds_estimate"], 5.0)
        self.assertEqual(summary["aggregate_core_interference_ratio"], 0.5005)
        self.assertFalse(summary["contaminated"])
        summary = core_telemetry.interference_summary(
            samples, 3, [51], True, 0.5
        )
        self.assertTrue(summary["contaminated"])

    def test_incomplete_regions_fail_closed(self):
        summary = core_telemetry.interference_summary([], 3, [51], False, 0.002)
        self.assertTrue(summary["contaminated"])


if __name__ == "__main__":
    unittest.main()
