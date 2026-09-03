#!/usr/bin/env python3

import unittest
from pathlib import Path
import tempfile

import core_telemetry


class CoreTelemetryTest(unittest.TestCase):
    def test_busy_percent(self):
        self.assertEqual(core_telemetry.busy_percent((2, 10), (4, 20)), 20.0)
        self.assertEqual(core_telemetry.busy_percent((2, 10), (2, 10)), 0.0)

    def test_busy_seconds(self):
        self.assertEqual(core_telemetry.busy_seconds((2, 10), (4, 20), 100), 0.02)

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
                '{"kind":"region","mono_t0_ns":10,"mono_t1_ns":20}\n'
            )
            second.write_text(
                '{"kind":"header","pid":2}\n'
                '{"kind":"region","mono_t0_ns":15,"mono_t1_ns":30}\n'
            )
            regions, count = core_telemetry.load_timed_regions([first, second])
            self.assertEqual(count, 2)
            self.assertEqual(regions, [(10, 30)])


if __name__ == "__main__":
    unittest.main()
