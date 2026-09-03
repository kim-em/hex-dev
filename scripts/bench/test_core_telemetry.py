#!/usr/bin/env python3

import unittest

import core_telemetry


class CoreTelemetryTest(unittest.TestCase):
    def test_busy_percent(self):
        self.assertEqual(core_telemetry.busy_percent((2, 10), (4, 20)), 20.0)
        self.assertEqual(core_telemetry.busy_percent((2, 10), (2, 10)), 0.0)

    def test_descendants(self):
        snapshot = {
            10: (1, "S", 0, "root"),
            11: (10, "S", 0, "child"),
            12: (11, "R", 1, "grandchild"),
            20: (1, "R", 1, "foreign"),
        }
        self.assertEqual(core_telemetry.descendants(10, snapshot), {10, 11, 12})


if __name__ == "__main__":
    unittest.main()
