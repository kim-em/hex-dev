#!/usr/bin/env python3
"""Check the declared comparison scope without taking performance samples."""
from copy import deepcopy
import unittest

from sturm_regression import AUXILIARY, NATIVE_FIXED, native_harness_pins, registrations


class RegistrationTest(unittest.TestCase):
    def setUp(self):
        self.lines = ["registered benchmarks:",
                      "Hex.SturmBench.runInteger expected complexity: n ^ 4",
                      "Hex.SturmFrontendBench.runPrepared expected complexity: n ^ 4",
                      AUXILIARY + " expected complexity: n ^ 2"]
        self.lines += [name + " [fixed] repeats=4" for name in sorted(NATIVE_FIXED)]
        self.lines += ["Hex.SturmExternalBench.runFlintCount [fixed] repeats=4"]

    def select(self):
        return registrations("\n".join(self.lines))

    def test_timing_scope_and_correctness_controls(self):
        names, native, excluded = self.select()
        self.assertEqual(len(names), 2)
        self.assertEqual(set(native), NATIVE_FIXED)
        self.assertEqual(set(excluded), {AUXILIARY, "Hex.SturmExternalBench.runFlintCount"})
        self.assertNotIn(AUXILIARY, names)

    def test_no_native_controls(self):
        self.lines = [line for line in self.lines if "runNative" not in line]
        with self.assertRaisesRegex(RuntimeError, "native fixed"):
            self.select()

    def test_missing_one_native_control(self):
        self.lines = [line for line in self.lines if "runNative64" not in line]
        with self.assertRaisesRegex(RuntimeError, "native fixed"):
            self.select()

    def test_duplicate_native_control(self):
        self.lines.append(sorted(NATIVE_FIXED)[0] + " [fixed] repeats=4")
        with self.assertRaisesRegex(RuntimeError, "native fixed"):
            self.select()

    def test_missing_auxiliary_requires_scope_review(self):
        self.lines = [line for line in self.lines if AUXILIARY not in line]
        with self.assertRaisesRegex(RuntimeError, "auxiliary registration"):
            self.select()

    def test_empty_timing_scope(self):
        self.lines = [line for line in self.lines if "expected complexity:" not in line]
        with self.assertRaisesRegex(RuntimeError, "unexpected computational"):
            self.select()

    def test_unknown_computational_namespace(self):
        self.lines.append("Other.run expected complexity: n")
        with self.assertRaisesRegex(RuntimeError, "unexpected computational"):
            self.select()

    def test_duplicate_timing_registration(self):
        self.lines.append(self.lines[1])
        with self.assertRaisesRegex(RuntimeError, "unexpected computational"):
            self.select()

    def test_unhashed_registration(self):
        self.lines[1] += " (no Hashable)"
        with self.assertRaisesRegex(RuntimeError, "unhashed"):
            self.select()


class NativePinTest(unittest.TestCase):
    def setUp(self):
        self.manifest = {"packages": [
            {"name": name, "type": "git", "rev": "old", "url": "https://example.test/" + name}
            for name in ("Cli", "«lean-bench»", "mathlib", "TauCeti")]}

    def test_proof_only_pin_changes_do_not_confuse_native_comparison(self):
        changed = deepcopy(self.manifest)
        changed["packages"][2]["rev"] = "new"
        changed["packages"][3]["rev"] = "new"
        self.assertEqual(native_harness_pins(changed), native_harness_pins(self.manifest))

    def test_cli_and_runner_pin_changes_are_visible(self):
        for index in (0, 1):
            changed = deepcopy(self.manifest)
            changed["packages"][index]["rev"] = "new"
            self.assertNotEqual(native_harness_pins(changed), native_harness_pins(self.manifest))

    def test_missing_cli_refused(self):
        self.manifest["packages"].pop(0)
        with self.assertRaisesRegex(RuntimeError, "dependency pin"):
            native_harness_pins(self.manifest)


if __name__ == "__main__":
    unittest.main()
