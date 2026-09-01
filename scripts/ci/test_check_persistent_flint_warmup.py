#!/usr/bin/env python3
"""Regression tests for the persistent FLINT fixed-benchmark warmup lint."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_persistent_flint_warmup as lint


class PersistentFlintWarmupTests(unittest.TestCase):
    def check_source(self, source: str) -> tuple[list[lint.Registration], list[lint.Registration]]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "bench" / "Sample" / "Bench.lean"
            path.parent.mkdir(parents=True)
            path.write_text(source, encoding="utf-8")
            return lint.check(root)

    def test_rejects_direct_cold_registration(self) -> None:
        registrations, failures = self.check_source(
            "def runFlint (_ : Unit) := Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
            "setup_fixed_benchmark runFlint where { repeats := 5 }\n"
        )
        self.assertEqual(len(registrations), 1)
        self.assertEqual(failures, registrations)

    def test_rejects_registration_without_where_clause(self) -> None:
        registrations, failures = self.check_source(
            "def runFlint (_ : Unit) := Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
            "setup_fixed_benchmark runFlint\n"
        )
        self.assertEqual(len(registrations), 1)
        self.assertEqual(failures, registrations)

    def test_rejects_cold_ntl_registration(self) -> None:
        registrations, failures = self.check_source(
            "partial def requestNtlLineWithRetry (_ : String) (_ : Nat) := pure \"\"\n"
            "def runNtl (_ : Unit) := requestNtlLineWithRetry \"ping\" 1\n"
            "setup_fixed_benchmark runNtl where { repeats := 5 }\n"
        )
        self.assertEqual(len(registrations), 1)
        self.assertEqual(failures, registrations)

    def test_accepts_warm_ntl_registration(self) -> None:
        registrations, failures = self.check_source(
            "partial def requestNtlLineWithRetry (_ : String) (_ : Nat) := pure \"\"\n"
            "def runNtl (_ : Unit) := requestNtlLineWithRetry \"ping\" 1\n"
            "def config := { repeats := 5, warmupFirstIter := true }\n"
            "setup_fixed_benchmark runNtl where config\n"
        )
        self.assertEqual(len(registrations), 1)
        self.assertEqual(failures, [])

    def test_follows_adapter_and_named_config(self) -> None:
        registrations, failures = self.check_source(
            "def callFlint := Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
            "def runAdapter (_ : Unit) := callFlint\n"
            "def compareConfig := { repeats := 5, warmupFirstIter := true }\n"
            "setup_fixed_benchmark runAdapter where compareConfig\n"
        )
        self.assertEqual(len(registrations), 1)
        self.assertEqual(failures, [])

    def test_explicit_false_override_fails_closed(self) -> None:
        registrations, failures = self.check_source(
            "def runFlint (_ : Unit) := Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
            "def warmConfig := { warmupFirstIter := true }\n"
            "setup_fixed_benchmark runFlint where\n"
            "  { warmConfig with warmupFirstIter := false }\n"
        )
        self.assertEqual(failures, registrations)

    def test_comments_do_not_fake_driver_or_warmup(self) -> None:
        registrations, failures = self.check_source(
            "/- Hex.BenchOracle.Flint.runOp -/\n"
            "def ordinary (_ : Unit) := pure 0\n"
            "setup_fixed_benchmark ordinary where { repeats := 5 }\n"
            "def runFlint (_ : Unit) := Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
            "-- warmupFirstIter := true\n"
            "setup_fixed_benchmark runFlint where { repeats := 5 }\n"
        )
        self.assertEqual(len(registrations), 1)
        self.assertEqual(failures, registrations)

    def test_follows_qualified_target_across_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            helper = root / "bench" / "SampleFlint.lean"
            main = root / "bench" / "Sample" / "Bench.lean"
            helper.parent.mkdir(parents=True)
            main.parent.mkdir(parents=True)
            helper.write_text(
                "def runFlint (_ : Unit) := "
                "Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
                "def config := { warmupFirstIter := true }\n",
                encoding="utf-8",
            )
            main.write_text(
                "setup_fixed_benchmark Sample.runFlint where Sample.config\n",
                encoding="utf-8",
            )
            registrations, failures = lint.check(root)
            self.assertEqual(len(registrations), 1)
            self.assertEqual(failures, [])

    def test_same_named_warm_config_in_other_file_does_not_mask_cold_config(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cold = root / "bench" / "Cold" / "Bench.lean"
            warm = root / "bench" / "Warm" / "Bench.lean"
            cold.parent.mkdir(parents=True)
            warm.parent.mkdir(parents=True)
            cold.write_text(
                "def runFlint (_ : Unit) := "
                "Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
                "def flintCompareConfig := { repeats := 5 }\n"
                "setup_fixed_benchmark runFlint where flintCompareConfig\n",
                encoding="utf-8",
            )
            warm.write_text(
                "def flintCompareConfig := { warmupFirstIter := true }\n",
                encoding="utf-8",
            )
            registrations, failures = lint.check(root)
            self.assertEqual(failures, registrations)

    def test_ambiguous_cross_file_config_fails_if_any_candidate_is_cold(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "bench" / "Target" / "Bench.lean"
            cold = root / "bench" / "ColdConfig.lean"
            warm = root / "bench" / "WarmConfig.lean"
            target.parent.mkdir(parents=True)
            target.write_text(
                "def runFlint (_ : Unit) := "
                "Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
                "setup_fixed_benchmark runFlint where Shared.config\n",
                encoding="utf-8",
            )
            cold.write_text("def config := { repeats := 5 }\n", encoding="utf-8")
            warm.write_text(
                "def config := { warmupFirstIter := true }\n", encoding="utf-8"
            )
            registrations, failures = lint.check(root)
            self.assertEqual(failures, registrations)

    def test_conditional_warm_config_fails_closed(self) -> None:
        registrations, failures = self.check_source(
            "def runFlint (_ : Unit) := Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
            "def config (external : Bool) := if external then "
            "{ warmupFirstIter := true } else {}\n"
            "setup_fixed_benchmark runFlint where config false\n"
        )
        self.assertEqual(failures, registrations)

    def test_follows_abbrev_and_attributed_partial_adapter(self) -> None:
        registrations, failures = self.check_source(
            "abbrev callFlint := Hex.BenchOracle.Flint.runOp \"x\" \"y\" #[]\n"
            "@[inline] partial def runAdapter (_ : Unit) := callFlint\n"
            "abbrev config := { warmupFirstIter := true }\n"
            "setup_fixed_benchmark runAdapter where config\n"
        )
        self.assertEqual(len(registrations), 1)
        self.assertEqual(failures, [])

    def test_repository_has_persistent_registrations(self) -> None:
        registrations, failures = lint.check(lint.REPO_ROOT)
        self.assertGreater(len(registrations), 0)
        self.assertEqual(failures, [])


if __name__ == "__main__":
    unittest.main()
