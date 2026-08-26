#!/usr/bin/env python3
"""Regression tests for the reusable matched fresh-module harness."""

from __future__ import annotations

import dataclasses
import io
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

from scripts.bench import fresh_module_sweep as sweep


EXPECTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
PAIR = sweep.ProbePair(
    name="center-direct",
    reference=sweep.ProbeModule("HexIntervalMathlib.CenterBaseline"),
    candidate=sweep.ProbeModule(
        "HexIntervalMathlib.CenterDirect", EXPECTED_AXIOMS
    ),
    metadata={"family": "test"},
)
SPEC = sweep.SweepSpec(
    description="generic harness test",
    pairs=(PAIR,),
    probe_target="HexIntervalMathlibProofProbe",
    schema="test",
    measurement="test",
    output_stem="test",
)
CALLER = Path(__file__)


class ProvenanceTests(unittest.TestCase):
    def test_transitive_local_sources_are_included(self) -> None:
        sources = set(sweep.provenance_sources(SPEC, CALLER))
        self.assertIn(
            sweep.ROOT / "HexIntervalMathlib" / "Experiment" / "Center.lean",
            sources,
        )
        self.assertIn(
            sweep.ROOT / "HexInterval" / "Experiment" / "Center.lean",
            sources,
        )

    def test_source_hash_changes_with_source_content(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Transitive.lean"
            source.write_text("def value := 1\n", encoding="utf-8")
            with mock.patch.object(sweep, "ROOT", root), mock.patch.object(
                sweep, "provenance_sources", return_value=[source]
            ):
                before = sweep.source_hashes(SPEC, CALLER)
                source.write_text("def value := 2\n", encoding="utf-8")
                after = sweep.source_hashes(SPEC, CALLER)
            self.assertNotEqual(before, after)

    def test_untracked_checkout_content_marks_dirty_and_changes_state(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(
                ["git", "config", "user.email", "probe-test@example.invalid"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Probe Test"],
                cwd=root,
                check=True,
            )
            tracked = root / "tracked.txt"
            tracked.write_text("tracked\n", encoding="utf-8")
            subprocess.run(["git", "add", "tracked.txt"], cwd=root, check=True)
            subprocess.run(
                ["git", "commit", "-qm", "initial"], cwd=root, check=True
            )
            clean = sweep.checkout_state(root)
            untracked = root / "untracked.txt"
            untracked.write_text("first\n", encoding="utf-8")
            first = sweep.checkout_state(root)
            untracked.write_text("second\n", encoding="utf-8")
            second = sweep.checkout_state(root)
            self.assertFalse(clean["dirty"])
            self.assertTrue(first["dirty"])
            self.assertNotEqual(clean["state_sha256"], first["state_sha256"])
            self.assertNotEqual(first["state_sha256"], second["state_sha256"])

    def test_checkout_git_failures_fail_closed(self) -> None:
        commands = [
            ("rev-parse", "HEAD^{tree}"),
            ("status", "--porcelain=v1", "-z", "--untracked-files=all"),
            ("diff", "--binary", "HEAD"),
            ("diff", "--binary", "--cached"),
            ("ls-files", "--others", "--exclude-standard", "-z"),
        ]
        for failing in commands:
            with self.subTest(command=failing):
                def fake_git(_directory: Path, *args: str) -> subprocess.CompletedProcess[bytes]:
                    if args == failing:
                        return subprocess.CompletedProcess(
                            ["git", *args], 1, stdout=b"", stderr=b"forced failure"
                        )
                    output = b"deadbeef\n" if args[0] == "rev-parse" else b""
                    return subprocess.CompletedProcess(
                        ["git", *args], 0, stdout=output, stderr=b""
                    )

                with mock.patch.object(sweep, "_git_bytes", side_effect=fake_git):
                    with self.assertRaisesRegex(RuntimeError, "forced failure"):
                        sweep.checkout_state(Path("/unused"))

    def test_missing_declared_provenance_source_fails_closed(self) -> None:
        spec = sweep.SweepSpec(
            description="missing provenance",
            pairs=(PAIR,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            extra_sources=(Path("missing.md"),),
        )
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(
            sweep, "ROOT", Path(directory)
        ), mock.patch.object(
            sweep, "local_import_sources", return_value=set()
        ):
            with self.assertRaisesRegex(
                RuntimeError, "missing declared provenance"
            ):
                sweep.provenance_sources(spec, CALLER)


class ProcessGroupTests(unittest.TestCase):
    def test_run_timed_records_scheduler_metrics(self) -> None:
        proc, elapsed, metrics = sweep.run_timed(["true"], 5)
        self.assertEqual(proc.returncode, 0)
        self.assertGreater(elapsed, 0)
        if sweep.time_binary() is not None:
            self.assertIsNotNone(metrics["peak_rss_kb"])
            self.assertIsNotNone(metrics["user_seconds"])
            self.assertIsNotNone(metrics["system_seconds"])
            self.assertIsNotNone(metrics["cpu_percent"])
        self.assertIsNotNone(metrics["precise_child_user_seconds"])
        self.assertIsNotNone(metrics["precise_child_system_seconds"])

    @unittest.skipUnless(Path("/proc").is_dir(), "requires procfs")
    def test_run_timed_invokes_group_cleanup(self) -> None:
        with mock.patch.object(sweep, "time_binary", return_value=None), \
                mock.patch.object(
                    sweep,
                    "terminate_process_group",
                    wraps=sweep.terminate_process_group,
                ) as cleanup:
            with self.assertRaises(subprocess.TimeoutExpired):
                sweep.run_timed(
                    [sys.executable, "-c", "import time; time.sleep(60)"], 0.05
                )
        cleanup.assert_called_once()

    @unittest.skipUnless(Path("/proc").is_dir(), "requires procfs")
    def test_sigkill_fallback_reaps_resistant_descendant(self) -> None:
        descendant_script = (
            "import signal,time; "
            "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
            "print('ready', flush=True); time.sleep(60)"
        )
        script = (
            "import signal,subprocess,sys,time; "
            "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
            f"child=subprocess.Popen([sys.executable,'-c',{descendant_script!r}], "
            "stdout=subprocess.PIPE, text=True); "
            "child.stdout.readline(); print(child.pid, flush=True); time.sleep(60)"
        )
        parent = subprocess.Popen(
            [sys.executable, "-c", script],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        descendant: int | None = None
        try:
            assert parent.stdout is not None
            descendant = int(parent.stdout.readline().strip())
            sweep.terminate_process_group(parent, grace=0.1)
            deadline = time.monotonic() + 3
            while (Path(f"/proc/{descendant}").exists()
                   and time.monotonic() < deadline):
                time.sleep(0.05)
            self.assertEqual(parent.returncode, -signal.SIGKILL)
            self.assertFalse(Path(f"/proc/{descendant}").exists())
        finally:
            if parent.poll() is None:
                try:
                    os.killpg(parent.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                parent.communicate()
            if descendant is not None and Path(f"/proc/{descendant}").exists():
                try:
                    os.kill(descendant, signal.SIGKILL)
                except ProcessLookupError:
                    pass


class PairingTests(unittest.TestCase):
    @staticmethod
    def shared_arm(
        *,
        foreign: float = 0.0,
        residual: float = 0.0,
        noninterrupt_residual: float | None = None,
        interrupt: float = 0.0,
        sibling_busy: float = 0.0,
    ) -> dict[str, object]:
        host = {
            "concurrent_lake_lean_count": 0,
            "load_1m_per_cpu": 0.0,
            "affinity_cpu_frequency_khz": "2500000",
        }
        return {
            "wall_nanos": 1_000_000_000,
            "peak_rss_kb": 1,
            "axioms": None,
            "cpu_percent": 100.0,
            "host_before": host,
            "host_after": host,
            "cpu_accounting": {
                "clock_ticks_per_second": 100,
                "measurement_cpu_residual_seconds": residual,
                "measurement_cpu_interrupt_seconds": interrupt,
                "measurement_cpu_noninterrupt_residual_seconds": (
                    residual
                    if noninterrupt_residual is None
                    else noninterrupt_residual
                ),
                "measurement_cpu_foreign_seconds": foreign,
                "aggregate_core_interference_seconds":
                    foreign + sibling_busy,
                "mean_frequency_khz": 2_500_000,
                "pressure_some_delta_us": 0,
                "per_cpu": {"95": {"busy_seconds": sibling_busy}},
            },
        }

    def test_interrupt_ticks_are_not_classified_as_foreign_work(self) -> None:
        raw, noninterrupt, foreign = sweep.foreign_cpu_accounting(
            target_busy_seconds=1.08,
            child_cpu_seconds=0.99,
            runner_cpu_seconds_value=0.01,
            interrupt_seconds=0.07,
        )
        self.assertAlmostEqual(raw, 0.08)
        self.assertAlmostEqual(noninterrupt, 0.01)
        self.assertAlmostEqual(foreign, 0.01)

    def test_shared_host_retries_complete_pair_in_same_order(self) -> None:
        bad = self.shared_arm(sibling_busy=0.10)
        good = self.shared_arm(sibling_busy=0.01)
        modules = (
            ("reference", sweep.ProbeModule("Probe.Baseline")),
            ("candidate", sweep.ProbeModule("Probe.Candidate")),
        )
        with mock.patch.object(
            sweep, "build_sample", side_effect=[bad, good, good, good]
        ) as build, mock.patch.object(
            sweep, "sampled_host_state", return_value={}
        ), mock.patch.object(sweep, "cpu_affinity", return_value=[47]):
            with mock.patch.object(
                sweep,
                "wait_for_shared_host_window",
                return_value={
                    "admitted": True,
                    "elapsed_seconds": 2.0,
                    "rejected_windows": [],
                    "accepted_window": {},
                },
            ):
                accepted, rejected, preflight_failure = (
                    sweep.build_shared_host_pair(
                        "pair", 1, 0, modules,
                        60.0, 47, [47, 95], [95], 0.002, 2,
                        2.0, 300.0,
                    )
                )
        assert accepted is not None
        self.assertIsNone(preflight_failure)
        self.assertEqual(accepted["measurement_attempt"], 2)
        self.assertEqual(len(rejected), 1)
        self.assertEqual(
            [call.args[0] for call in build.call_args_list],
            [
                "Probe.Baseline", "Probe.Candidate",
                "Probe.Baseline", "Probe.Candidate",
            ],
        )
        self.assertRegex(
            "; ".join(rejected[0]["issues"]),
            "aggregate measurement-CPU foreign and SMT-sibling",
        )

    def test_shared_host_retry_exhaustion_admits_no_pair(self) -> None:
        modules = (
            ("candidate", sweep.ProbeModule("Probe.Candidate")),
            ("reference", sweep.ProbeModule("Probe.Baseline")),
        )
        with mock.patch.object(
            sweep,
            "build_sample",
            side_effect=[
                self.shared_arm(foreign=0.10),
                self.shared_arm(foreign=0.10),
                self.shared_arm(foreign=0.10),
                self.shared_arm(foreign=0.10),
            ],
        ), mock.patch.object(
            sweep, "sampled_host_state", return_value={}
        ), mock.patch.object(sweep, "cpu_affinity", return_value=[47]):
            with mock.patch.object(
                sweep,
                "wait_for_shared_host_window",
                return_value={
                    "admitted": True,
                    "elapsed_seconds": 2.0,
                    "rejected_windows": [],
                    "accepted_window": {},
                },
            ):
                accepted, rejected, preflight_failure = (
                    sweep.build_shared_host_pair(
                        "pair", 1, 0, modules,
                        60.0, 47, [47, 95], [95], 0.002, 1,
                        2.0, 300.0,
                    )
                )
        self.assertIsNone(accepted)
        self.assertIsNone(preflight_failure)
        self.assertEqual(len(rejected), 2)
        self.assertEqual(rejected[-1]["build_order"], [
            "candidate", "reference"
        ])
        self.assertRegex(
            "; ".join(rejected[-1]["issues"]),
            "aggregate measurement-CPU foreign",
        )

    def test_shared_host_hard_cap_is_33_complete_attempts(self) -> None:
        modules = (
            ("reference", sweep.ProbeModule("Probe.Baseline")),
            ("candidate", sweep.ProbeModule("Probe.Candidate")),
        )
        with (
            mock.patch.object(
                sweep,
                "build_sample",
                return_value=self.shared_arm(foreign=0.10),
            ) as build,
            mock.patch.object(sweep, "sampled_host_state", return_value={}),
            mock.patch.object(sweep, "cpu_affinity", return_value=[47]),
            mock.patch.object(sys, "stdout", new=io.StringIO()),
            mock.patch.object(sys, "stderr", new=io.StringIO()),
            mock.patch.object(
                sweep,
                "wait_for_shared_host_window",
                return_value={
                    "admitted": True,
                    "elapsed_seconds": 2.0,
                    "rejected_windows": [],
                    "accepted_window": {},
                },
            ),
        ):
            accepted, rejected, preflight_failure = (
                sweep.build_shared_host_pair(
                    "pair", 1, 0, modules,
                    60.0, 47, [47, 95], [95], 0.002,
                    sweep.MAX_PAIR_RETRIES, 2.0, 300.0,
                )
            )
        self.assertIsNone(accepted)
        self.assertIsNone(preflight_failure)
        self.assertEqual(len(rejected), 33)
        self.assertEqual(build.call_count, 66)
        self.assertEqual(rejected[-1]["measurement_attempt"], 33)

    def test_interrupt_cannot_mask_negative_cpu_accounting(self) -> None:
        arm = self.shared_arm(
            residual=0.10,
            noninterrupt_residual=-0.05,
            interrupt=0.15,
        )
        issues = sweep.shared_host_arm_issues(
            "pair", 1, "reference", arm, 47, [95], 0.02
        )
        self.assertRegex(
            "; ".join(issues),
            "child CPU time exceeds pinned-CPU busy time",
        )

    def test_foreign_and_sibling_interference_share_one_allowance(self) -> None:
        arm = self.shared_arm(foreign=0.02, sibling_busy=0.02)
        issues = sweep.shared_host_arm_issues(
            "pair", 1, "reference", arm, 47, [95], 0.02
        )
        self.assertRegex(
            "; ".join(issues),
            "aggregate measurement-CPU foreign and SMT-sibling",
        )

    def test_preflight_waits_out_sibling_activity(self) -> None:
        def ticks(
            target_user: int = 0, sibling_user: int = 0
        ) -> dict[int, dict[str, int]]:
            fields = {
                "user": 0, "nice": 0, "system": 0, "idle": 100,
                "iowait": 0, "irq": 0, "softirq": 0, "steal": 0,
            }
            target = dict(fields)
            target["user"] = target_user
            sibling = dict(fields)
            sibling["user"] = sibling_user
            return {47: target, 95: sibling}

        with mock.patch.object(
            sweep,
            "cpu_ticks",
            side_effect=[
                ticks(), ticks(sibling_user=5),
                ticks(), ticks(target_user=1),
            ],
        ), mock.patch.object(
            sweep.time, "sleep"
        ) as sleep, mock.patch.object(
            sweep.time, "monotonic", side_effect=[0.0, 2.0, 4.0]
        ):
            result = sweep.wait_for_shared_host_window(
                47, [47, 95], [95], 2.0, 300.0
            )
        self.assertTrue(result["admitted"])
        self.assertEqual(len(result["rejected_windows"]), 1)
        self.assertEqual(
            result["accepted_window"]["per_cpu"]["47"][
                "noninterrupt_busy_ticks"
            ],
            1,
        )
        self.assertEqual(sleep.call_count, 2)

    def test_preflight_timeout_is_explicit(self) -> None:
        fields = {
            "user": 0, "nice": 0, "system": 0, "idle": 100,
            "iowait": 0, "irq": 0, "softirq": 0, "steal": 0,
        }
        before = {47: dict(fields), 95: dict(fields)}
        after = {47: dict(fields), 95: {**fields, "user": 5}}
        with mock.patch.object(
            sweep, "cpu_ticks", side_effect=[before, after]
        ), mock.patch.object(
            sweep.time, "sleep"
        ), mock.patch.object(
            sweep.time, "monotonic", side_effect=[0.0, 2.0]
        ):
            result = sweep.wait_for_shared_host_window(
                47, [47, 95], [95], 2.0, 2.0
            )
        self.assertFalse(result["admitted"])
        self.assertEqual(len(result["rejected_windows"]), 1)
        self.assertRegex(
            "; ".join(result["issues"]), "did not become quiet"
        )

    def test_preflight_timeout_builds_no_pair(self) -> None:
        modules = (
            ("reference", sweep.ProbeModule("Probe.Baseline")),
            ("candidate", sweep.ProbeModule("Probe.Candidate")),
        )
        failure = {
            "admitted": False,
            "elapsed_seconds": 300.0,
            "rejected_windows": [],
            "accepted_window": None,
            "issues": ["physical core remained busy"],
        }
        with mock.patch.object(
            sweep, "wait_for_shared_host_window", return_value=failure
        ), mock.patch.object(sweep, "build_sample") as build:
            accepted, rejected, preflight_failure = (
                sweep.build_shared_host_pair(
                    "pair", 1, 0, modules,
                    60.0, 47, [47, 95], [95], 0.002, 8,
                    2.0, 300.0,
                )
            )
        self.assertIsNone(accepted)
        self.assertEqual(rejected, [])
        assert preflight_failure is not None
        self.assertEqual(preflight_failure["issues"], [
            "physical core remained busy"
        ])
        build.assert_not_called()

    def test_frequency_residency_uses_arm_weighted_mean(self) -> None:
        delta = sweep.frequency_residency_delta(
            {1_500_000: 10, 3_000_000: 20},
            {1_500_000: 11, 3_000_000: 23},
        )
        self.assertEqual(delta, {1_500_000: 1, 3_000_000: 3})
        self.assertEqual(
            sweep.mean_residency_frequency(delta), 2_625_000
        )

    def test_summary_uses_each_pairs_adjacent_measurements(self) -> None:
        rows: dict[str, list[dict[str, object]]] = {
            PAIR.name: [{
                "round": 1,
                "build_order": ["reference", "candidate"],
                "reference": {
                    "wall_nanos": 100,
                    "peak_rss_kb": None,
                    "axioms": None,
                },
                "candidate": {
                    "wall_nanos": 125,
                    "peak_rss_kb": None,
                    "axioms": list(EXPECTED_AXIOMS),
                },
                "signed_wall_delta_nanos": 25,
            }]
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(SPEC, rows)
        self.assertEqual(
            summary[PAIR.name]["signed_wall_delta_nanos"], [25]
        )
        self.assertFalse(summary[PAIR.name]["null_control"])

    def test_axiom_policy_is_per_module(self) -> None:
        sample = {
            "wall_nanos": 1,
            "peak_rss_kb": None,
            "axioms": list(EXPECTED_AXIOMS),
        }
        sweep.validate_axioms(
            "case", "candidate",
            sweep.ProbeModule("Probe", EXPECTED_AXIOMS),
            sample,
        )
        with self.assertRaisesRegex(RuntimeError, "axiom set mismatch"):
            sweep.validate_axioms(
                "case", "reference", sweep.ProbeModule("Baseline"), sample
            )

    def test_rotation_is_stable(self) -> None:
        self.assertEqual(sweep.rotate(["a", "b", "c"], 1), ["b", "c", "a"])
        self.assertEqual(sweep.rotate(["a", "b", "c"], 4), ["b", "c", "a"])

    def test_pair_orientation_alternates(self) -> None:
        self.assertEqual(
            [role for role, _module in sweep.ordered_modules(PAIR, 0)],
            ["reference", "candidate"],
        )
        self.assertEqual(
            [role for role, _module in sweep.ordered_modules(PAIR, 1)],
            ["candidate", "reference"],
        )

    def test_null_pair_orientation_alternates_with_one_module(self) -> None:
        module = sweep.ProbeModule("Probe.Baseline")
        pair = sweep.ProbePair(
            "null", module, module, {}, null_control=True
        )
        self.assertEqual(
            sweep.ordered_modules(pair, 0),
            [("reference", module), ("candidate", module)],
        )
        self.assertEqual(
            sweep.ordered_modules(pair, 1),
            [("candidate", module), ("reference", module)],
        )
        first_roles = [
            sweep.ordered_modules(pair, round_index)[0][0]
            for round_index in range(6)
        ]
        self.assertEqual(first_roles.count("reference"), 3)
        self.assertEqual(first_roles.count("candidate"), 3)

    def test_null_summary_preserves_candidate_minus_reference_sign(self) -> None:
        module = sweep.ProbeModule("Probe.Baseline")
        pair = sweep.ProbePair(
            "null", module, module, {}, null_control=True
        )
        spec = sweep.SweepSpec(
            description="null",
            pairs=(pair,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        rows = {
            pair.name: [{
                "round": 1,
                "build_order": ["candidate", "reference"],
                "reference": {
                    "wall_nanos": 120,
                    "peak_rss_kb": None,
                    "axioms": None,
                },
                "candidate": {
                    "wall_nanos": 100,
                    "peak_rss_kb": None,
                    "axioms": None,
                },
                "signed_wall_delta_nanos": -20,
            }]
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, rows)[pair.name]
        self.assertTrue(summary["null_control"])
        self.assertEqual(summary["signed_wall_delta_nanos"], [-20])
        self.assertEqual(summary["median_signed_wall_delta_nanos"], -20)

    def test_robust_null_envelope_is_floored_by_observed_outlier(self) -> None:
        statistics = sweep.robust_null_statistics([0, 0, 0, 0, 0, 100])
        self.assertEqual(statistics["tukey_envelope_nanos"], 0)
        self.assertEqual(statistics["max_absolute_delta_nanos"], 100)
        self.assertEqual(statistics["envelope_nanos"], 100)
        self.assertEqual(statistics["outlier_count"], 1)

    def test_summary_metadata_cannot_spoof_null_control(self) -> None:
        module = sweep.ProbeModule("Probe.Baseline")
        pair = sweep.ProbePair(
            "null", module, module, {"null_control": False}, null_control=True
        )
        spec = sweep.SweepSpec(
            description="null",
            pairs=(pair,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        rows = {
            pair.name: [{
                "reference": {"wall_nanos": 1, "peak_rss_kb": None},
                "candidate": {"wall_nanos": 1, "peak_rss_kb": None},
                "signed_wall_delta_nanos": 0,
            }]
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, rows)[pair.name]
        self.assertTrue(summary["null_control"])

    def test_summary_resolves_against_magnitude_comparable_control(self) -> None:
        cheap = sweep.ProbeModule("Probe.Cheap")
        expensive = sweep.ProbeModule("Probe.Expensive")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair("cheap", cheap, cheap, {}, null_control=True),
            sweep.ProbePair(
                "expensive", expensive, expensive, {}, null_control=True
            ),
            sweep.ProbePair(
                "tactic",
                expensive,
                candidate,
                {"tactic_budget_ms": 100},
            ),
        )
        spec = sweep.SweepSpec(
            description="resolution",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )

        def rows(wall: int, deltas: list[int]) -> list[dict[str, object]]:
            return [{
                "reference": {
                    "wall_nanos": wall,
                    "peak_rss_kb": None,
                },
                "candidate": {
                    "wall_nanos": wall + delta,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos": delta,
            } for delta in deltas]

        samples = {
            "cheap": rows(100_000_000, [-1_000_000, 1_000_000]),
            "expensive": rows(
                1_000_000_000, [-10_000_000, 10_000_000]
            ),
            "tactic": rows(
                1_000_000_000, [85_000_000, 95_000_000]
            ),
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, samples)
        self.assertEqual(
            summary["tactic"]["comparable_control"], "expensive"
        )
        self.assertEqual(summary["tactic"]["resolution"], "resolved")
        self.assertEqual(summary["tactic"]["budget_status"], "unresolved")

    def test_one_sided_null_uses_zero_centred_envelope(self) -> None:
        module = sweep.ProbeModule("Probe.Baseline")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair(
                "null", module, module, {}, null_control=True
            ),
            sweep.ProbePair("effect", module, candidate, {}),
        )
        spec = sweep.SweepSpec(
            description="one-sided null",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )

        def rows(deltas: list[int]) -> list[dict[str, object]]:
            return [{
                "reference": {"wall_nanos": 1_000, "peak_rss_kb": None},
                "candidate": {
                    "wall_nanos": 1_000 + delta,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos": delta,
            } for delta in deltas]

        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(
                spec, {"null": rows([90, 100]), "effect": rows([50, 50])}
            )
        self.assertEqual(summary["null"]["null_spread_nanos"], 10)
        self.assertEqual(
            summary["effect"]["comparable_null_envelope_nanos"], 105
        )
        self.assertEqual(summary["effect"]["resolution"], "unresolved")

    def test_import_baseline_is_subtracted_by_round(self) -> None:
        baseline = sweep.ProbeModule("Probe.Baseline")
        reference = sweep.ProbeModule("Probe.Reference")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair(
                "baseline", baseline, baseline, {}, null_control=True
            ),
            sweep.ProbePair("effect", reference, candidate, {}),
        )
        spec = sweep.SweepSpec(
            description="baseline subtraction",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            import_baseline_control="baseline",
        )

        def row(
            round_index: int, reference_wall: int, candidate_wall: int
        ) -> dict[str, object]:
            return {
                "round": round_index,
                "reference": {
                    "wall_nanos": reference_wall,
                    "peak_rss_kb": None,
                },
                "candidate": {
                    "wall_nanos": candidate_wall,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos":
                    candidate_wall - reference_wall,
            }

        rows = {
            "baseline": [row(1, 1_000, 1_000), row(2, 1_100, 1_100)],
            "effect": [row(1, 1_400, 1_200), row(2, 1_600, 1_300)],
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, rows)
        effect = summary["effect"]
        self.assertEqual(
            effect["median_reference_workload_wall_nanos"], 450
        )
        self.assertEqual(
            effect["median_candidate_workload_wall_nanos"], 200
        )
        self.assertEqual(
            effect["reference_over_candidate_workload_ratio"], 2.25
        )
        self.assertEqual(
            effect["import_baseline_robust_envelope_nanos"], 100
        )
        self.assertEqual(effect["workload_ratio_resolution"], "resolved")
        self.assertAlmostEqual(
            effect[
                "maximum_raw_reference_over_zero_workload_candidate_ratio"
            ],
            1_500 / 1_050,
        )

    def test_import_baseline_noise_limits_workload_ratio(self) -> None:
        baseline = sweep.ProbeModule("Probe.Baseline")
        reference = sweep.ProbeModule("Probe.Reference")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair(
                "baseline", baseline, baseline, {}, null_control=True
            ),
            sweep.ProbePair("effect", reference, candidate, {}),
        )
        spec = sweep.SweepSpec(
            description="baseline noise",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            import_baseline_control="baseline",
        )

        def row(
            round_index: int, reference_wall: int, candidate_wall: int
        ) -> dict[str, object]:
            return {
                "round": round_index,
                "reference": {
                    "wall_nanos": reference_wall,
                    "peak_rss_kb": None,
                },
                "candidate": {
                    "wall_nanos": candidate_wall,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos":
                    candidate_wall - reference_wall,
            }

        rows = {
            "baseline": [row(1, 1_000, 1_000), row(2, 1_200, 1_200)],
            "effect": [row(1, 1_150, 1_100), row(2, 1_350, 1_300)],
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, rows)
        effect = summary["effect"]
        self.assertEqual(
            effect["import_baseline_robust_envelope_nanos"], 200
        )
        self.assertEqual(
            effect["median_reference_workload_wall_nanos"], 150
        )
        self.assertEqual(
            effect["workload_ratio_resolution"], "baseline-limited"
        )

    def test_workload_control_is_subtracted_by_round(self) -> None:
        baseline = sweep.ProbeModule("Probe.Baseline")
        reference = sweep.ProbeModule("Probe.Reference")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair(
                "baseline", baseline, baseline, {}, null_control=True
            ),
            sweep.ProbePair(
                "large-null", reference, reference, {}, null_control=True
            ),
            sweep.ProbePair("construction", reference, candidate, {}),
            sweep.ProbePair(
                "full",
                reference,
                candidate,
                {
                    "workload_control": "construction",
                    "ratio_threshold": 1.5,
                },
            ),
        )
        spec = sweep.SweepSpec(
            description="construction subtraction",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            import_baseline_control="baseline",
        )

        def row(
            round_index: int, reference_wall: int, candidate_wall: int
        ) -> dict[str, object]:
            return {
                "round": round_index,
                "reference": {
                    "wall_nanos": reference_wall,
                    "peak_rss_kb": None,
                },
                "candidate": {
                    "wall_nanos": candidate_wall,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos":
                    candidate_wall - reference_wall,
            }

        rows = {
            "baseline": [row(1, 100, 100), row(2, 120, 120)],
            "large-null": [row(1, 600, 600), row(2, 620, 620)],
            "construction": [row(1, 400, 300), row(2, 450, 350)],
            "full": [row(1, 600, 400), row(2, 670, 470)],
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, rows)
        full = summary["full"]
        self.assertEqual(full["workload_control"], "construction")
        self.assertEqual(
            full["median_reference_net_workload_wall_nanos"], 210
        )
        self.assertEqual(
            full["median_candidate_net_workload_wall_nanos"], 110
        )
        self.assertAlmostEqual(
            full["reference_over_candidate_net_workload_ratio"],
            210 / 110,
        )
        self.assertEqual(full["net_workload_ratio_resolution"], "resolved")
        self.assertEqual(
            full["ratio_threshold_basis"],
            "import-and-workload-control-subtracted",
        )
        self.assertAlmostEqual(full["ratio_lower_bound"], 210 / 110)
        self.assertAlmostEqual(full["ratio_upper_bound"], 210 / 110)
        self.assertEqual(full["ratio_threshold_status"], "passed")

    def test_ratio_threshold_requires_noise_separation(self) -> None:
        baseline = sweep.ProbeModule("Probe.Baseline")
        reference = sweep.ProbeModule("Probe.Reference")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair(
                "baseline", baseline, baseline, {}, null_control=True
            ),
            sweep.ProbePair(
                "large-null", reference, reference, {}, null_control=True
            ),
            sweep.ProbePair(
                "ratio",
                reference,
                candidate,
                {"ratio_threshold": 2.0},
            ),
            sweep.ProbePair(
                "failed",
                reference,
                candidate,
                {"ratio_threshold": 2.0},
            ),
            sweep.ProbePair(
                "noise-limited",
                reference,
                candidate,
                {"ratio_threshold": 2.0},
            ),
        )
        spec = sweep.SweepSpec(
            description="ratio threshold",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            import_baseline_control="baseline",
        )

        def row(
            round_index: int, reference_wall: int, candidate_wall: int
        ) -> dict[str, object]:
            return {
                "round": round_index,
                "reference": {
                    "wall_nanos": reference_wall,
                    "peak_rss_kb": None,
                },
                "candidate": {
                    "wall_nanos": candidate_wall,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos":
                    candidate_wall - reference_wall,
            }

        rows = {
            "baseline": [row(1, 100, 100), row(2, 100, 100)],
            "large-null": [row(1, 600, 599), row(2, 599, 600)],
            "ratio": [row(1, 301, 200), row(2, 301, 200)],
            "failed": [row(1, 250, 200), row(2, 250, 200)],
            "noise-limited": [
                row(1, 201, 200),
                row(2, 201, 200),
            ],
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, rows)
        ratio = summary["ratio"]
        self.assertAlmostEqual(
            ratio["reference_over_candidate_workload_ratio"], 201 / 100
        )
        self.assertEqual(ratio["workload_ratio_resolution"], "resolved")
        self.assertLess(ratio["ratio_lower_bound"], 2.0)
        self.assertGreater(ratio["ratio_upper_bound"], 2.0)
        self.assertEqual(ratio["ratio_threshold_status"], "unresolved")
        failed = summary["failed"]
        self.assertLessEqual(failed["ratio_upper_bound"], 2.0)
        self.assertEqual(failed["ratio_threshold_status"], "failed")
        noise_limited = summary["noise-limited"]
        self.assertEqual(
            noise_limited["workload_ratio_resolution"], "noise-limited"
        )
        self.assertEqual(
            noise_limited["ratio_threshold_status"], "unresolved"
        )

    def test_ratio_threshold_handles_unbounded_upper_and_missing_control(
        self,
    ) -> None:
        baseline = sweep.ProbeModule("Probe.Baseline")
        reference = sweep.ProbeModule("Probe.Reference")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair(
                "baseline", baseline, baseline, {}, null_control=True
            ),
            sweep.ProbePair(
                "large-null", reference, reference, {}, null_control=True
            ),
            sweep.ProbePair(
                "unbounded-upper",
                reference,
                candidate,
                {"ratio_threshold": 2.0},
            ),
            sweep.ProbePair(
                "missing-control",
                reference,
                candidate,
                {"ratio_threshold": 2.0},
            ),
        )
        spec = sweep.SweepSpec(
            description="ratio threshold edge cases",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            import_baseline_control="baseline",
        )

        def row(
            round_index: int, reference_wall: int, candidate_wall: int
        ) -> dict[str, object]:
            return {
                "round": round_index,
                "reference": {
                    "wall_nanos": reference_wall,
                    "peak_rss_kb": None,
                },
                "candidate": {
                    "wall_nanos": candidate_wall,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos":
                    candidate_wall - reference_wall,
            }

        rows = {
            "baseline": [row(1, 100, 100), row(2, 100, 100)],
            "large-null": [row(1, 600, 599), row(2, 599, 600)],
            "unbounded-upper": [
                row(1, 110, 101),
                row(2, 110, 101),
            ],
            "missing-control": [
                row(1, 5_000, 2_000),
                row(2, 5_000, 2_000),
            ],
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, rows)

        unbounded = summary["unbounded-upper"]
        self.assertEqual(unbounded["ratio_lower_bound"], 4.5)
        self.assertIsNone(unbounded["ratio_upper_bound"])
        self.assertEqual(unbounded["ratio_threshold_status"], "passed")

        missing = summary["missing-control"]
        self.assertEqual(missing["resolution"], "no-comparable-control")
        self.assertIsNone(missing["ratio_lower_bound"])
        self.assertIsNone(missing["ratio_upper_bound"])
        self.assertEqual(
            missing["ratio_threshold_status"], "no-comparable-control"
        )

    def test_net_workload_threshold_is_noise_limited(self) -> None:
        baseline = sweep.ProbeModule("Probe.Baseline")
        reference = sweep.ProbeModule("Probe.Reference")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair(
                "baseline", baseline, baseline, {}, null_control=True
            ),
            sweep.ProbePair(
                "large-null", reference, reference, {}, null_control=True
            ),
            sweep.ProbePair("construction", reference, candidate, {}),
            sweep.ProbePair(
                "full",
                reference,
                candidate,
                {
                    "workload_control": "construction",
                    "ratio_threshold": 2.0,
                },
            ),
        )
        spec = sweep.SweepSpec(
            description="net workload resolution",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            import_baseline_control="baseline",
        )

        def row(
            round_index: int, reference_wall: int, candidate_wall: int
        ) -> dict[str, object]:
            return {
                "round": round_index,
                "reference": {
                    "wall_nanos": reference_wall,
                    "peak_rss_kb": None,
                },
                "candidate": {
                    "wall_nanos": candidate_wall,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos":
                    candidate_wall - reference_wall,
            }

        rows = {
            "baseline": [row(1, 100, 100), row(2, 100, 100)],
            "large-null": [row(1, 600, 590), row(2, 590, 600)],
            "construction": [
                row(1, 400, 300),
                row(2, 400, 300),
            ],
            "full": [row(1, 440, 320), row(2, 440, 320)],
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            full = sweep.summarize(spec, rows)["full"]

        self.assertEqual(
            full["median_reference_net_workload_wall_nanos"], 40
        )
        self.assertEqual(
            full["median_candidate_net_workload_wall_nanos"], 20
        )
        self.assertEqual(
            full["net_workload_ratio_resolution"], "noise-limited"
        )
        self.assertEqual(full["ratio_threshold_status"], "unresolved")

    def test_null_controls_are_interpolated_by_build_magnitude(self) -> None:
        cheap = sweep.ProbeModule("Probe.Cheap")
        expensive = sweep.ProbeModule("Probe.Expensive")
        effect = sweep.ProbeModule("Probe.Effect")
        pairs = (
            sweep.ProbePair("cheap", cheap, cheap, {}, null_control=True),
            sweep.ProbePair(
                "expensive", expensive, expensive, {}, null_control=True
            ),
            sweep.ProbePair("effect", cheap, effect, {}),
        )
        spec = sweep.SweepSpec(
            description="interpolation",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )

        def rows(wall: int, deltas: list[int]) -> list[dict[str, object]]:
            return [{
                "reference": {"wall_nanos": wall, "peak_rss_kb": None},
                "candidate": {
                    "wall_nanos": wall + delta,
                    "peak_rss_kb": None,
                },
                "signed_wall_delta_nanos": delta,
            } for delta in deltas]

        samples = {
            "cheap": rows(100, [-10, 10]),
            "expensive": rows(300, [-30, 30]),
            "effect": rows(200, [0, 0]),
        }
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(spec, samples)
        self.assertEqual(
            summary["effect"]["comparable_control"],
            ["cheap", "expensive"],
        )
        self.assertEqual(
            summary["effect"]["control_interpolation_weight"], 0.5
        )
        self.assertEqual(
            summary["effect"]["comparable_null_envelope_nanos"], 40
        )

    def test_shared_host_observations_reject_sibling_contention(self) -> None:
        def arm(sibling_busy: float) -> dict[str, object]:
            host = {
                "concurrent_lake_lean_count": 2,
                "load_1m_per_cpu": 0.25,
                "affinity_cpu_frequency_khz": "2500000",
            }
            return {
                "wall_nanos": 1_000_000_000,
                "host_before": host,
                "host_after": host,
                "cpu_accounting": {
                    "measurement_cpu_residual_seconds": 0.01,
                    "measurement_cpu_noninterrupt_residual_seconds": 0.01,
                    "measurement_cpu_foreign_seconds": 0.01,
                    "aggregate_core_interference_seconds":
                        0.01 + sibling_busy,
                    "mean_frequency_khz": 2_500_000,
                    "pressure_some_delta_us": 5,
                    "per_cpu": {
                        "95": {"busy_seconds": sibling_busy},
                    },
                },
            }

        rows = {
            "pair": [{
                "round": 1,
                "reference": arm(0.01),
                "candidate": arm(0.10),
            }]
        }
        observed = sweep.shared_host_observations(
            rows, 47, [95], 0.02, 0.15
        )
        self.assertEqual(observed["max_smt_sibling_busy_ratio"], 0.10)
        self.assertRegex(
            "; ".join(observed["violations"]),
            "aggregate measurement-CPU foreign and SMT-sibling",
        )

    def test_shared_host_observations_reject_missing_frequency(self) -> None:
        host = {
            "concurrent_lake_lean_count": 0,
            "load_1m_per_cpu": 0.0,
            "affinity_cpu_frequency_khz": None,
        }
        arm = {
            "wall_nanos": 1_000_000_000,
            "host_before": host,
            "host_after": host,
            "cpu_accounting": {
                "measurement_cpu_residual_seconds": 0.0,
                "measurement_cpu_noninterrupt_residual_seconds": 0.0,
                "measurement_cpu_foreign_seconds": 0.0,
                "aggregate_core_interference_seconds": 0.0,
                "mean_frequency_khz": None,
                "pressure_some_delta_us": 0,
                "per_cpu": {"95": {"busy_seconds": 0.0}},
            },
        }
        rows = {
            "pair": [{
                "round": 1,
                "reference": arm,
                "candidate": arm,
            }]
        }
        observed = sweep.shared_host_observations(
            rows, 47, [95], 0.02, 0.15
        )
        self.assertEqual(observed["expected_frequency_observations"], 2)
        self.assertEqual(observed["observed_frequency_observations"], 0)
        self.assertRegex(
            "; ".join(observed["violations"]),
            "frequency accounting is incomplete",
        )

    def test_shared_host_observations_reject_impossible_cpu_total(self) -> None:
        host = {
            "concurrent_lake_lean_count": 0,
            "load_1m_per_cpu": 0.0,
            "affinity_cpu_frequency_khz": "2500000",
        }
        arm = {
            "wall_nanos": 1_000_000_000,
            "host_before": host,
            "host_after": host,
            "cpu_accounting": {
                "measurement_cpu_residual_seconds": 0.1,
                "measurement_cpu_interrupt_seconds": 0.6,
                "measurement_cpu_noninterrupt_residual_seconds": -0.5,
                "measurement_cpu_foreign_seconds": 0.0,
                "aggregate_core_interference_seconds": 0.0,
                "mean_frequency_khz": 2_500_000,
                "pressure_some_delta_us": 0,
                "per_cpu": {"95": {"busy_seconds": 0.0}},
            },
        }
        rows = {
            "pair": [{
                "round": 1,
                "reference": arm,
                "candidate": arm,
            }]
        }
        observed = sweep.shared_host_observations(
            rows, 47, [95], 0.02, 0.15
        )
        self.assertRegex(
            "; ".join(observed["violations"]),
            "child CPU time exceeds pinned-CPU busy time",
        )

    def test_shared_host_observations_gate_arm_mean_frequency(self) -> None:
        host = {
            "concurrent_lake_lean_count": 0,
            "load_1m_per_cpu": 0.0,
            "affinity_cpu_frequency_khz": "1500000",
        }

        def arm(mean_frequency: int) -> dict[str, object]:
            return {
                "wall_nanos": 1_000_000_000,
                "cpu_percent": 100.0,
                "host_before": host,
                "host_after": host,
                "cpu_accounting": {
                    "measurement_cpu_residual_seconds": 0.0,
                    "measurement_cpu_noninterrupt_residual_seconds": 0.0,
                    "measurement_cpu_foreign_seconds": 0.0,
                    "aggregate_core_interference_seconds": 0.0,
                    "mean_frequency_khz": mean_frequency,
                    "pressure_some_delta_us": 0,
                    "per_cpu": {"95": {"busy_seconds": 0.0}},
                },
            }

        rows = {
            "pair": [{
                "round": 1,
                "reference": arm(2_000_000),
                "candidate": arm(2_500_000),
            }]
        }
        observed = sweep.shared_host_observations(
            rows, 47, [95], 0.002, 0.15
        )
        self.assertAlmostEqual(observed["frequency_spread_ratio"], 0.25)
        self.assertRegex(
            "; ".join(observed["violations"]),
            "pinned-CPU frequency spread",
        )

    def test_nonshared_sweep_does_not_require_null_controls(self) -> None:
        args = sweep.parse_args("validity", [])
        quality, issues = sweep.validity_summary(
            SPEC,
            args,
            {"center-direct": {"resolution": "no-comparable-control"}},
            None,
            [],
        )
        self.assertTrue(quality)
        self.assertEqual(issues, [])

    def test_shared_sweep_requires_measured_control_separation(self) -> None:
        module = sweep.ProbeModule("Probe.Baseline")
        pairs = (
            sweep.ProbePair("cheap", module, module, {}, null_control=True),
            sweep.ProbePair(
                "expensive", module, module, {}, null_control=True
            ),
            sweep.ProbePair("effect", module, module, {}),
        )
        spec = sweep.SweepSpec(
            description="control magnitudes",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        args = sweep.parse_args(
            "validity",
            [
                "--shared-host", "--expected-host", "bench",
                "--cpu", "22", "--samples", "6",
            ],
        )
        results = {
            "cheap": {"build_magnitude_wall_nanos": 1_000},
            "expensive": {"build_magnitude_wall_nanos": 1_500},
            "effect": {
                "build_magnitude_wall_nanos": 1_250,
                "resolution": "resolved",
            },
        }
        quality, issues = sweep.validity_summary(
            spec, args, results, {"violations": []}, []
        )
        self.assertFalse(quality)
        self.assertIn(
            "null-control build magnitudes are not sufficiently distinct",
            issues,
        )

    def test_shared_budget_must_exceed_interference_ceiling(self) -> None:
        module = sweep.ProbeModule("Probe.Baseline")
        pairs = (
            sweep.ProbePair("cheap", module, module, {}, null_control=True),
            sweep.ProbePair(
                "expensive", module, module, {}, null_control=True
            ),
            sweep.ProbePair(
                "tactic",
                module,
                module,
                {"tactic_budget_ms": 100},
            ),
        )
        spec = sweep.SweepSpec(
            description="budget resolution",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        args = sweep.parse_args(
            "validity",
            [
                "--shared-host", "--expected-host", "bench",
                "--cpu", "22", "--samples", "6",
            ],
        )
        arm = {"wall_nanos": 30_000_000_000}
        results = {
            "cheap": {"build_magnitude_wall_nanos": 10_000_000_000},
            "expensive": {"build_magnitude_wall_nanos": 30_000_000_000},
            "tactic": {
                "build_magnitude_wall_nanos": 30_000_000_000,
                "resolution": "resolved",
                "budget_nanos": 100_000_000,
                "budget_status": "passed",
                "samples": [
                    {"reference": arm, "candidate": arm}
                ],
            },
        }
        quality, issues = sweep.validity_summary(
            spec, args, results, {"violations": []}, []
        )
        self.assertFalse(quality)
        self.assertGreater(
            results["tactic"]["budget_interference_ceiling_nanos"],
            results["tactic"]["budget_nanos"],
        )
        self.assertRegex(
            "; ".join(issues),
            "not resolvable under the admitted core-interference ceiling",
        )

    def test_contention_violation_makes_release_quality_false(self) -> None:
        args = sweep.parse_args("validity", [])
        observations = {"violations": ["sibling contention"]}
        quality, issues = sweep.validity_summary(
            SPEC,
            args,
            {"center-direct": {}},
            observations,
            [],
        )
        self.assertFalse(quality)
        self.assertEqual(issues, ["sibling contention"])

    def test_excessive_robust_null_spread_invalidates_record(self) -> None:
        module = sweep.ProbeModule("Probe.Baseline")
        candidate = sweep.ProbeModule("Probe.Candidate")
        pairs = (
            sweep.ProbePair(
                "null", module, module, {}, null_control=True
            ),
            sweep.ProbePair("effect", module, candidate, {}),
        )
        spec = sweep.SweepSpec(
            description="null spread",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        results = {
            "null": {
                "build_magnitude_wall_nanos": 1_000,
                "null_robust_spread_ratio": 0.11,
            },
            "effect": {"resolution": "resolved"},
        }
        quality, issues = sweep.validity_summary(
            spec, sweep.parse_args("validity", []), results, None, []
        )
        self.assertFalse(quality)
        self.assertRegex("; ".join(issues), "robust null IQR/build ratio")


class HarnessValidationTests(unittest.TestCase):
    def test_shared_host_arguments_are_complete_and_exclusive(self) -> None:
        with mock.patch.object(sys, "stderr", new=io.StringIO()):
            with self.assertRaises(SystemExit):
                sweep.parse_args("shared", ["--shared-host"])
            with self.assertRaises(SystemExit):
                sweep.parse_args(
                    "shared", ["--expected-host", "bench-host", "--cpu", "3"]
                )
            with self.assertRaises(SystemExit):
                sweep.parse_args(
                    "shared",
                    [
                        "--shared-host", "--expected-host", "bench-host",
                        "--cpu", "3", "--allow-busy",
                    ],
                )

    def test_pair_retry_default_and_hard_cap_are_distinct(self) -> None:
        self.assertEqual(
            sweep.parse_args("shared", []).max_pair_retries, 8
        )
        self.assertEqual(
            sweep.parse_args(
                "shared", ["--max-pair-retries", "32"]
            ).max_pair_retries,
            32,
        )
        self.assertEqual(
            sweep.parse_args(
                "shared", ["--max-arm-retries", "32"]
            ).max_pair_retries,
            32,
        )
        with mock.patch.object(sys, "stderr", new=io.StringIO()):
            with self.assertRaises(SystemExit):
                sweep.parse_args(
                    "shared", ["--max-pair-retries", "33"]
                )
            with self.assertRaises(SystemExit):
                sweep.parse_args(
                    "shared", ["--max-arm-retries", "33"]
                )
            with self.assertRaises(SystemExit):
                sweep.parse_args(
                    "shared", ["--max-pair-retries", "-1"]
                )

    def test_suite_preregisters_exact_shared_host_retry_bound(self) -> None:
        spec = dataclasses.replace(SPEC, max_pair_retries=32)
        with mock.patch.object(sweep, "configure_shared_host"):
            with self.assertRaisesRegex(
                RuntimeError,
                "requires --max-pair-retries 32, got 8",
            ):
                sweep.run_cli(
                    spec,
                    CALLER,
                    [
                        "--samples", "6",
                        "--shared-host",
                        "--expected-host", "chungus2",
                        "--cpu", "22",
                    ],
                )

    def test_exhausted_pair_emits_unsummarized_partial_artifact(self) -> None:
        rejected = [{
            "attempt": 1,
            "issues": ["synthetic aggregate interference"],
            "reference": {"wall_nanos": 1},
            "candidate": {"wall_nanos": 2},
        }]
        env = {
            "repository": {"state_sha256": "stable"},
            "dependency_checkouts": {},
            "host_before": {},
            "git_commit": "deadbeef",
            "hostname": "chungus2",
        }
        topology = {"thread_siblings_list": "22,70"}
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "partial.json"
            with mock.patch.object(sweep, "validate_spec"), \
                    mock.patch.object(sweep, "configure_shared_host"), \
                    mock.patch.object(
                        sweep, "shared_host_protocol_issues", return_value=[]
                    ), mock.patch.object(
                        sweep, "environment", return_value=env
                    ), mock.patch.object(
                        sweep, "dirty_issues", return_value=[]
                    ), mock.patch.object(
                        sweep, "host_issues", return_value=[]
                    ), mock.patch.object(sweep, "warm_imports"), \
                    mock.patch.object(
                        sweep, "source_hashes",
                        return_value={"source": "hash"},
                    ), mock.patch.object(
                        sweep, "cpu_topology", return_value=topology
                    ), mock.patch.object(
                        sweep, "host_state", return_value={}
                    ), mock.patch.object(
                        sweep, "build_shared_host_pair",
                        return_value=(None, rejected, None),
                    ), mock.patch.object(
                        sweep, "checkout_state",
                        return_value={"state_sha256": "stable"},
                    ), mock.patch.object(
                        sweep, "dependency_checkouts", return_value={}
                    ), mock.patch.object(
                        sweep, "summarize"
                    ) as summarize:
                status = sweep.run_cli(
                    SPEC,
                    CALLER,
                    [
                        "--samples", "6",
                        "--shared-host",
                        "--expected-host", "chungus2",
                        "--cpu", "22",
                        "--output", str(output),
                    ],
                )
            record = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(status, 2)
        summarize.assert_not_called()
        self.assertEqual(record["measurement_state"], "incomplete")
        self.assertEqual(record["results"], {})
        self.assertEqual(record["partial_samples"][PAIR.name], [])
        self.assertEqual(len(record["rejected_pair_attempts"]), 1)
        self.assertEqual(record["validity"]["observed"][
            "total_rejected_pair_attempts"
        ], 1)
        self.assertEqual(record["validity"]["observed"][
            "total_exhausted_pairs"
        ], 1)
        self.assertRegex(
            "; ".join(record["validity"]["exceptions"]),
            "exhausted 1 pair attempt",
        )

    def test_shared_host_pins_named_machine(self) -> None:
        args = sweep.parse_args(
            SPEC.description,
            [
                "--shared-host",
                "--expected-host", "bench-host",
                "--cpu", "3",
                "--samples", "6",
            ],
        )
        with mock.patch.object(
            sweep.socket, "gethostname", return_value="bench-host"
        ), mock.patch.object(
            sweep.os, "sched_setaffinity", create=True
        ) as set_affinity:
            sweep.configure_shared_host(args)
        set_affinity.assert_called_once_with(0, {3})

    def test_shared_host_rejects_wrong_machine(self) -> None:
        args = sweep.parse_args(
            SPEC.description,
            [
                "--shared-host",
                "--expected-host", "bench-host",
                "--cpu", "3",
                "--samples", "6",
            ],
        )
        with mock.patch.object(
            sweep.socket, "gethostname", return_value="other-host"
        ):
            with self.assertRaisesRegex(RuntimeError, "expected host"):
                sweep.configure_shared_host(args)

    def test_shared_host_requires_single_cpu_affinity(self) -> None:
        args = sweep.parse_args(
            SPEC.description,
            [
                "--shared-host", "--expected-host", "bench-host",
                "--cpu", "3", "--samples", "6",
            ],
        )
        with mock.patch.object(
            sweep, "cpu_affinity", return_value=[3, 4]
        ):
            self.assertRegex(
                "; ".join(sweep.shared_host_protocol_issues(SPEC, args)),
                "exactly one affinity CPU",
            )

    def test_shared_host_requires_two_controls(self) -> None:
        args = sweep.parse_args(
            SPEC.description,
            [
                "--shared-host", "--expected-host", "bench-host",
                "--cpu", "3", "--samples", "6",
            ],
        )
        with mock.patch.object(sweep, "cpu_affinity", return_value=[3]):
            self.assertRegex(
                "; ".join(sweep.shared_host_protocol_issues(SPEC, args)),
                "at least two same-module null controls",
            )

    def test_shared_host_accepts_balanced_controlled_spec(self) -> None:
        cheap = sweep.ProbeModule("Probe.Cheap")
        expensive = sweep.ProbeModule("Probe.Expensive")
        controls = (
            sweep.ProbePair("cheap", cheap, cheap, {}, null_control=True),
            sweep.ProbePair(
                "expensive", expensive, expensive, {}, null_control=True
            ),
            sweep.ProbePair(
                "substantive",
                cheap,
                sweep.ProbeModule("Probe.Candidate"),
                {},
            ),
        )
        spec = sweep.SweepSpec(
            description="shared",
            pairs=controls,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            required_samples=6,
        )
        args = sweep.parse_args(
            spec.description,
            [
                "--shared-host", "--expected-host", "bench-host",
                "--cpu", "3", "--samples", "6",
            ],
        )
        with mock.patch.object(sweep, "cpu_affinity", return_value=[3]):
            self.assertEqual(sweep.shared_host_protocol_issues(spec, args), [])

    def test_shared_host_requires_controls_before_substantive_pairs(self) -> None:
        cheap = sweep.ProbeModule("Probe.Cheap")
        expensive = sweep.ProbeModule("Probe.Expensive")
        pairs = (
            sweep.ProbePair("cheap", cheap, cheap, {}, null_control=True),
            sweep.ProbePair(
                "substantive",
                cheap,
                sweep.ProbeModule("Probe.Candidate"),
                {},
            ),
            sweep.ProbePair(
                "expensive", expensive, expensive, {}, null_control=True
            ),
        )
        spec = sweep.SweepSpec(
            description="misordered controls",
            pairs=pairs,
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            required_samples=6,
        )
        args = sweep.parse_args(
            spec.description,
            [
                "--shared-host", "--expected-host", "bench-host",
                "--cpu", "3", "--samples", "6",
            ],
        )
        with mock.patch.object(sweep, "cpu_affinity", return_value=[3]):
            self.assertRegex(
                "; ".join(
                    sweep.shared_host_protocol_issues(spec, args)
                ),
                "all null controls must precede substantive pairs",
            )

    def test_shared_host_records_global_activity_without_rejecting_it(self) -> None:
        state = {
            "concurrent_lake_lean": [{"pid": 1, "command": "lake build"}],
            "load_1m_per_cpu": 0.25,
        }
        self.assertEqual(
            sweep.host_issues(
                state, 0.5, concurrent_is_issue=False, load_is_issue=False
            ),
            [],
        )
        state["load_1m_per_cpu"] = 0.75
        self.assertEqual(
            sweep.host_issues(
                state, 0.5, concurrent_is_issue=False, load_is_issue=False
            ),
            [],
        )

    def test_warmup_builds_every_unique_import_closure(self) -> None:
        completed = subprocess.CompletedProcess(
            ["lake", "build"], 0, stdout="", stderr=""
        )
        with mock.patch.object(
            sweep, "run_timed", return_value=(completed, 1, None)
        ) as timed:
            sweep.warm_imports(SPEC, 30)
        command, timeout = timed.call_args.args
        self.assertEqual(timeout, 30)
        self.assertEqual(command[:2], ["lake", "build"])
        self.assertEqual(
            set(command[2:]),
            {
                "+HexIntervalMathlib.CenterBaseline:deps",
                "+HexIntervalMathlib.CenterDirect:deps",
            },
        )

    def test_warmup_timeout_fails_closed(self) -> None:
        with mock.patch.object(
            sweep,
            "run_timed",
            side_effect=subprocess.TimeoutExpired(["lake", "build"], 1),
        ):
            with self.assertRaisesRegex(RuntimeError, "warmup timed out"):
                sweep.warm_imports(SPEC, 1)

    def test_remove_outputs_is_exact_to_selected_module(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            lean_dir = build / "lib" / "lean" / "Probe"
            ir_dir = build / "ir" / "Probe"
            lean_dir.mkdir(parents=True)
            ir_dir.mkdir(parents=True)
            selected = [
                lean_dir / "Measured.olean",
                lean_dir / "Measured.ilean",
                ir_dir / "Measured.c",
            ]
            untouched = lean_dir / "Other.olean"
            for path in [*selected, untouched]:
                path.write_bytes(b"artifact")
            with mock.patch.object(sweep, "BUILD", build):
                sweep.remove_module_outputs("Probe.Measured")
            self.assertTrue(all(not path.exists() for path in selected))
            self.assertTrue(untouched.is_file())

    def test_duplicate_pair_names_fail_closed(self) -> None:
        spec = sweep.SweepSpec(
            description="duplicate",
            pairs=(PAIR, PAIR),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        with self.assertRaisesRegex(RuntimeError, "must be unique"):
            sweep.validate_spec(spec)

    def test_ordinary_identical_pair_fails_closed(self) -> None:
        module = sweep.ProbeModule("Probe.Same")
        spec = sweep.SweepSpec(
            description="ordinary identical",
            pairs=(sweep.ProbePair("same", module, module, {}),),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        with self.assertRaisesRegex(RuntimeError, "are identical"):
            sweep.validate_spec(spec)

    def test_null_control_requires_identical_modules(self) -> None:
        pair = sweep.ProbePair(
            "null",
            sweep.ProbeModule("Probe.Reference"),
            sweep.ProbeModule("Probe.Candidate"),
            {},
            null_control=True,
        )
        spec = sweep.SweepSpec(
            description="invalid null",
            pairs=(pair,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        with self.assertRaisesRegex(RuntimeError, "must be identical"):
            sweep.validate_spec(spec)

    def test_null_control_requires_identical_axiom_policies(self) -> None:
        pair = sweep.ProbePair(
            "null",
            sweep.ProbeModule("Probe.Same"),
            sweep.ProbeModule("Probe.Same", EXPECTED_AXIOMS),
            {},
            null_control=True,
        )
        spec = sweep.SweepSpec(
            description="invalid null policy",
            pairs=(pair,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        with self.assertRaisesRegex(RuntimeError, "axiom policies"):
            sweep.validate_spec(spec)

    def test_same_module_null_control_is_valid(self) -> None:
        module = sweep.ProbeModule("Probe.Same")
        pair = sweep.ProbePair("null", module, module, {}, null_control=True)
        spec = sweep.SweepSpec(
            description="valid null",
            pairs=(pair,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        source = Path("/unused/Probe/Same.lean")
        with mock.patch.object(sweep, "probe_source", return_value=source), \
                mock.patch.object(Path, "is_file", return_value=True), \
                mock.patch.object(sweep, "_parse_imports", return_value=[]):
            sweep.validate_spec(spec)

    def test_required_sample_count_is_enforced_before_warmup(self) -> None:
        spec = sweep.SweepSpec(
            description="required samples",
            pairs=(PAIR,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
            required_samples=6,
        )
        with mock.patch.object(sweep, "validate_spec"):
            with self.assertRaisesRegex(RuntimeError, "requires --samples 6"):
                sweep.run_cli(spec, CALLER, ["--samples", "4"])

    def test_every_sweep_requires_even_sample_count(self) -> None:
        module = sweep.ProbeModule("Probe.Same")
        pair = sweep.ProbePair(
            "ordinary",
            module,
            sweep.ProbeModule("Probe.Other"),
            {},
        )
        spec = sweep.SweepSpec(
            description="balanced",
            pairs=(pair,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        with mock.patch.object(sweep, "validate_spec"):
            with self.assertRaisesRegex(RuntimeError, "even --samples"):
                sweep.run_cli(spec, CALLER, ["--samples", "5"])

    def test_transitive_measured_module_import_fails_closed(self) -> None:
        pair = sweep.ProbePair(
            name="bad-import",
            reference=sweep.ProbeModule("Probe.Reference"),
            candidate=sweep.ProbeModule("Probe.Candidate"),
            metadata={},
        )
        spec = sweep.SweepSpec(
            description="bad import",
            pairs=(pair,),
            probe_target="Probe",
            schema="test",
            measurement="test",
            output_stem="test",
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {
                "Probe.Reference": root / "Reference.lean",
                "Probe.Candidate": root / "Candidate.lean",
                "Probe.Support": root / "Support.lean",
            }
            for source in sources.values():
                source.write_text("module\n", encoding="utf-8")

            def source_for(module: str, _src_dir: Path) -> Path:
                return sources[module]

            def imports_for(path: Path) -> list[str]:
                if path == sources["Probe.Reference"]:
                    return ["Probe.Support"]
                if path == sources["Probe.Support"]:
                    return ["Probe.Candidate"]
                return []

            def resolve_module(
                module: str, _target: object, _root: Path
            ) -> Path | None:
                return sources.get(module)

            with mock.patch.object(
                sweep, "probe_source", side_effect=source_for
            ), mock.patch.object(
                sweep, "_parse_imports", side_effect=imports_for
            ), mock.patch.object(
                sweep, "_resolve_module", side_effect=resolve_module
            ):
                with self.assertRaisesRegex(RuntimeError, "reaches measured probe"):
                    sweep.validate_spec(spec)


if __name__ == "__main__":
    unittest.main()
