#!/usr/bin/env python3
"""Regression tests for the reusable matched fresh-module harness."""

from __future__ import annotations

import io
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
                    "measurement_cpu_foreign_seconds": 0.01,
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
            "; ".join(observed["violations"]), "SMT sibling CPU 95"
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
