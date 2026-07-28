#!/usr/bin/env python3
"""Regression tests for the reusable matched fresh-module harness."""

from __future__ import annotations

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


class ProcessGroupTests(unittest.TestCase):
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


class HarnessValidationTests(unittest.TestCase):
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
