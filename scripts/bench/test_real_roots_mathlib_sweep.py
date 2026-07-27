#!/usr/bin/env python3
"""Regression tests for the isolate_roots fresh-module sweep."""

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

from scripts.bench import real_roots_mathlib_sweep as sweep


class ProvenanceTests(unittest.TestCase):
    def test_transitive_local_sources_are_included(self) -> None:
        sources = set(sweep.provenance_sources())
        self.assertIn(sweep.ROOT / "HexPoly" / "Dense.lean", sources)
        self.assertIn(sweep.ROOT / "HexHensel" / "Basic.lean", sources)
        self.assertIn(
            sweep.ROOT / "HexModArithMathlib" / "Basic.lean", sources
        )

    def test_source_hash_changes_with_source_content(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Transitive.lean"
            source.write_text("def value := 1\n", encoding="utf-8")
            with mock.patch.object(sweep, "ROOT", root), mock.patch.object(
                sweep, "provenance_sources", return_value=[source]
            ):
                before = sweep.source_hashes()
                source.write_text("def value := 2\n", encoding="utf-8")
                after = sweep.source_hashes()
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
    def test_summary_uses_each_arms_adjacent_baseline(self) -> None:
        rows: dict[str, list[dict[str, object]]] = {
            key: [] for key in sweep.CASES
        }
        rows["baseline"] = [
            {"wall_nanos": 10, "peak_rss_kb": None, "axioms": None},
            {"wall_nanos": 100, "peak_rss_kb": None, "axioms": None},
        ]
        for key in rows:
            if key == "baseline":
                continue
            rows[key] = [{
                "wall_nanos": 125,
                "peak_rss_kb": None,
                "axioms": sweep.EXPECTED_AXIOMS,
                "adjacent_baseline_wall_nanos": 100,
                "adjacent_baseline_peak_rss_kb": None,
            }]
        with mock.patch.object(sweep, "artifact_sizes", return_value={}):
            summary = sweep.summarize(rows)
        self.assertEqual(
            summary["natural-6"]["signed_baseline_wall_margin_nanos"], [25]
        )


if __name__ == "__main__":
    unittest.main()
