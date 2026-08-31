#!/usr/bin/env python3
"""Tests for release-manifest Phase-7 admission and rollback."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path
from types import SimpleNamespace

from scripts.release.check_released_manifest import (
    check_ci_workflows,
    check_phase_admission,
    parse_sync_baseline,
    published_repositories,
)


class Phase7AdmissionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self.temporary.name)
        self.git_env = {
            **os.environ,
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_CONFIG_NOSYSTEM": "1",
        }
        self._git("init", "-q")
        (self.repo / "synced.json").write_text(
            json.dumps({"hex-example": "a" * 40}), encoding="utf-8"
        )
        self._git("add", "synced.json")
        self._git(
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.com",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "baseline",
        )
        self._git(
            "update-ref", "refs/remotes/origin/release-sync-baseline", "HEAD"
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _git(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", "-C", str(self.repo), *args],
            check=True,
            capture_output=True,
            text=True,
            env=self.git_env,
        )

    @staticmethod
    def entry() -> dict:
        return {"repo": "leanprover/hex-example", "lib": "HexExample"}

    def test_live_baseline_records_published_repository(self) -> None:
        self.assertEqual(published_repositories(self.repo), {"hex-example"})

    def test_published_repository_may_roll_back(self) -> None:
        check_phase_admission(
            [self.entry()],
            {"HexExample": SimpleNamespace(done_through=3)},
            {"hex-example"},
        )

    def test_unpublished_repository_cannot_enter_below_phase7(self) -> None:
        with self.assertRaisesRegex(ValueError, "new released.yml entry requires"):
            check_phase_admission(
                [self.entry()],
                {"HexExample": SimpleNamespace(done_through=3)},
                set(),
            )

    def test_unpublished_repository_may_enter_at_phase7(self) -> None:
        check_phase_admission(
            [self.entry()],
            {"HexExample": SimpleNamespace(done_through=7)},
            set(),
        )

    def test_malformed_baseline_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "malformed baseline entry"):
            parse_sync_baseline('{"hex-example": "short"}', "test baseline")


class ReleasedCiTests(unittest.TestCase):
    def test_workflow_set_must_match_manifest(self) -> None:
        entries = [{"repo": "leanprover/hex-example"}]
        with (
            patch(
                "scripts.release.check_released_manifest.released_ci_workflows",
                return_value={"hex-other": "name: CI\n"},
            ),
            self.assertRaisesRegex(ValueError, "differs from the release manifest"),
        ):
            check_ci_workflows(entries)


if __name__ == "__main__":
    unittest.main()
