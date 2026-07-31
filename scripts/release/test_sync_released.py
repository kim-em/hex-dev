#!/usr/bin/env python3
"""Regression tests for release-wide toolchain and dependency synchronization."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.release import sync_released


class SyncReleasedTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self.temporary.name)
        (self.repo / "lean-toolchain").write_text(
            "leanprover/lean4:v4.32.0-rc1\n", encoding="utf-8")
        (self.repo / "bench").mkdir()
        (self.repo / "bench" / "lean-toolchain").write_text(
            "leanprover/lean4:v4.32.0-rc1\n", encoding="utf-8")
        self.pins = sync_released.external_pins()
        self.mathlib = self.pins[
            sync_released._git_url(
                "https://github.com/leanprover-community/mathlib4.git")]
        self.verso = self.pins[
            sync_released._git_url("https://github.com/leanprover/verso.git")]

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_toolchain_reaches_side_projects(self) -> None:
        notes = sync_released.rewrite_toolchains(self.repo)
        expected = sync_released.TOOLCHAIN.read_text(encoding="utf-8")
        self.assertEqual((self.repo / "lean-toolchain").read_text(), expected)
        self.assertEqual(
            (self.repo / "bench" / "lean-toolchain").read_text(), expected)
        self.assertEqual(len(notes), 2)

    def test_direct_pins_rewrite_toml_and_lean(self) -> None:
        (self.repo / "lakefile.toml").write_text(
            '[[require]]\n'
            'name = "mathlib"\n'
            'git = "https://github.com/leanprover-community/mathlib4.git"\n'
            'rev = "v4.32.0-rc1-patch1"\n',
            encoding="utf-8",
        )
        (self.repo / "bench" / "lakefile.lean").write_text(
            'require verso from git\n'
            '  "https://github.com/leanprover/verso.git" @ "v4.32.0-rc1"\n',
            encoding="utf-8",
        )
        sync_released.rewrite_external_pins(self.repo, self.pins)
        self.assertIn(
            f'rev = "{self.mathlib["inputRev"]}"',
            (self.repo / "lakefile.toml").read_text(),
        )
        self.assertIn(
            f'@ "{self.verso["inputRev"]}"',
            (self.repo / "bench" / "lakefile.lean").read_text(),
        )

    def test_manifest_uses_exact_external_commit(self) -> None:
        manifest = {
            "version": "1.1.0",
            "packages": [{
                "name": "mathlib",
                "url": "https://github.com/leanprover-community/mathlib4.git",
                "rev": "old",
                "inputRev": "v4.32.0-rc1-patch1",
            }],
        }
        path = self.repo / "lake-manifest.json"
        path.write_text(json.dumps(manifest), encoding="utf-8")
        sync_released.rewrite_manifest(
            {}, self.repo, {}, {}, self.pins)
        package = json.loads(path.read_text())["packages"][0]
        self.assertEqual(package["rev"], self.mathlib["rev"])
        self.assertEqual(package["inputRev"], self.mathlib["inputRev"])

    def test_missing_root_toolchain_fails_closed(self) -> None:
        (self.repo / "lean-toolchain").unlink()
        with self.assertRaisesRegex(RuntimeError, "no root lean-toolchain"):
            sync_released.rewrite_toolchains(self.repo)


if __name__ == "__main__":
    unittest.main()
