#!/usr/bin/env python3
"""Regression tests for release-wide toolchain and dependency synchronization."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

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

    def test_reservoir_toml_pin_rewrites_by_package_name(self) -> None:
        (self.repo / "lakefile.toml").write_text(
            'name = "consumer"\n'
            '\n'
            '[[require]]\n'
            'name = "mathlib"\n'
            'scope = "leanprover-community"\n'
            'rev = "v4.32.0-rc1-patch1"\n'
            '\n'
            '[[require]]\n'
            'rev = "v4.32.0-rc1"\n'
            'git = "https://github.com/leanprover/verso.git"\n'
            'name = "verso"\n'
            '\n'
            '[[lean_lib]]\n'
            'name = "Consumer"\n',
            encoding="utf-8",
        )
        notes = sync_released.rewrite_external_pins(self.repo, self.pins)
        rewritten = (self.repo / "lakefile.toml").read_text()
        self.assertIn(f'rev = "{self.mathlib["inputRev"]}"', rewritten)
        self.assertIn(f'rev = "{self.verso["inputRev"]}"', rewritten)
        self.assertEqual(len(notes), 2)

    def test_external_toml_requirement_without_rev_fails_closed(self) -> None:
        (self.repo / "lakefile.toml").write_text(
            '[[require]]\n'
            'name = "mathlib"\n'
            'scope = "leanprover-community"\n',
            encoding="utf-8",
        )
        with self.assertRaisesRegex(RuntimeError, "has no rev"):
            sync_released.rewrite_external_pins(self.repo, self.pins)

    def test_release_skeleton_checks_build_roots(self) -> None:
        (self.repo / "lakefile.lean").write_text(
            "import Lake\n"
            "lean_lib ConsumerTests where\n"
            "  globs := #[`Consumer.Tests]\n"
            "lean_lib ConsumerModules where\n"
            "  globs := #[`Consumer.All]\n"
            "lean_exe consumer_check where\n"
            "  root := `Consumer.Check\n"
            "lean_exe unrelated where\n"
            "  root := `Consumer.Other\n",
            encoding="utf-8",
        )
        entry = {
            "lakefile": "lean",
            "test_modules": ["Consumer.Tests"],
            "build_modules": ["Consumer.All"],
            "executables": {"consumer_check": "Consumer.Check"},
        }
        sync_released.validate_skeleton(entry, self.repo)

        entry["executables"]["consumer_check"] = "Consumer.Other"
        with self.assertRaisesRegex(RuntimeError, "must define executable"):
            sync_released.validate_skeleton(entry, self.repo)

    def test_release_skeleton_requires_declared_lake_format(self) -> None:
        (self.repo / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "lakefile.toml"):
            sync_released.validate_skeleton({"lakefile": "toml"}, self.repo)

    def test_release_skeleton_checks_module_precompilation(self) -> None:
        lakefile = self.repo / "lakefile.toml"
        lakefile.write_text(
            '[[lean_lib]]\nname = "Consumer"\n',
            encoding="utf-8",
        )
        entry = {"lakefile": "toml", "precompile_modules": True}
        with self.assertRaisesRegex(RuntimeError, "must precompile modules"):
            sync_released.validate_skeleton(entry, self.repo)
        lakefile.write_text(
            '[[lean_lib]]\nname = "Consumer"\nprecompileModules = true\n',
            encoding="utf-8",
        )
        sync_released.validate_skeleton(entry, self.repo)

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

    def test_failed_publication_persists_already_pushed_heads(self) -> None:
        manifest = self.repo / "released.yml"
        manifest.write_text(
            "repos:\n"
            "  - repo: leanprover/first\n"
            "  - repo: leanprover/second\n",
            encoding="utf-8",
        )
        baseline = self.repo / "baseline.json"
        baseline.write_text(
            json.dumps({"first": "old-first", "second": "old-second"}),
            encoding="utf-8",
        )

        def publish(entry, _source_sha, _token, _dry_run, synced,
                    _baseline, _force, _dep_owner, _pins):
            if entry["repo"].endswith("/first"):
                synced["first"] = "new-first"
                return True
            raise RuntimeError("second mirror failed")

        argv = [
            "sync_released.py",
            "--token",
            "secret-token",
            "--baseline",
            str(baseline),
        ]
        with (
            patch.object(sync_released, "MANIFEST", manifest),
            patch.object(sync_released, "external_pins", return_value={}),
            patch.object(sync_released, "run", return_value="source-sha"),
            patch.object(sync_released, "sync_repo", side_effect=publish),
            patch("sys.argv", argv),
        ):
            self.assertEqual(sync_released.main(), 1)

        advanced = json.loads(baseline.read_text(encoding="utf-8"))
        self.assertEqual(advanced["first"], "new-first")
        self.assertEqual(advanced["second"], "old-second")


if __name__ == "__main__":
    unittest.main()
