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
    check_build_settings,
    check_ci_workflows,
    check_keep_paths,
    check_library_only,
    check_phase_admission,
    parse_sync_baseline,
    published_import_closure_violations,
    published_repositories,
)


class LibraryOnlyTests(unittest.TestCase):
    def test_library_entry_is_accepted(self) -> None:
        check_library_only({"repo": "leanprover/hex-example", "lib": "HexExample"})

    def test_bench_and_oracle_fields_are_rejected(self) -> None:
        for field, value in (("bench", True), ("conformance", True),
                             ("fixtures", ["HexExample"]), ("oracles", ["e.py"])):
            with self.subTest(field=field):
                with self.assertRaisesRegex(ValueError, "stay in hex-dev"):
                    check_library_only(
                        {"repo": "leanprover/hex-example", field: value}
                    )

    def test_remove_paths_is_retired(self) -> None:
        with self.assertRaisesRegex(ValueError, "remove_paths is retired"):
            check_library_only(
                {"repo": "leanprover/hex-example", "remove_paths": ["bench"]}
            )


class KeepPathsTests(unittest.TestCase):
    def test_mirror_local_file_is_accepted(self) -> None:
        check_keep_paths(
            {"repo": "leanprover/hex-test-kit", "keep_paths": ["HexTestKit.lean"]}
        )

    def test_unpublished_trees_are_rejected(self) -> None:
        for path in ("bench", "conformance/HexExample",
                     "conformance-fixtures", "scripts/oracle/example.py",
                     "reports/hex-example-performance.md",
                     "reports/figures/hex-example.svg",
                     ".claude/CLAUDE.md", ".github/workflows/bench.yml"):
            with self.subTest(path=path):
                with self.assertRaisesRegex(ValueError, "stay in hex-dev"):
                    check_keep_paths(
                        {"repo": "leanprover/hex-example", "keep_paths": [path]}
                    )

    def test_skeleton_paths_are_rejected_as_redundant(self) -> None:
        for path in ("LICENSE", "lean-toolchain"):
            with self.subTest(path=path):
                with self.assertRaisesRegex(ValueError, "unmanaged skeleton"):
                    check_keep_paths(
                        {"repo": "leanprover/hex-example", "keep_paths": [path]}
                    )


class BuildSettingTests(unittest.TestCase):
    """The mirror's build settings are derived from lakefile.lean, not declared."""

    def test_a_released_library_is_accepted(self) -> None:
        check_build_settings({"repo": "leanprover/hex-lll", "lib": "HexLLL"})

    def test_a_declared_precompile_flag_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "drop the key"):
            check_build_settings({
                "repo": "leanprover/hex-lll",
                "lib": "HexLLL",
                "precompile_modules": True,
            })

    def test_a_library_absent_from_the_lakefile_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "declares no lean_lib HexGone"):
            check_build_settings({"repo": "leanprover/hex-gone", "lib": "HexGone"})


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
    @staticmethod
    def workflow() -> str:
        from scripts.release.sync_released import released_ci_workflows

        return released_ci_workflows()["hex-basic"]

    def check(self, workflow: str) -> None:
        entries = [{"repo": "leanprover/hex-example"}]
        with patch(
            "scripts.release.check_released_manifest.released_ci_workflows",
            return_value={"hex-example": workflow},
        ):
            check_ci_workflows(entries)

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

    def test_complete_workflow_is_accepted(self) -> None:
        self.check(self.workflow())

    def test_restore_and_save_paths_must_match(self) -> None:
        workflow = self.workflow()
        marker = "            .lake/packages/Hex*/.lake/build\n"
        head, tail = workflow.rsplit(marker, 1)
        with self.assertRaisesRegex(ValueError, "run-unique save key"):
            self.check(
                head + "            .lake/packages/HexOther/.lake/build\n" + tail
            )

    def test_restore_prefix_must_match_unique_key(self) -> None:
        workflow = self.workflow().replace(
            "restore-keys: |\n            lake-build-",
            "restore-keys: |\n            wrong-build-",
            1,
        )
        with self.assertRaisesRegex(ValueError, "run-unique save key"):
            self.check(workflow)

    def test_main_run_must_not_be_cancelled(self) -> None:
        workflow = self.workflow().replace(
            "cancel-in-progress: ${{ github.ref != 'refs/heads/main' }}",
            "cancel-in-progress: true",
            1,
        )
        with self.assertRaisesRegex(ValueError, "terminal cache save"):
            self.check(workflow)

    def test_main_push_trigger_is_required(self) -> None:
        workflow = self.workflow().replace("branches: [main]", "branches: [dev]", 1)
        with self.assertRaisesRegex(ValueError, "main pushes"):
            self.check(workflow)


if __name__ == "__main__":
    unittest.main()


class MathlibOnlyRowTests(unittest.TestCase):
    """A Mathlib-facing library with no computational half takes the Mathlib column."""

    def test_mathlib_only_entry_links_in_the_mathlib_column(self) -> None:
        from scripts.release import aggregate_readme

        manifest = {
            "repos": [
                {"repo": "leanprover/hex-foo", "lib": "HexFoo", "component": "Foo", "pins": []},
                {"repo": "leanprover/hex-foo-mathlib", "lib": "HexFooMathlib", "pins": ["hex-foo"]},
                {
                    "repo": "leanprover/hex-tac",
                    "lib": "HexTac",
                    "component": "A tactic",
                    "mathlib_only": True,
                    "pins": [],
                },
                {"repo": "leanprover/hex", "pins_only": True, "pins": ["hex-foo", "hex-foo-mathlib", "hex-tac"]},
            ]
        }
        table = aggregate_readme.render_table(manifest)
        self.assertIn(
            "| Foo | [HexFoo](https://github.com/leanprover/hex-foo) | "
            "[HexFooMathlib](https://github.com/leanprover/hex-foo-mathlib) |",
            table,
        )
        self.assertIn(
            "| A tactic | n/a | [HexTac](https://github.com/leanprover/hex-tac) |",
            table,
        )

class PublishedImportClosureTests(unittest.TestCase):
    """A released umbrella may reach only published libraries."""

    def _write(self, root: Path, module: str, imports: list[str]) -> None:
        path = root / Path(*module.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        lines = ["module", ""] + [f"public import {name}" for name in imports]
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def test_umbrella_reaching_unpublished_library_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write(root, "HexBasic", [])
            self._write(root, "HexFoo", ["HexBasic", "HexFoo.Kernel"])
            self._write(root, "HexFoo.Kernel", ["HexPhantom.Fast"])
            self._write(root, "HexPhantom.Fast", [])
            entries = [
                {"repo": "leanprover/hex-basic", "lib": "HexBasic", "pins": []},
                {"repo": "leanprover/hex-foo", "lib": "HexFoo", "pins": ["hex-basic"]},
            ]
            violations = published_import_closure_violations(entries, root)
            self.assertEqual(
                violations,
                [
                    "leanprover/hex-foo: HexFoo.Kernel imports HexPhantom.Fast, "
                    "whose library HexPhantom is not in released.yml"
                ],
            )

    def test_extra_paths_root_and_test_kit_are_allowed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write(root, "HexBasic", [])
            self._write(root, "HexGraph", ["HexBasic"])
            self._write(root, "HexFoo", ["HexBasic", "HexGraph", "Hex.BenchKit"])
            self._write(root, "HexFoo.Tests", ["HexFoo"])
            entries = [
                {"repo": "leanprover/hex-basic", "lib": "HexBasic", "pins": []},
                {
                    "repo": "leanprover/hex-foo",
                    "lib": "HexFoo",
                    "pins": ["hex-basic"],
                    "test_modules": ["HexFoo.Tests"],
                    "extra_paths": [{"src": "HexGraph", "dest": "HexGraph"}],
                },
            ]
            self.assertEqual(published_import_closure_violations(entries, root), [])

    def test_pinned_upstream_extra_root_is_allowed_downstream(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self._write(root, "HexGraph", [])
            self._write(root, "HexFoo", ["HexGraph"])
            self._write(root, "HexFooMathlib", ["HexFoo", "HexGraph.Basic"])
            entries = [
                {
                    "repo": "leanprover/hex-foo",
                    "lib": "HexFoo",
                    "pins": [],
                    "extra_paths": [{"src": "HexGraph", "dest": "HexGraph"}],
                },
                {"repo": "leanprover/hex-foo-mathlib", "lib": "HexFooMathlib", "pins": ["hex-foo"]},
            ]
            self.assertEqual(published_import_closure_violations(entries, root), [])
