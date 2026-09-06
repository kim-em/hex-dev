#!/usr/bin/env python3
"""Regression tests for release-wide toolchain and dependency synchronization."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import yaml

from scripts.release import aggregate_readme, sync_released


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

    def _bridge_clone(self) -> Path:
        """A mirror carrying the skeleton, its library, and stale extras."""
        clone = self.repo / "clone"
        (clone / "HexBridge").mkdir(parents=True)
        (clone / "HexBridge" / "Basic.lean").write_text("--\n", encoding="utf-8")
        for name in ("LICENSE", "AGENTS.md", ".gitignore", "README.md",
                     "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            (clone / name).write_text("skeleton\n", encoding="utf-8")
        (clone / ".github" / "workflows").mkdir(parents=True)
        (clone / ".github" / "workflows" / "ci.yml").write_text(
            "name: CI\n", encoding="utf-8")
        (clone / ".github" / "workflows" / "bench.yml").write_text(
            "name: bench\n", encoding="utf-8")
        (clone / ".github" / "dependabot.yml").write_text(
            "version: 2\n", encoding="utf-8")
        (clone / ".claude").mkdir()
        (clone / ".claude" / "CLAUDE.md").write_text("notes\n", encoding="utf-8")
        (clone / "reports" / "bench-results").mkdir(parents=True)
        (clone / "reports" / "bench-results" / "run.json").write_text(
            "{}\n", encoding="utf-8")
        (clone / "reports" / "hex-bridge-performance.md").write_text(
            "report\n", encoding="utf-8")
        for stale in ("bench/HexBridge", "conformance/HexBridge",
                      "conformance-fixtures/HexBridge", "scripts/oracle"):
            (clone / stale).mkdir(parents=True)
            (clone / stale / "file").write_text("stale\n", encoding="utf-8")
        (clone / "conformance" / "lakefile.toml").write_text(
            "name = \"conformance\"\n", encoding="utf-8")
        (clone / "SPEC").mkdir()
        (clone / "SPEC" / "hex-bridge.md").write_text("spec\n", encoding="utf-8")
        (clone / "SPEC" / "obsolete.md").write_text("stale\n", encoding="utf-8")
        return clone

    def _bridge_entry(self) -> dict:
        return {
            "repo": "leanprover/hex-bridge",
            "lib": "HexBridge",
            "readme": False,
            "umbrella": False,
            "spec": "hex-bridge",
        }

    def test_prune_removes_everything_outside_the_allowance(self) -> None:
        clone = self._bridge_clone()
        with tempfile.TemporaryDirectory() as source_directory:
            source = Path(source_directory)
            with patch.object(sync_released, "REPO_ROOT", source):
                notes = sync_released.prune_unmanaged(self._bridge_entry(), clone)
        for gone in ("bench", "conformance", "conformance-fixtures", "scripts",
                     "SPEC/obsolete.md", ".claude", "reports",
                     ".github/workflows/bench.yml", ".github/dependabot.yml"):
            self.assertFalse((clone / gone).exists(), gone)
            self.assertIn(f"  remove {gone}", notes)
        for kept in ("HexBridge/Basic.lean", "SPEC/hex-bridge.md", "LICENSE",
                     "AGENTS.md", ".gitignore", "README.md", "lakefile.toml",
                     "lake-manifest.json", "lean-toolchain",
                     ".github/workflows/ci.yml"):
            self.assertTrue((clone / kept).exists(), kept)

    def test_prune_keeps_only_the_figures_the_entry_publishes(self) -> None:
        """`reports/` goes, except the figures the manifest names."""
        clone = self.repo / "clone"
        (clone / "reports" / "figures").mkdir(parents=True)
        (clone / "reports" / "figures" / "hex-bridge-scaling.svg").write_text(
            "<svg/>", encoding="utf-8")
        (clone / "reports" / "figures" / "stale.svg").write_text(
            "<svg/>", encoding="utf-8")
        (clone / "reports" / "bench-results").mkdir()
        (clone / "reports" / "bench-results" / "run.json").write_text(
            "{}\n", encoding="utf-8")
        (clone / "reports" / "hex-bridge-performance.md").write_text(
            "report\n", encoding="utf-8")
        entry = dict(self._bridge_entry(), performance=True,
                     figures=["hex-bridge-scaling.svg"])
        with tempfile.TemporaryDirectory() as source_directory:
            with patch.object(sync_released, "REPO_ROOT", Path(source_directory)):
                notes = sync_released.prune_unmanaged(entry, clone)
        self.assertTrue(
            (clone / "reports" / "figures" / "hex-bridge-scaling.svg").is_file())
        for gone in ("reports/figures/stale.svg", "reports/bench-results",
                     "reports/hex-bridge-performance.md"):
            self.assertFalse((clone / gone).exists(), gone)
            self.assertIn(f"  remove {gone}", notes)

    def test_prune_is_idempotent(self) -> None:
        clone = self._bridge_clone()
        entry = self._bridge_entry()
        with tempfile.TemporaryDirectory() as source_directory:
            source = Path(source_directory)
            with patch.object(sync_released, "REPO_ROOT", source):
                sync_released.prune_unmanaged(entry, clone)
                self.assertEqual(sync_released.prune_unmanaged(entry, clone), [])

    def test_prune_leaves_the_pins_only_aggregate_alone(self) -> None:
        clone = self.repo / "clone"
        (clone / "docs").mkdir(parents=True)
        (clone / "docs" / "index.html").write_text("<p>", encoding="utf-8")
        (clone / "Hex.lean").write_text("import HexBasic\n", encoding="utf-8")
        (clone / ".github" / "workflows").mkdir(parents=True)
        (clone / ".github" / "workflows" / "docs.yml").write_text(
            "name: docs\n", encoding="utf-8")
        (clone / ".claude").mkdir()
        (clone / ".claude" / "CLAUDE.md").write_text("notes\n", encoding="utf-8")
        entry = {"repo": "leanprover/hex", "pins_only": True}
        self.assertEqual(
            sync_released.prune_unmanaged(entry, clone), ["  remove .claude"])
        self.assertFalse((clone / ".claude").exists())
        self.assertTrue((clone / "Hex.lean").is_file())
        self.assertTrue((clone / "docs" / "index.html").is_file())
        self.assertTrue((clone / ".github" / "workflows" / "docs.yml").is_file())

    def test_prune_honours_the_keep_paths_escape_hatch(self) -> None:
        clone = self.repo / "clone"
        clone.mkdir()
        (clone / "HexTestKit.lean").write_text("import Hex\n", encoding="utf-8")
        (clone / "Stale.lean").write_text("--\n", encoding="utf-8")
        entry = {
            "repo": "leanprover/hex-test-kit",
            "lib": "Hex",
            "readme": False,
            "umbrella": False,
            "spec": None,
            "paths": [{"src": "Hex", "dest": "Hex"}],
            "keep_paths": ["HexTestKit.lean"],
        }
        with tempfile.TemporaryDirectory() as source_directory:
            with patch.object(sync_released, "REPO_ROOT", Path(source_directory)):
                notes = sync_released.prune_unmanaged(entry, clone)
        self.assertTrue((clone / "HexTestKit.lean").is_file())
        self.assertEqual(notes, ["  remove Stale.lean"])

    def test_every_manifest_entry_sweeps_development_instruments(self) -> None:
        """The policy holds for every entry, including ones added later.

        This is the regression the per-entry deletion list could not carry: an
        entry admitted to the manifest without its own cleanup list published
        the sidecars anyway.
        """
        document = yaml.safe_load(
            sync_released.MANIFEST.read_text(encoding="utf-8"))
        instruments = ("bench", "conformance", "conformance-fixtures",
                       "scripts/oracle", "scripts/ci", "reports/bench-results",
                       ".claude")
        for entry in document["repos"]:
            if entry.get("pins_only"):
                continue
            with self.subTest(repo=entry["repo"]):
                clone = self.repo / "sweep" / entry["repo"].split("/")[-1]
                for instrument in instruments:
                    (clone / instrument).mkdir(parents=True)
                    (clone / instrument / "file").write_text(
                        "stale\n", encoding="utf-8")
                (clone / "reports" / "performance.md").write_text(
                    "report\n", encoding="utf-8")
                workflows = clone / ".github" / "workflows"
                workflows.mkdir(parents=True)
                for name in ("ci.yml", "bench.yml"):
                    (workflows / name).write_text("name: x\n", encoding="utf-8")
                sync_released.prune_unmanaged(entry, clone)
                for instrument in instruments:
                    self.assertFalse((clone / instrument).exists(), instrument)
                self.assertFalse((clone / "scripts").exists())
                self.assertFalse((clone / "reports" / "performance.md").exists())
                self.assertFalse((workflows / "bench.yml").exists())
                self.assertTrue((workflows / "ci.yml").is_file())

    def test_apply_paths_copies_explicit_supporting_file(self) -> None:
        with tempfile.TemporaryDirectory() as source_directory:
            source = Path(source_directory)
            (source / "HexExample").mkdir()
            helper = source / "scripts" / "bench" / "check_example.py"
            helper.parent.mkdir(parents=True)
            helper.write_text("print('checked')\n", encoding="utf-8")
            clone = self.repo / "clone"
            workflows = self.repo / "released-ci.yml"
            workflows.write_text(
                "workflows:\n  hex-example: |\n    name: CI\n", encoding="utf-8"
            )
            entry = {
                "repo": "leanprover/hex-example",
                "lib": "HexExample",
                "readme": False,
                "umbrella": False,
                "spec": None,
                "extra_paths": [{
                    "src": "scripts/bench/check_example.py",
                    "dest": "scripts/bench/check_example.py",
                }],
            }
            with (
                patch.object(sync_released, "REPO_ROOT", source),
                patch.object(sync_released, "RELEASED_CI", workflows),
            ):
                sync_released.apply_paths(entry, clone)
            self.assertEqual(
                (clone / "scripts" / "bench" / "check_example.py").read_text(),
                "print('checked')\n",
            )

    def test_prune_unlinks_a_symlink_without_following_it(self) -> None:
        clone = self.repo / "clone"
        clone.mkdir()
        outside = self.repo / "outside"
        outside.mkdir()
        (outside / "kept").write_text("keep\n", encoding="utf-8")
        (clone / "linked").symlink_to(outside, target_is_directory=True)
        with tempfile.TemporaryDirectory() as source_directory:
            source = Path(source_directory)
            (source / "HexBridge").mkdir()
            with patch.object(sync_released, "REPO_ROOT", source):
                notes = sync_released.prune_unmanaged(self._bridge_entry(), clone)
        self.assertEqual(notes, ["  remove linked"])
        self.assertFalse((clone / "linked").exists())
        self.assertEqual((outside / "kept").read_text(), "keep\n")

    def test_keep_paths_rejects_unsafe_destinations(self) -> None:
        for path in (".", "..", "../outside", "/absolute"):
            with self.subTest(path=path), self.assertRaisesRegex(
                ValueError, "unsafe keep_paths entry"
            ):
                sync_released.keep_paths({"keep_paths": [path]})

    def test_released_ci_workflow_requires_complete_text_mapping(self) -> None:
        source = self.repo / "released-ci.yml"
        source.write_text("workflows:\n  hex-example: 42\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "map names to text"):
            sync_released.released_ci_workflows(source)

    def test_apply_ci_workflow_requires_repository_entry(self) -> None:
        source = self.repo / "released-ci.yml"
        source.write_text(
            "workflows:\n  hex-other: |\n    name: CI\n", encoding="utf-8"
        )
        with (
            patch.object(sync_released, "RELEASED_CI", source),
            self.assertRaisesRegex(RuntimeError, "no managed CI workflow"),
        ):
            sync_released.apply_ci_workflow(
                {"repo": "leanprover/hex-example"}, self.repo / "clone"
            )

    def test_extra_workflow_is_published_beside_ci(self) -> None:
        """A declared extra workflow lands at `.github/workflows/<stem>.yml`."""
        source = self.repo / "released-ci.yml"
        source.write_text(
            "workflows:\n  hex: |\n    name: CI\n"
            "extra_workflows:\n  hex:\n    docs: |\n      name: docs\n",
            encoding="utf-8")
        clone = self.repo / "clone"
        with patch.object(sync_released, "RELEASED_CI", source):
            notes = sync_released.apply_ci_workflow(
                {"repo": "leanprover/hex"}, clone)
        self.assertEqual(
            (clone / ".github" / "workflows" / "ci.yml").read_text(), "name: CI\n")
        self.assertEqual(
            (clone / ".github" / "workflows" / "docs.yml").read_text(), "name: docs\n")
        self.assertIn(
            "  scripts/release/released-ci.yml -> .github/workflows/docs.yml", notes)

    def test_sweep_keeps_a_declared_extra_workflow(self) -> None:
        """The allowance follows the manifest, so the sweep cannot orphan it."""
        source = self.repo / "released-ci.yml"
        source.write_text(
            "workflows:\n  hex-bridge: |\n    name: CI\n"
            "extra_workflows:\n  hex-bridge:\n    docs: |\n      name: docs\n",
            encoding="utf-8")
        clone = self._bridge_clone()
        for stem in ("ci", "docs", "stray"):
            (clone / ".github" / "workflows" / f"{stem}.yml").write_text(
                "name: x\n", encoding="utf-8")
        with tempfile.TemporaryDirectory() as source_directory:
            with (
                patch.object(sync_released, "REPO_ROOT", Path(source_directory)),
                patch.object(sync_released, "RELEASED_CI", source),
            ):
                sync_released.prune_unmanaged(self._bridge_entry(), clone)
        workflows = clone / ".github" / "workflows"
        self.assertTrue((workflows / "ci.yml").exists())
        self.assertTrue((workflows / "docs.yml").exists())
        self.assertFalse((workflows / "stray.yml").exists())

    def test_extra_workflows_reject_a_ci_stem(self) -> None:
        """`ci.yml` has one source; declaring it twice would be ambiguous."""
        source = self.repo / "released-ci.yml"
        source.write_text(
            "workflows:\n  hex: |\n    name: CI\n"
            "extra_workflows:\n  hex:\n    ci: |\n      name: other\n",
            encoding="utf-8")
        with (
            patch.object(sync_released, "RELEASED_CI", source),
            self.assertRaisesRegex(ValueError, "ci as an extra workflow"),
        ):
            sync_released.released_extra_workflows(source)

    def test_extra_workflows_require_a_trailing_newline(self) -> None:
        source = self.repo / "released-ci.yml"
        source.write_text(
            "workflows:\n  hex: |\n    name: CI\n"
            "extra_workflows:\n  hex:\n    docs: \"name: docs\"\n",
            encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "must end in a newline"):
            sync_released.released_extra_workflows(source)

    def test_pins_only_apply_overwrites_managed_ci(self) -> None:
        source = self.repo / "released-ci.yml"
        source.write_text(
            "workflows:\n  hex: |\n    name: Managed CI\n", encoding="utf-8"
        )
        clone = self.repo / "clone"
        workflow = clone / ".github" / "workflows" / "ci.yml"
        workflow.parent.mkdir(parents=True)
        workflow.write_text("name: Old CI\n", encoding="utf-8")
        with patch.object(sync_released, "RELEASED_CI", source):
            notes = sync_released.apply_paths(
                {"repo": "leanprover/hex", "pins_only": True}, clone
            )
        self.assertEqual(workflow.read_text(), "name: Managed CI\n")
        self.assertEqual(
            notes,
            ["  scripts/release/released-ci.yml -> .github/workflows/ci.yml"],
        )

    def test_managed_ci_requires_unmanaged_helpers(self) -> None:
        source = self.repo / "released-ci.yml"
        source.write_text(
            "workflows:\n"
            "  hex-example: |\n"
            "    name: CI\n"
            "    jobs:\n"
            "      build:\n"
            "        steps:\n"
            "          - run: bash scripts/ci/check_example.sh\n",
            encoding="utf-8",
        )
        entry = {"repo": "leanprover/hex-example"}
        with (
            patch.object(sync_released, "RELEASED_CI", source),
            self.assertRaisesRegex(RuntimeError, "lacks CI helpers"),
        ):
            sync_released.validate_ci_helpers(entry, self.repo)
        helper = self.repo / "scripts" / "ci" / "check_example.sh"
        helper.parent.mkdir(parents=True)
        helper.write_text("#!/bin/sh\n", encoding="utf-8")
        with patch.object(sync_released, "RELEASED_CI", source):
            sync_released.validate_ci_helpers(entry, self.repo)

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

    def test_manifest_gains_entries_for_unseen_pins(self) -> None:
        (self.repo / "lakefile.toml").write_text(
            '[[require]]\n'
            'name = "HexPoly"\n'
            'git = "https://github.com/leanprover/hex-poly.git"\n'
            'rev = "0000000"\n',
            encoding="utf-8",
        )
        manifest = {"version": "1.2.0", "packages": [{
            "name": "HexPoly",
            "url": "https://github.com/leanprover/hex-poly.git",
            "rev": "0000000",
            "inputRev": "0000000",
        }]}
        path = self.repo / "lake-manifest.json"
        path.write_text(json.dumps(manifest), encoding="utf-8")
        synced = {"hex-basic": "a" * 40, "hex-poly": "b" * 40,
                  "hex-arith": "c" * 40}
        catalog = {"hex-basic": {"lib": "HexBasic", "lakefile": "toml"},
                   "hex-poly": {"lib": "HexPoly", "lakefile": "toml"},
                   "hex-arith": {"lib": "HexArith", "lakefile": "lean"}}
        notes = sync_released.rewrite_manifest(
            {"pins": ["hex-basic", "hex-arith", "hex-poly"]}, self.repo,
            synced, {}, self.pins, catalog)
        packages = {pkg["name"]: pkg
                    for pkg in json.loads(path.read_text())["packages"]}
        self.assertEqual(set(packages), {"HexPoly", "HexBasic", "HexArith"})
        self.assertEqual(packages["HexPoly"]["rev"], "b" * 40)
        basic = packages["HexBasic"]
        self.assertEqual(basic["url"], "https://github.com/leanprover/hex-basic.git")
        self.assertEqual(basic["rev"], "a" * 40)
        self.assertEqual(basic["inputRev"], "a" * 40)
        self.assertTrue(basic["inherited"])
        self.assertEqual(basic["configFile"], "lakefile.toml")
        self.assertEqual(packages["HexArith"]["configFile"], "lakefile.lean")
        self.assertTrue(any("manifest + hex-basic" in note for note in notes))
        # A second pass finds everything present and adds nothing.
        again = sync_released.rewrite_manifest(
            {"pins": ["hex-basic", "hex-arith", "hex-poly"]}, self.repo,
            synced, {}, self.pins, catalog)
        self.assertFalse(any("manifest +" in note for note in again))

    def test_manifest_records_direct_pins_as_not_inherited(self) -> None:
        (self.repo / "lakefile.toml").write_text(
            '[[require]]\n'
            'name = "HexBasic"\n'
            'git = "https://github.com/leanprover/hex-basic.git"\n'
            'rev = "0000000"\n',
            encoding="utf-8",
        )
        path = self.repo / "lake-manifest.json"
        path.write_text(json.dumps({"version": "1.2.0", "packages": []}),
                        encoding="utf-8")
        sync_released.rewrite_manifest(
            {"pins": ["hex-basic"]}, self.repo, {"hex-basic": "a" * 40}, {},
            self.pins, {"hex-basic": {"lib": "HexBasic", "lakefile": "toml"}})
        package = json.loads(path.read_text())["packages"][0]
        self.assertFalse(package["inherited"])

    def _external_import_entry(self, lakefile: str, source: str) -> dict:
        lib = self.repo / "HexProbe"
        lib.mkdir(exist_ok=True)
        (lib / "Basic.lean").write_text(source, encoding="utf-8")
        (self.repo / "lakefile.toml").write_text(lakefile, encoding="utf-8")
        return {"repo": "leanprover/hex-probe", "lib": "HexProbe",
                "lakefile": "toml", "readme": False}

    def test_batteries_import_without_provider_fails_closed(self) -> None:
        entry = self._external_import_entry(
            '[[require]]\nname = "HexBasic"\n'
            'git = "https://github.com/leanprover/hex-basic.git"\nrev = "0"\n',
            "module\n\npublic import HexBasic\nimport Batteries.Data.Vector\n")
        with self.assertRaisesRegex(RuntimeError, "imports Batteries"):
            sync_released.validate_external_imports(entry, self.repo)

    def test_mathlib_requirement_provides_batteries(self) -> None:
        entry = self._external_import_entry(
            '[[require]]\nname = "mathlib"\n'
            'git = "https://github.com/leanprover-community/mathlib4.git"\n'
            'rev = "0"\n',
            "import Mathlib.Tactic\nimport Batteries.Data.Vector\n")
        sync_released.validate_external_imports(entry, self.repo)

    def test_direct_imports_gain_direct_requires_in_toml(self) -> None:
        lib = self.repo / "HexProbe"
        lib.mkdir()
        (lib / "Basic.lean").write_text(
            "module\n\npublic import HexArith.Basic\nimport HexMatrix\n"
            "import HexProbe.Other\n", encoding="utf-8")
        (self.repo / "lakefile.toml").write_text(
            'name = "hex-probe"\n\n[[require]]\nname = "HexMatrix"\n'
            'git = "https://github.com/leanprover/hex-matrix.git"\nrev = "0"\n\n'
            '[[lean_lib]]\nname = "HexProbe"\n', encoding="utf-8")
        entry = {"repo": "leanprover/hex-probe", "lib": "HexProbe",
                 "lakefile": "toml", "readme": False,
                 "pins": ["hex-basic", "hex-arith", "hex-matrix"]}
        synced = {"hex-basic": "a" * 40, "hex-arith": "b" * 40,
                  "hex-matrix": "c" * 40}
        catalog = {"hex-basic": {"lib": "HexBasic", "lakefile": "toml"},
                   "hex-arith": {"lib": "HexArith", "lakefile": "lean"},
                   "hex-matrix": {"lib": "HexMatrix", "lakefile": "toml"}}
        notes = sync_released.rewrite_requires(
            entry, self.repo, synced, {}, catalog)
        text = (self.repo / "lakefile.toml").read_text()
        self.assertEqual(notes, [
            f'  require + hex-arith (HexArith) -> {"b" * 12} (lakefile.toml)'])
        self.assertNotIn("hex-basic.git", text)
        block = ('[[require]]\nname = "HexArith"\n'
                 'git = "https://github.com/leanprover/hex-arith.git"\n'
                 f'rev = "{"b" * 40}"\n\n[[lean_lib]]')
        self.assertIn(block, text)
        self.assertEqual(text.count("[[require]]"), 2)
        self.assertEqual(
            sync_released.rewrite_requires(entry, self.repo, synced, {}, catalog),
            [])

    def test_direct_imports_gain_direct_requires_in_lean(self) -> None:
        lib = self.repo / "HexProbe"
        lib.mkdir()
        (lib / "Basic.lean").write_text(
            "import HexBasic.Core\n", encoding="utf-8")
        (self.repo / "lakefile.lean").write_text(
            "import Lake\n\nopen Lake DSL\n\npackage «hex-probe» where\n"
            "  leanOptions := #[]\n\nrequire HexArith from git\n"
            '  "https://github.com/leanprover/hex-arith.git" @ "0"\n\n'
            "@[default_target]\nlean_lib HexProbe\n", encoding="utf-8")
        entry = {"repo": "leanprover/hex-probe", "lib": "HexProbe",
                 "lakefile": "lean", "readme": False,
                 "pins": ["hex-basic", "hex-arith"]}
        sync_released.rewrite_requires(
            entry, self.repo, {"hex-basic": "a" * 40, "hex-arith": "b" * 40}, {},
            {"hex-basic": {"lib": "HexBasic", "lakefile": "toml"},
             "hex-arith": {"lib": "HexArith", "lakefile": "lean"}})
        text = (self.repo / "lakefile.lean").read_text()
        self.assertIn(
            '@ "0"\n\nrequire HexBasic from git\n'
            f'  "https://github.com/leanprover/hex-basic.git" @ "{"a" * 40}"\n\n'
            "@[default_target]", text)

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
            patch.object(sync_released, "selection_check", return_value=None),
            patch.object(sync_released, "sync_repo", side_effect=publish),
            patch("sys.argv", argv),
        ):
            self.assertEqual(sync_released.main(), 1)

        advanced = json.loads(baseline.read_text(encoding="utf-8"))
        self.assertEqual(advanced["first"], "new-first")
        self.assertEqual(advanced["second"], "old-second")

    def test_only_sync_seeds_dependency_pins_from_baseline(self) -> None:
        manifest = self.repo / "released.yml"
        manifest.write_text(
            "repos:\n"
            "  - repo: leanprover/upstream\n"
            "  - repo: leanprover/downstream\n",
            encoding="utf-8",
        )
        baseline = self.repo / "baseline.json"
        baseline.write_text(
            json.dumps({"upstream": "new-upstream", "downstream": "old-downstream"}),
            encoding="utf-8",
        )

        def publish(entry, _source_sha, _token, _dry_run, synced,
                    _baseline, _force, _dep_owner, _pins):
            self.assertEqual(entry["repo"], "leanprover/downstream")
            self.assertEqual(synced["upstream"], "new-upstream")
            self.assertEqual(synced["downstream"], "old-downstream")
            synced["downstream"] = "new-downstream"
            return True

        argv = [
            "sync_released.py",
            "--token",
            "secret-token",
            "--baseline",
            str(baseline),
            "--only",
            "downstream",
        ]
        with (
            patch.object(sync_released, "MANIFEST", manifest),
            patch.object(sync_released, "external_pins", return_value={}),
            patch.object(sync_released, "run", return_value="source-sha"),
            patch.object(sync_released, "selection_check", return_value=None),
            patch.object(sync_released, "sync_repo", side_effect=publish),
            patch("sys.argv", argv),
        ):
            self.assertEqual(sync_released.main(), 0)

        advanced = json.loads(baseline.read_text(encoding="utf-8"))
        self.assertEqual(advanced["upstream"], "new-upstream")
        self.assertEqual(advanced["downstream"], "new-downstream")


class LibBuildSettingTests(unittest.TestCase):
    """The mirror's `lean_lib` must be built the way hex-dev builds it.

    A mirror that drops `precompileModules` still compiles; the failure surfaces
    only downstream, where an `@[extern]` declaration has no native
    implementation because its module dynlib was never built.
    """

    SOURCE = (
        "lean_lib Plain where\n"
        "\n"
        "lean_lib Consumer where\n"
        "  -- comment lines are not settings\n"
        "  precompileModules := true\n"
        "\n"
        "lean_lib Linked where\n"
        "  precompileModules := true\n"
        "  extraDepTargets := #[`consumerffi]\n"
        "  moreLinkArgs :=\n"
        "    if System.Platform.isOSX then\n"
        "      #[]\n"
        "    else\n"
        "      #[\"-ldl\"]\n"
    )

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        # The monorepo lakefile and the mirror clone are separate trees, and
        # both are called lakefile.lean.
        self.repo = Path(self.temporary.name) / "clone"
        self.repo.mkdir()
        self.source = Path(self.temporary.name) / "hex-dev" / "lakefile.lean"
        self.source.parent.mkdir()
        self.source.write_text(self.SOURCE, encoding="utf-8")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def settings(self, lib: str) -> dict[str, str]:
        return sync_released.source_build_settings(lib, self.source)

    def rewrite(self, entry: dict) -> list[str]:
        with patch.object(sync_released, "LAKEFILE", self.source):
            return sync_released.rewrite_lib_settings(entry, self.repo)

    def test_settings_are_read_from_the_monorepo_lakefile(self) -> None:
        self.assertEqual(self.settings("Plain"), {})
        self.assertEqual(self.settings("Consumer"), {"precompileModules": "true"})
        self.assertEqual(self.settings("Linked"), {
            "precompileModules": "true",
            "extraDepTargets": "#[`consumerffi]",
            "moreLinkArgs": 'if System.Platform.isOSX then #[] else #["-ldl"]',
        })

    def test_a_released_library_must_be_a_lean_lib_here(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "declares no lean_lib Absent"):
            self.settings("Absent")

    def test_toml_mirror_gains_precompilation(self) -> None:
        lakefile = self.repo / "lakefile.toml"
        lakefile.write_text(
            'name = "consumer"\n\n[[lean_lib]]\nname = "Consumer"\n\n'
            '[[lean_lib]]\nname = "ConsumerTests"\nglobs = ["Consumer.Tests"]\n',
            encoding="utf-8")
        entry = {"lib": "Consumer", "lakefile": "toml"}
        notes = self.rewrite(entry)
        self.assertEqual(notes, ["  precompileModules on lean_lib Consumer "
                                 "(lakefile.toml)"])
        text = lakefile.read_text(encoding="utf-8")
        self.assertIn('name = "Consumer"\nprecompileModules = true\n', text)
        self.assertNotIn("ConsumerTests\"\nprecompileModules", text)
        self.assertEqual(self.rewrite(entry), [])

    def test_lean_mirror_gains_precompilation(self) -> None:
        lakefile = self.repo / "lakefile.lean"
        lakefile.write_text(
            "@[default_target]\nlean_lib Consumer where\n"
            "  moreLinkArgs := #[]\n\nlean_exe check where\n"
            "  root := `Consumer.Check\n",
            encoding="utf-8")
        entry = {"lib": "Consumer", "lakefile": "lean"}
        self.assertEqual(self.rewrite(entry),
                         ["  precompileModules on lean_lib Consumer "
                          "(lakefile.lean)"])
        self.assertIn("lean_lib Consumer where\n  precompileModules := true\n"
                      "  moreLinkArgs := #[]\n",
                      lakefile.read_text(encoding="utf-8"))
        self.assertEqual(self.rewrite(entry), [])

    def test_a_bare_lean_lib_gains_a_settings_block(self) -> None:
        lakefile = self.repo / "lakefile.lean"
        lakefile.write_text(
            "@[default_target]\nlean_lib Consumer\n\nlean_lib Other where\n",
            encoding="utf-8")
        self.rewrite({"lib": "Consumer", "lakefile": "lean"})
        self.assertIn("lean_lib Consumer where\n  precompileModules := true\n",
                      lakefile.read_text(encoding="utf-8"))

    def test_a_library_without_settings_is_left_alone(self) -> None:
        lakefile = self.repo / "lakefile.toml"
        original = '[[lean_lib]]\nname = "PlainLib"\n'
        lakefile.write_text(original, encoding="utf-8")
        self.assertEqual(self.rewrite({"lib": "Plain", "lakefile": "toml"}), [])
        self.assertEqual(lakefile.read_text(encoding="utf-8"), original)

    def test_a_missing_link_setting_stops_the_publication(self) -> None:
        lakefile = self.repo / "lakefile.lean"
        lakefile.write_text(
            "lean_lib Linked where\n  extraDepTargets := #[`consumerffi]\n",
            encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "must set moreLinkArgs"):
            self.rewrite({"lib": "Linked", "lakefile": "lean"})

    def test_a_missing_mirror_library_stops_the_publication(self) -> None:
        (self.repo / "lakefile.toml").write_text(
            '[[lean_lib]]\nname = "Other"\n', encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "declares no lean_lib Consumer"):
            self.rewrite({"lib": "Consumer", "lakefile": "toml"})

    def test_a_contradicting_mirror_setting_stops_the_publication(self) -> None:
        (self.repo / "lakefile.toml").write_text(
            '[[lean_lib]]\nname = "Consumer"\nprecompileModules = false\n',
            encoding="utf-8")
        with self.assertRaisesRegex(RuntimeError, "contradicting"):
            self.rewrite({"lib": "Consumer", "lakefile": "toml"})

    def test_every_released_library_keeps_its_monorepo_lean_lib(self) -> None:
        manifest = yaml.safe_load(
            sync_released.MANIFEST.read_text(encoding="utf-8"))
        for entry in manifest["repos"]:
            if entry.get("pins_only"):
                continue
            with self.subTest(repo=entry["repo"]):
                sync_released.source_build_settings(entry["lib"])


class TokenPreflightTests(unittest.TestCase):
    """A library published here but missing from every token's selected
    repositories must stop the run before anything is pushed."""

    ENTRIES = [{"repo": "leanprover/hex-basic"}, {"repo": "leanprover/hex-arith"}]

    def test_writable_repos_pass(self) -> None:
        with patch.object(sync_released, "selection_check", return_value=None):
            routed, blocked = sync_released.route_tokens(self.ENTRIES, ["t"])
        self.assertEqual(blocked, [])
        self.assertEqual(routed, {e["repo"]: "t" for e in self.ENTRIES})

    def test_unlisted_repo_is_reported_with_every_tokens_reason(self) -> None:
        def check(repo: str, token: str) -> str | None:
            if repo.endswith("hex-basic"):
                return None
            return f"not in the token's selected repositories ({token})"

        with patch.object(sync_released, "selection_check", side_effect=check):
            routed, blocked = sync_released.route_tokens(self.ENTRIES, ["t1", "t2"])
        self.assertEqual(routed, {"leanprover/hex-basic": "t1"})
        self.assertEqual(len(blocked), 1)
        self.assertIn("leanprover/hex-arith", blocked[0])
        self.assertIn("token 1: not in the token's selected repositories (t1)", blocked[0])
        self.assertIn("token 2: not in the token's selected repositories (t2)", blocked[0])

    def test_repos_split_across_tokens_each_route_to_a_seeing_token(self) -> None:
        def check(repo: str, token: str) -> str | None:
            on = {"leanprover/hex-basic": "t1", "leanprover/hex-arith": "t2"}
            return None if on[repo] == token else "not in the token's selected repositories"

        with patch.object(sync_released, "selection_check", side_effect=check):
            routed, blocked = sync_released.route_tokens(self.ENTRIES, ["t1", "t2"])
        self.assertEqual(blocked, [])
        self.assertEqual(routed, {"leanprover/hex-basic": "t1",
                                  "leanprover/hex-arith": "t2"})

    def test_first_seeing_token_wins_and_later_tokens_are_not_probed(self) -> None:
        probes: list[tuple[str, str]] = []

        def check(repo: str, token: str) -> str | None:
            probes.append((repo, token))
            return None

        with patch.object(sync_released, "selection_check", side_effect=check):
            routed, _ = sync_released.route_tokens(self.ENTRIES, ["t1", "t2"])
        self.assertEqual(set(routed.values()), {"t1"})
        self.assertNotIn(("leanprover/hex-basic", "t2"), probes)

    def test_env_tokens_collects_in_numeric_order_and_skips_empty(self) -> None:
        env = {"RELEASED_SYNC_PAT_2": "tok2", "RELEASED_SYNC_PAT": "tok1",
               "RELEASED_SYNC_PAT_10": "tok10", "RELEASED_SYNC_PATX": "not-a-slot",
               "RELEASED_SYNC_PAT_3": ""}
        with patch.dict(sync_released.os.environ, env, clear=True):
            self.assertEqual(sync_released.env_tokens(), ["tok1", "tok2", "tok10"])

    def test_env_tokens_ignores_noncanonical_slots(self) -> None:
        # `_0`, `_1`, and zero-padded suffixes would sort ambiguously against
        # the base slot, so only the base and integer suffixes >= 2 count.
        env = {"RELEASED_SYNC_PAT": "tok1", "RELEASED_SYNC_PAT_0": "alias0",
               "RELEASED_SYNC_PAT_1": "alias1", "RELEASED_SYNC_PAT_02": "alias02"}
        with patch.dict(sync_released.os.environ, env, clear=True):
            self.assertEqual(sync_released.env_tokens(), ["tok1"])

    def test_empty_cli_token_is_rejected(self) -> None:
        # An empty token probes anonymously and would win the routing for every
        # public repository, only to fail at push time.
        argv = ["sync_released.py", "--token", "", "--baseline",
                str(self.repo / "baseline.json")]
        with patch("sys.argv", argv), self.assertRaises(SystemExit) as caught:
            sync_released.main()
        self.assertEqual(caught.exception.code, 2)

    def test_dry_run_passes_no_token_despite_env_tokens(self) -> None:
        manifest = self.repo / "released.yml"
        manifest.write_text("repos:\n  - repo: leanprover/hex-basic\n", encoding="utf-8")
        baseline = self.repo / "baseline.json"
        baseline.write_text(json.dumps({"hex-basic": "old"}), encoding="utf-8")
        seen_tokens: list = []

        def publish(entry, _source_sha, token, _dry_run, synced,
                    _baseline, _force, _dep_owner, _pins):
            seen_tokens.append(token)
            return False

        argv = ["sync_released.py", "--dry-run", "--baseline", str(baseline)]
        env = {"RELEASED_SYNC_PAT": "tok1", "RELEASED_SYNC_PAT_2": "tok2"}
        with (
            patch.object(sync_released, "MANIFEST", manifest),
            patch.object(sync_released, "external_pins", return_value={}),
            patch.object(sync_released, "run", return_value="source-sha"),
            patch.object(sync_released, "sync_repo", side_effect=publish),
            patch.dict(sync_released.os.environ, env),
            patch("sys.argv", argv),
        ):
            self.assertEqual(sync_released.main(), 0)
        self.assertEqual(seen_tokens, [None])

    def _check(self, advertisement, anonymous: list | None = None) -> str | None:
        """Run selection_check with the receive-pack advertisement answering
        `advertisement` and, when reached, the anonymous `_api_repo` probe
        answering from `anonymous`."""
        with (
            patch.object(sync_released, "_receive_pack_status",
                         side_effect=[advertisement]),
            patch.object(sync_released, "_api_repo",
                         side_effect=anonymous or []),
        ):
            return sync_released.selection_check("leanprover/hex-arith", "t")

    def test_write_capable_repo_passes(self) -> None:
        self.assertIsNone(self._check(200))

    def test_unselected_repo_is_named_as_such(self) -> None:
        # A public repository is readable by any fine-grained token whether or
        # not it is selected, so only the write handshake separates the tokens:
        # unauthorized receive-pack means no Contents: write grant here.
        for status in (401, 403):
            with self.subTest(status=status):
                reason = self._check(status)
                self.assertIn("not granted Contents: write", reason)

    def test_absent_repo_says_create_it(self) -> None:
        reason = self._check(404, [404])
        self.assertIn("no such repository", reason)

    def test_rate_limit_is_indeterminate_not_a_missing_repo(self) -> None:
        reason = self._check(429)
        self.assertIn("could not be checked", reason)
        self.assertNotIn("no such repository", reason)

    def test_server_error_is_indeterminate(self) -> None:
        reason = self._check(503)
        self.assertIn("could not be checked", reason)

    def test_anonymous_probe_failure_does_not_claim_the_repo_is_missing(self) -> None:
        reason = self._check(404, [429])
        self.assertIn("undetermined", reason)
        self.assertNotIn("no such repository", reason)

    def test_hidden_but_public_repo_is_undetermined(self) -> None:
        reason = self._check(404, [{"name": "hex-arith"}])
        self.assertIn("undetermined", reason)
        self.assertNotIn("no such repository", reason)

    def test_network_failure_is_indeterminate(self) -> None:
        import urllib.error
        reason = self._check(urllib.error.URLError("dns"))
        self.assertIn("could not be checked", reason)

    def test_misspelled_only_fails_instead_of_publishing_nothing(self) -> None:
        manifest = self.repo / "released.yml"
        manifest.write_text("repos:\n  - repo: leanprover/hex-basic\n", encoding="utf-8")
        baseline = self.repo / "baseline.json"
        baseline.write_text(json.dumps({"hex-basic": "old"}), encoding="utf-8")
        argv = ["sync_released.py", "--token", "secret-token",
                "--baseline", str(baseline), "--only", "hex-baisc"]
        with (
            patch.object(sync_released, "MANIFEST", manifest),
            patch.object(sync_released, "external_pins", return_value={}),
            patch.object(sync_released, "run", return_value="source-sha"),
            patch.object(sync_released, "sync_repo") as publish,
            patch("sys.argv", argv),
        ):
            self.assertEqual(sync_released.main(), 1)
        publish.assert_not_called()

    def test_main_refuses_to_push_when_a_target_is_unwritable(self) -> None:
        manifest = self.repo / "released.yml"
        manifest.write_text(
            "repos:\n  - repo: leanprover/hex-basic\n  - repo: leanprover/hex-arith\n",
            encoding="utf-8",
        )
        argv = ["sync_released.py", "--token", "secret-token",
                "--baseline", str(self.repo / "baseline.json")]
        with (
            patch.object(sync_released, "MANIFEST", manifest),
            patch.object(sync_released, "external_pins", return_value={}),
            patch.object(sync_released, "run", return_value="source-sha"),
            patch.object(sync_released, "selection_check", return_value="HTTP 404"),
            patch.object(sync_released, "sync_repo") as publish,
            patch("sys.argv", argv),
        ):
            self.assertEqual(sync_released.main(), 1)
        publish.assert_not_called()

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self.temporary.name)
        self.addCleanup(self.temporary.cleanup)


class AggregateReadmeTests(unittest.TestCase):
    """The aggregate README's table is generated, never hand-maintained."""

    MANIFEST = {
        "repos": [
            {"repo": "leanprover/hex-matrix", "lib": "HexMatrix",
             "component": "Matrices"},
            {"repo": "leanprover/hex-matrix-mathlib", "lib": "HexMatrixMathlib"},
            {"repo": "leanprover/hex-lll", "lib": "HexLLL",
             "component": "LLL lattice reduction"},
            {"repo": "leanprover/hex-test-kit", "lib": "Hex", "aggregate": False},
            {"repo": "leanprover/hex", "pins_only": True},
        ],
    }

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.template = Path(self.temporary.name) / "hex-README.md"
        self.template.write_text(
            "# hex\n\n"
            "<!-- LIBRARIES:BEGIN (generated) -->\n"
            "| Component | stale | rows |\n"
            "<!-- LIBRARIES:END -->\n\n"
            "<!-- ANNOUNCEMENTS:BEGIN (generated) -->\n"
            "- stale announcement\n"
            "<!-- ANNOUNCEMENTS:END -->\n\n"
            "trailer\n",
            encoding="utf-8",
        )
        self.addCleanup(self.temporary.cleanup)

    def test_rows_cover_computational_libraries_only(self) -> None:
        rows = [entry["repo"] for entry in aggregate_readme.table_entries(self.MANIFEST)]
        # the Mathlib companion occupies a column, the test kit is not aggregated,
        # and the aggregate does not list itself
        self.assertEqual(rows, ["leanprover/hex-matrix", "leanprover/hex-lll"])

    def test_render_replaces_the_marked_region(self) -> None:
        text = aggregate_readme.render(self.MANIFEST, self.template)
        self.assertNotIn("stale", text)
        self.assertTrue(text.startswith("# hex\n"))
        self.assertTrue(text.endswith("trailer\n"))
        self.assertIn(
            "| Matrices | [HexMatrix](https://github.com/leanprover/hex-matrix) | "
            "[HexMatrixMathlib](https://github.com/leanprover/hex-matrix-mathlib) |",
            text,
        )
        # a computational library with no Mathlib companion still gets a row
        self.assertIn(
            "| LLL lattice reduction | [HexLLL](https://github.com/leanprover/hex-lll) "
            f"| {aggregate_readme.NO_LAYER} |",
            text,
        )

    def test_announcements_render_per_library(self) -> None:
        manifest = {"repos": [
            {"repo": "leanprover/hex-lll", "lib": "HexLLL",
             "component": "LLL lattice reduction",
             "announcements": {"zulip": "https://z.example/t",
                               "blog": "https://b.example/p"}},
            {"repo": "leanprover/hex-matrix", "lib": "HexMatrix",
             "component": "Matrices"},
            {"repo": "leanprover/hex", "pins_only": True},
        ]}
        rendered = aggregate_readme.render_announcements(manifest)
        # venue order is fixed by VENUES, not by the manifest's key order
        self.assertEqual(
            rendered,
            "- LLL lattice reduction ([HexLLL](https://github.com/leanprover/hex-lll)): "
            "[blog post](https://b.example/p), [Zulip](https://z.example/t)")
        # a library with no announcements contributes no line
        self.assertNotIn("Matrices", rendered)

    def test_announcement_region_is_replaced(self) -> None:
        text = aggregate_readme.render(self.MANIFEST, self.template)
        self.assertNotIn("stale announcement", text)
        self.assertTrue(text.endswith("trailer\n"))

    def test_template_without_announcement_markers_is_an_error(self) -> None:
        partial = Path(self.temporary.name) / "partial.md"
        partial.write_text(
            "# hex\n<!-- LIBRARIES:BEGIN -->\n<!-- LIBRARIES:END -->\n",
            encoding="utf-8")
        with self.assertRaises(ValueError):
            aggregate_readme.render(self.MANIFEST, partial)

    def test_missing_component_label_is_an_error(self) -> None:
        manifest = {"repos": [{"repo": "leanprover/hex-matrix", "lib": "HexMatrix"}]}
        with self.assertRaises(ValueError):
            aggregate_readme.render(manifest, self.template)

    def test_template_without_markers_is_an_error(self) -> None:
        bare = Path(self.temporary.name) / "bare.md"
        bare.write_text("# hex\n", encoding="utf-8")
        with self.assertRaises(ValueError):
            aggregate_readme.render(self.MANIFEST, bare)


if __name__ == "__main__":
    unittest.main()
