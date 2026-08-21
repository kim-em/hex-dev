#!/usr/bin/env python3
"""Regression tests for release-wide toolchain and dependency synchronization."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

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

    def _check(self, responses: list) -> str | None:
        """Run selection_check with `_api_repo` answering from `responses`,
        in call order: authenticated first, then the anonymous probe."""
        with patch.object(sync_released, "_api_repo", side_effect=responses):
            return sync_released.selection_check("leanprover/hex-arith", "t")

    def test_visible_repo_passes(self) -> None:
        self.assertIsNone(self._check([{"permissions": {"push": True}}]))

    def test_visible_but_read_only_role_still_passes(self) -> None:
        # `permissions` reports the *user's* role, not the token's grants, so it
        # is deliberately not treated as evidence either way.
        self.assertIsNone(self._check([{"permissions": {"push": False}}]))

    def test_unselected_repo_is_named_as_such(self) -> None:
        reason = self._check([404, {"name": "hex-arith"}])
        self.assertIn("not in the token's selected repositories", reason)

    def test_absent_repo_says_create_it(self) -> None:
        reason = self._check([404, 404])
        self.assertIn("no such repository", reason)

    def test_rate_limit_is_indeterminate_not_a_missing_repo(self) -> None:
        for status in (403, 429):
            with self.subTest(status=status):
                reason = self._check([status])
                self.assertIn("could not be checked", reason)
                self.assertNotIn("no such repository", reason)

    def test_server_error_is_indeterminate(self) -> None:
        reason = self._check([503])
        self.assertIn("could not be checked", reason)

    def test_anonymous_probe_failure_does_not_claim_the_repo_is_missing(self) -> None:
        reason = self._check([404, 429])
        self.assertIn("undetermined", reason)
        self.assertNotIn("no such repository", reason)

    def test_network_failure_is_indeterminate(self) -> None:
        import urllib.error
        reason = self._check([urllib.error.URLError("dns")])
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
