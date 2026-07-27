#!/usr/bin/env python3
"""Regression tests for the Mathlib-free benchmark import-graph lint."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_benches_mathlib_free as lint


class BenchLintTests(unittest.TestCase):
    def make_repo(self) -> tuple[tempfile.TemporaryDirectory[str], Path]:
        tmp = tempfile.TemporaryDirectory()
        return tmp, Path(tmp.name)

    def write(self, root: Path, rel: str, text: str) -> None:
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def target(self, root: Path, source: str) -> lint._ExeTarget:
        self.write(root, "lakefile.lean", source)
        targets = lint._parse_exe_targets(root / "lakefile.lean")
        self.assertEqual(list(targets), ["sample_bench"])
        return targets["sample_bench"]

    def test_src_dir_and_module_import_modifiers_reach_mathlib(self) -> None:
        for import_line in (
            "public import Mathlib.Data.Nat.Basic",
            "public meta import Mathlib.Tactic",
        ):
            with self.subTest(import_line=import_line):
                tmp, root = self.make_repo()
                with tmp:
                    target = self.target(
                        root,
                        'lean_exe sample_bench where\n'
                        '  srcDir := "bench"\n'
                        '  root := `Sample.Root\n',
                    )
                    self.write(
                        root, "bench/Sample/Root.lean",
                        f"module\n\n{import_line}\n\npublic section\n",
                    )
                    self.assertEqual(
                        target.root_path(root), root / "bench/Sample/Root.lean"
                    )
                    chain = lint._walk_for_mathlib(target, root)
                    self.assertIsNotNone(chain)
                    assert chain is not None
                    self.assertEqual(chain[0], "Sample.Root")
                    self.assertTrue(chain[-1].startswith("Mathlib."))

    def test_prelude_before_import_reaches_mathlib(self) -> None:
        for header in ("prelude\n", "module\nprelude\n"):
            with self.subTest(header=header):
                tmp, root = self.make_repo()
                with tmp:
                    target = self.target(
                        root,
                        'lean_exe sample_bench where\n'
                        '  srcDir := "bench"\n'
                        '  root := `Sample.Root\n',
                    )
                    self.write(
                        root, "bench/Sample/Root.lean",
                        header + "public import Mathlib.Data.Nat.Basic\n",
                    )
                    self.assertEqual(
                        lint._walk_for_mathlib(target, root),
                        ["Sample.Root", "Mathlib.Data.Nat.Basic"],
                    )

    def test_commented_lake_fields_do_not_override_real_fields(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            target = self.target(
                root,
                'lean_exe sample_bench where\n'
                '  -- srcDir := "safe"\n'
                '  -- root := `Safe.Root\n'
                '  srcDir := "bench"\n'
                '  root := `Danger.Root\n',
            )
            self.assertEqual(target.src_dir, Path("bench"))
            self.assertEqual(target.root, "Danger.Root")
            self.write(
                root, "bench/Danger/Root.lean",
                "module\npublic import Mathlib.Data.Nat.Basic\n",
            )
            self.assertIsNotNone(lint._walk_for_mathlib(target, root))

    def test_indented_attributed_and_escaped_executable_names(self) -> None:
        declarations = (
            '  lean_exe sample_bench where\n'
            '    srcDir := "bench"\n'
            '    root := `Sample.Root\n',
            '@[default_target] lean_exe sample_bench where\n'
            '  srcDir := "bench"\n'
            '  root := `Sample.Root\n',
            'lean_exe «sample_bench» where\n'
            '  srcDir := "bench"\n'
            '  root := `Sample.Root\n',
        )
        for declaration in declarations:
            with self.subTest(declaration=declaration.splitlines()[0]):
                tmp, root = self.make_repo()
                with tmp:
                    target = self.target(root, declaration)
                    self.assertEqual(target.name, "sample_bench")
                    self.assertTrue(target.name.endswith("_bench"))

    def test_missing_declared_root_is_failure(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            target = self.target(
                root,
                'lean_exe sample_bench where\n'
                '  srcDir := "bench"\n'
                '  root := `Missing.Root\n',
            )
            failures = lint._missing_exe_root_failures(
                {target.name: target}, root
            )
            self.assertEqual(len(failures), 1)
            self.assertIn("bench/Missing/Root.lean", failures[0])

    def test_default_src_dir_ignores_following_comment(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            target = self.target(
                root,
                'lean_exe sample_bench where\n'
                '  root := `Sample.Root\n\n'
                '-- Other targets use srcDir := "bench".\n'
                'lean_lib Other where\n'
                '  srcDir := "bench"\n',
            )
            self.assertEqual(target.src_dir, Path())

    def test_computed_src_dir_fails_closed(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            self.write(
                root, "lakefile.lean",
                'lean_exe sample_bench where\n'
                '  srcDir := benchSource\n'
                '  root := `Sample.Root\n',
            )
            with self.assertRaisesRegex(ValueError, "nonliteral srcDir"):
                lint._parse_exe_targets(root / "lakefile.lean")

    def test_probe_meta_import_of_leanbench_is_forbidden(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            path = root / "Probe.lean"
            path.write_text("module\npublic meta import LeanBench\n")
            self.assertIn("imports LeanBench", lint._probe_violations(path))

    def test_clean_src_dir_closure(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            target = self.target(
                root,
                'lean_exe sample_bench where\n'
                '  srcDir := "bench"\n'
                '  root := `Sample.Root\n',
            )
            self.write(
                root, "bench/Sample/Root.lean",
                "module\npublic import Project.Core\npublic section\n",
            )
            self.write(
                root, "Project/Core.lean",
                "module\npublic import Std.Data.HashMap\npublic section\n",
            )
            self.assertIsNone(lint._walk_for_mathlib(target, root))

    def test_src_dir_root_traverses_repo_library_imports(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            target = self.target(
                root,
                'lean_exe sample_bench where\n'
                '  srcDir := "bench"\n'
                '  root := `Sample.Root\n',
            )
            self.write(
                root, "bench/Sample/Root.lean",
                "module\npublic import Project.Core\npublic section\n",
            )
            self.write(
                root, "Project/Core.lean",
                "module\npublic import Mathlib.Data.Nat.Basic\npublic section\n",
            )
            self.assertEqual(
                lint._walk_for_mathlib(target, root),
                ["Sample.Root", "Project.Core", "Mathlib.Data.Nat.Basic"],
            )

    def test_dependency_library_src_dir_is_resolved(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            target = self.target(
                root,
                'lean_exe sample_bench where\n'
                '  srcDir := "bench"\n'
                '  root := `Sample.Root\n',
            )
            self.write(
                root, "bench/Sample/Root.lean",
                "module\npublic import Dependency.Core\n",
            )
            self.write(
                root, ".lake/packages/dependency/lakefile.toml",
                'name = "dependency"\n'
                '[[lean_lib]]\n'
                'name = "Dependency"\n'
                'srcDir = "src"\n',
            )
            self.write(
                root, ".lake/packages/dependency/src/Dependency/Core.lean",
                "module\npublic import Mathlib.Data.Nat.Basic\n",
            )
            self.assertEqual(
                lint._walk_for_mathlib(target, root),
                ["Sample.Root", "Dependency.Core", "Mathlib.Data.Nat.Basic"],
            )


if __name__ == "__main__":
    unittest.main()
