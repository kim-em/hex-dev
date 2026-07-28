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

    def manifest(self, root: Path, entries: str) -> tuple[Path, ...]:
        self.write(root, "libraries.yml", "libraries:\n" + entries)
        return lint._mathlib_probe_roots(root)

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

    def test_manifest_declares_explicit_non_suffix_probe_root(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n"
                "  HexCore:\n"
                "    deps: []\n"
                "    mathlib: false\n"
                "    done_through: 3\n"
                "    status: active\n",
            )
            self.assertEqual(roots, (root / "bench/HexRCF/ProofProbe",))
            self.write(
                root, "bench/HexRCF/ProofProbe/Import.lean", "import LeanBench\n"
            )
            self.write(
                root,
                "bench/HexRCF/ProofProbe/Register.lean",
                "@[implemented_by ignored] private setup_fixed_benchmark sample := 1\n",
            )
            self.write(
                root, "bench/HexRCF/ProofProbe/Main.lean",
                "noncomputable def main := pure ()\n"
            )
            self.write(
                root, "bench/HexRCF/ProofProbe/Clock.lean",
                "#check IO.monoNanosNow\n"
            )
            probes = lint._find_mathlib_probe_files(root, roots)
            self.assertEqual(len(probes), 4)
            violations = {
                violation
                for probe in probes
                for violation in lint._probe_violations(probe)
            }
            self.assertEqual(
                violations,
                {
                    "imports LeanBench",
                    "registers a LeanBench benchmark",
                    "defines main",
                    "uses an in-process monotonic clock",
                },
            )

    def test_mixed_owner_keeps_compiled_bench_outside_probe_root(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n",
            )
            target = self.target(
                root,
                "lean_exe sample_bench where\n"
                "  srcDir := \"bench\"\n"
                "  root := `HexRCF.Bench\n",
            )
            self.write(
                root,
                "bench/HexRCF/Bench.lean",
                "import LeanBench\nsetup_fixed_benchmark compiled := 1\n",
            )
            self.write(
                root,
                "bench/HexRCF/ProofProbe/Tactic.lean",
                "import Mathlib\n",
            )
            self.write(
                root,
                "bench/HexRCF/ProofProbeExtra/Hidden.lean",
                "import Mathlib\n",
            )
            self.write(
                root,
                "bench/HexRCF/Hidden.lean",
                "import Project.Helper\n",
            )
            self.write(root, "Project/Helper.lean", "import Mathlib\n")
            self.assertFalse(
                lint._is_mathlib_probe_path(
                    root / "bench/HexRCF/Bench.lean", root, roots
                )
            )
            self.assertFalse(
                lint._is_mathlib_probe_path(
                    root / "bench/HexRCF/ProofProbeExtra/Hidden.lean",
                    root,
                    roots,
                )
            )
            self.assertIsNone(lint._probe_root_path(target, root, roots))
            self.assertEqual(
                lint._find_mathlib_probe_files(root, roots),
                [root / "bench/HexRCF/ProofProbe/Tactic.lean"],
            )
            failures = lint._undeclared_mathlib_bench_failures(root, roots)
            self.assertEqual(len(failures), 2)
            joined = "\n".join(failures)
            self.assertIn("HexRCF/Hidden.lean", joined)
            self.assertIn("Project.Helper", joined)
            self.assertIn("ProofProbeExtra/Hidden.lean", joined)

    def test_undeclared_suffix_mathlib_source_gets_no_exception(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexFooMathlib:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n",
            )
            self.write(
                root, "bench/HexFooMathlib/Hidden.lean", "import Mathlib\n"
            )
            failures = lint._undeclared_mathlib_bench_failures(root, roots)
            self.assertEqual(len(failures), 1)
            self.assertIn("undeclared bench source", failures[0])

    def test_reserved_probe_root_may_not_exist_yet(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n",
            )
            self.assertEqual(roots, (root / "bench/HexRCF/ProofProbe",))
            self.assertFalse(roots[0].exists())

    def test_phase4_probe_root_must_exist_and_contain_source(self) -> None:
        for state, setup, message in (
            ("missing", lambda _root: None, "missing proof probe root"),
            (
                "empty",
                lambda root: (root / "bench/HexRCF/ProofProbe").mkdir(
                    parents=True
                ),
                "empty proof probe root",
            ),
        ):
            with self.subTest(state=state):
                tmp, root = self.make_repo()
                with tmp:
                    setup(root)
                    self.write(
                        root,
                        "libraries.yml",
                        "libraries:\n"
                        "  HexRCF:\n"
                        "    deps: []\n"
                        "    mathlib: true\n"
                        "    done_through: 4\n"
                        "    status: active\n"
                        "    proof_probes: [bench/HexRCF/ProofProbe]\n",
                    )
                    with self.assertRaisesRegex(ValueError, message):
                        lint._mathlib_probe_roots(root)

    def test_mathlib_false_owner_does_not_gain_probe_exception(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexCore:\n"
                "    deps: []\n"
                "    mathlib: false\n"
                "    done_through: 3\n"
                "    status: active\n",
            )
            self.write(root, "bench/HexCore/Probe.lean", "import Mathlib\n")
            probe = root / "bench/HexCore/Probe.lean"
            self.assertFalse(lint._is_mathlib_probe_path(probe, root, roots))
            self.assertEqual(lint._find_mathlib_probe_files(root, roots), [])

    def test_manifest_owned_probe_cannot_root_executable(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n",
            )
            target = self.target(
                root,
                "lean_exe sample_bench where\n"
                "  srcDir := \"bench\"\n"
                "  root := `HexRCF.ProofProbe.Probe\n",
            )
            self.write(
                root, "bench/HexRCF/ProofProbe/Probe.lean", "import Mathlib\n"
            )
            self.assertEqual(
                lint._probe_root_path(target, root, roots),
                root / "bench/HexRCF/ProofProbe/Probe.lean",
            )

    def test_malformed_manifest_fails_closed(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            self.write(
                root,
                "libraries.yml",
                "libraries:\n"
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: perhaps\n"
                "    done_through: 3\n"
                "    status: active\n",
            )
            with self.assertRaises(ValueError):
                lint._mathlib_probe_roots(root)

    def test_malformed_probe_schema_fails_closed(self) -> None:
        cases = (
            (
                "    mathlib: false\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n",
                "mathlib is false",
            ),
            (
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/Other/ProofProbe]\n",
                "invalid proof probe path",
            ),
            (
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/*]\n",
                "invalid proof probe path",
            ),
            (
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/Probe.lean]\n",
                "invalid proof probe path",
            ),
            (
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probe: [bench/HexRCF/ProofProbe]\n",
                "unknown fields",
            ),
            (
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF, bench/HexRCF/ProofProbe]\n",
                "overlapping proof probe paths",
            ),
        )
        for fields, message in cases:
            with self.subTest(message=message):
                tmp, root = self.make_repo()
                with tmp:
                    entries = "  HexRCF:\n    deps: []\n" + fields
                    with self.assertRaisesRegex(ValueError, message):
                        self.manifest(root, entries)

    def test_duplicate_manifest_ownership_fails_closed(self) -> None:
        duplicate_library = (
            "  HexRCF:\n"
            "    deps: []\n"
            "    mathlib: true\n"
            "    done_through: 3\n"
            "    status: active\n"
            "  HexRCF:\n"
            "    deps: []\n"
            "    mathlib: false\n"
            "    done_through: 3\n"
            "    status: active\n"
        )
        duplicate_field = (
            "  HexRCF:\n"
            "    deps: []\n"
            "    mathlib: true\n"
            "    mathlib: false\n"
            "    done_through: 3\n"
            "    status: active\n"
        )
        for entries, message in (
            (duplicate_library, "duplicate library entry HexRCF"),
            (duplicate_field, "duplicate HexRCF.mathlib field"),
            (
                duplicate_library.replace("HexRCF", "Hex-RCF"),
                "duplicate library entry Hex-RCF",
            ),
        ):
            with self.subTest(message=message):
                tmp, root = self.make_repo()
                with tmp:
                    with self.assertRaisesRegex(ValueError, message):
                        self.manifest(root, entries)

    def test_probe_root_path_normalizes_src_dir(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n"
                "  HexCore:\n"
                "    deps: []\n"
                "    mathlib: false\n"
                "    done_through: 3\n"
                "    status: active\n",
            )
            (root / "bench/Other").mkdir(parents=True)
            target = self.target(
                root,
                "lean_exe sample_bench where\n"
                "  srcDir := \"bench/Other/..\"\n"
                "  root := `HexRCF.ProofProbe.Probe\n",
            )
            self.write(
                root, "bench/HexRCF/ProofProbe/Probe.lean", "import Mathlib\n"
            )
            self.assertIsNotNone(lint._probe_root_path(target, root, roots))

            (root / "bench/HexRCF").mkdir(parents=True, exist_ok=True)
            target = self.target(
                root,
                "lean_exe sample_bench where\n"
                "  srcDir := \"bench/HexRCF/..\"\n"
                "  root := `HexCore.Probe\n",
            )
            self.write(root, "bench/HexCore/Probe.lean", "import Mathlib\n")
            self.assertIsNone(lint._probe_root_path(target, root, roots))

    def test_probe_root_symlink_outside_bench_is_rejected(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            self.write(
                root,
                "libraries.yml",
                "libraries:\n"
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n",
            )
            self.write(root, "Physical/Probe.lean", "import Mathlib\n")
            (root / "bench/HexRCF").mkdir(parents=True)
            (root / "bench/HexRCF/ProofProbe").symlink_to(
                root / "Physical", target_is_directory=True
            )
            with self.assertRaisesRegex(ValueError, "resolves outside bench"):
                lint._mathlib_probe_roots(root)

    def test_nested_probe_symlink_is_rejected(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            self.write(
                root,
                "libraries.yml",
                "libraries:\n"
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n",
            )
            self.write(root, "Physical/Evil.lean", "import LeanBench\n")
            probe_root = root / "bench/HexRCF/ProofProbe"
            probe_root.mkdir(parents=True)
            (probe_root / "Escape").symlink_to(
                root / "Physical", target_is_directory=True
            )
            with self.assertRaisesRegex(ValueError, "contains symlink"):
                lint._mathlib_probe_roots(root)

    def test_probe_root_path_follows_alias_into_owner(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n",
            )
            self.write(
                root, "bench/HexRCF/ProofProbe/Probe.lean", "import Mathlib\n"
            )
            (root / "Alias").symlink_to(
                root / "bench/HexRCF/ProofProbe", target_is_directory=True
            )
            target = self.target(
                root,
                "lean_exe sample_bench where\n"
                "  srcDir := \"Alias\"\n"
                "  root := `Probe\n",
            )
            self.assertIsNotNone(lint._probe_root_path(target, root, roots))

    def test_probe_main_and_unqualified_clock_variants_are_forbidden(self) -> None:
        main_variants = (
            "@[inline] def main : IO Unit := pure ()\n",
            "partial def main : IO Unit := main\n",
            "opaque main : IO Unit\n",
            "abbrev main := IO Unit\n",
            "def «main» : IO Unit := pure ()\n",
            "def _root_.main : IO Unit := pure ()\n",
            "def _root_.«main» : IO Unit := pure ()\n",
        )
        tmp, root = self.make_repo()
        with tmp:
            for index, source in enumerate(main_variants):
                with self.subTest(source=source.strip()):
                    path = root / f"Main{index}.lean"
                    path.write_text(source, encoding="utf-8")
                    self.assertIn("defines main", lint._probe_violations(path))
            clock = root / "Clock.lean"
            clock.write_text("open IO\n#check monoNanosNow\n", encoding="utf-8")
            self.assertIn(
                "uses an in-process monotonic clock",
                lint._probe_violations(clock),
            )

    def test_probe_local_import_closure_is_build_only(self) -> None:
        tmp, root = self.make_repo()
        with tmp:
            roots = self.manifest(
                root,
                "  HexRCF:\n"
                "    deps: []\n"
                "    mathlib: true\n"
                "    done_through: 3\n"
                "    status: active\n"
                "    proof_probes: [bench/HexRCF/ProofProbe]\n",
            )
            self.write(
                root,
                "bench/HexRCF/ProofProbe/Tactic.lean",
                "import Project.Helper\nimport Mathlib\n",
            )
            helper = root / "Project/Helper.lean"
            self.write(
                root,
                "Project/Helper.lean",
                "import LeanBench\n"
                "setup_fixed_benchmark hidden := 1\n"
                "def main : IO Unit := IO.monoNanosNow *> pure ()\n",
            )
            probes = lint._find_mathlib_probe_files(root, roots)
            self.assertEqual(
                probes, [root / "bench/HexRCF/ProofProbe/Tactic.lean"]
            )
            violations = lint._probe_closure_violations(probes[0], root)
            self.assertEqual(
                violations,
                [
                    (helper, "imports LeanBench"),
                    (helper, "registers a LeanBench benchmark"),
                    (helper, "defines main"),
                    (helper, "uses an in-process monotonic clock"),
                ],
            )
            escaped_clock = root / "EscapedClock.lean"
            escaped_clock.write_text(
                "#check IO.«monoNanosNow»\n#check _root_.IO.monoNanosNow\n",
                encoding="utf-8",
            )
            self.assertIn(
                "uses an in-process monotonic clock",
                lint._probe_violations(escaped_clock),
            )
            helper = root / "Helper.lean"
            helper.write_text(
                "def main' := 1\ndef main! := 1\ndef main? := 1\n",
                encoding="utf-8",
            )
            self.assertNotIn("defines main", lint._probe_violations(helper))

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
