from __future__ import annotations

import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from io import StringIO
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_dag import (
    KNOWN_EXCEPTIONS,
    check_adapter_imports,
    check_sealed_import_all,
    import_roots,
    import_closure_in_library,
    parse_imports,
    main,
    lean_build_roots,
)
from check_phase4 import check_headline_reports
from libgraph import (load_libraries, library_owner_for_path, may_import,
                      reachable_dependencies)


class AdapterOwnershipTest(unittest.TestCase):
    def test_development_adapter_keeps_library_owner(self) -> None:
        libraries = load_libraries()
        self.assertEqual(
            library_owner_for_path(Path("adapters/HexRCF/RealFormula.lean"), libraries),
            "HexRCF",
        )

    def test_adapter_imports_do_not_expand_base_or_published_closure(self) -> None:
        libraries = load_libraries()
        closure = reachable_dependencies(libraries)
        for dependency in ["HexRealAlgebraicMathlib", "HexNumberFieldMathlib"]:
            self.assertTrue(may_import("HexRCF", dependency, libraries, closure, adapter=True))
            self.assertFalse(may_import("HexRCF", dependency, libraries, closure))
            self.assertNotIn(dependency, closure["HexRCF"])
        self.assertFalse(may_import("HexPoly", "HexNumberFieldMathlib", libraries, closure,
                                    adapter=True))
        self.assertFalse(may_import("HexRCF", "HexGraphIso", libraries, closure, adapter=True))

    def test_adapter_dependencies_must_exist(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "libraries.yml"
            manifest.write_text("libraries:\n  HexCore:\n    deps: []\n"
                                "    adapter_deps: [HexMissing]\n    mathlib: false\n"
                                "    done_through: 0\n    status: active\n")
            with self.assertRaisesRegex(ValueError, "unknown library HexMissing"):
                load_libraries(manifest)


class AdapterImportBoundaryTest(unittest.TestCase):
    def test_library_imports_cannot_reach_adapters(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {
                "adapters/HexCore/Optional.lean": "",
                "HexCore.lean": "public import HexCore.Optional\n",
                "HexCore/Proof.lean": "public meta import HexCore.Optional\n",
                "HexCore/Private.lean": "private import all HexCore.Optional -- hidden facet\n",
                "HexCore/Many.lean": "import HexCore.Safe HexCore.Optional\n",
                "HexOther/Use.lean": "import HexCore.Optional\n",
                "adapters/HexOther/Use.lean": "import HexCore.Optional\n",
                "conformance/HexCore/Use.lean": "import HexCore.Optional\n",
                "HexManual/Use.lean": "import HexCore.Optional\n",
                "HexCore/Safe.lean": "import Mathlib.Basic\n",
            }
            for name, text in sources.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            errors = check_adapter_imports(root, list(map(Path, sources)),
                                           {"HexCore", "HexOther", "HexManual"})
            self.assertEqual(len(errors), 5)
            self.assertTrue(all("development adapter HexCore.Optional" in e for e in errors))
            self.assertFalse(any(e.startswith(("adapters/", "conformance/", "HexManual/"))
                                 for e in errors))


class ExternalProofDependencyTest(unittest.TestCase):
    def test_tau_ceti_requires_a_mathlib_library(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "libraries.yml").write_text(
                "libraries:\n"
                "  HexCore:\n    deps: []\n    mathlib: false\n"
                "    done_through: 0\n    status: active\n"
                "  HexCoreMathlib:\n    deps: [HexCore]\n    mathlib: true\n"
                "    done_through: 0\n    status: active\n")
            names = {"HexCore", "HexCoreMathlib"} | KNOWN_EXCEPTIONS
            for name in names:
                (root / f"{name}.lean").write_text("")
            (root / "lakefile.lean").write_text(
                "\n".join(f"lean_lib {name} where" for name in sorted(names)))
            (root / "HexCoreMathlib.lean").write_text(
                "public import TauCeti.Algebra.Polynomial.Sturm.Infinity\n")
            with patch("check_dag.__file__", str(root / "scripts/check_dag.py")):
                self.assertEqual(main(), 0)
                for dependency in ["TauCeti", "Mathlib"]:
                    with self.subTest(dependency=dependency):
                        (root / "HexCore.lean").write_text(f"public import {dependency}.Basic\n")
                        errors = StringIO()
                        with redirect_stderr(errors):
                            self.assertEqual(main(), 1)
                        self.assertIn(f"imports {dependency} but HexCore is not a mathlib bridge",
                                      errors.getvalue())


class MetaImportTest(unittest.TestCase):
    def test_meta_imports_are_edges(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "HexOwner.lean"
            path.write_text(
                "public meta import HexDependency.Tactic\n"
                "meta import HexDependency.Runtime\n",
                encoding="utf-8",
            )

            self.assertEqual(
                parse_imports(path),
                ["HexDependency.Tactic", "HexDependency.Runtime"],
            )
            self.assertEqual(
                import_roots("public meta import HexDependency.Tactic"),
                ["HexDependency"],
            )
            self.assertEqual(
                import_roots("meta import HexDependency.Runtime"),
                ["HexDependency"],
            )
            self.assertEqual(
                import_roots("meta public import HexDependency.Invalid"), []
            )


class ImportAllClosureTest(unittest.TestCase):
    def test_optional_library_entries_are_explicit_roots(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            lakefile = Path(directory) / "lakefile.lean"
            lakefile.write_text(
                "lean_lib HexCore where\n"
                "  roots := #[`HexCore,\n    `HexCore.Optional]\n"
                "  globs := #[.submodules `HexCore]\n"
                "lean_exe smoke where\n  root := `Smoke\n")
            self.assertEqual(lean_build_roots(lakefile),
                             {"HexCore", "HexCore.Optional", "Smoke"})

    def test_private_facets_are_build_dependencies(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "HexCore").mkdir()
            (root / "HexCore.lean").write_text("public import HexCore.Entry\n")
            (root / "HexCore/Entry.lean").write_text(
                "import all HexCore.Proof\nprivate import all HexCore.Helper -- private facet\n")
            (root / "HexCore/Proof.lean").write_text("meta import all HexCore.Meta\n")
            (root / "HexCore/Helper.lean").write_text("")
            (root / "HexCore/Meta.lean").write_text("")
            self.assertEqual(import_closure_in_library(root, "HexCore", "HexCore"),
                             {"HexCore", "HexCore.Entry", "HexCore.Proof",
                              "HexCore.Helper", "HexCore.Meta"})


class SealedImportAllTest(unittest.TestCase):
    def test_ownerless_roots_are_checked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cases = [
                (Path("conformance/HexInterval/BypassExecutable.lean"),
                    "HexInterval.Executable"),
                (Path("bench/HexInterval/BypassExecutable.lean"),
                    "HexInterval.Executable"),
                (Path("conformance/HexInterval/BypassRuntime.lean"),
                    "HexInterval.Runtime"),
                (Path("bench/HexInterval/BypassRuntime.lean"),
                    "HexInterval.Runtime"),
                (Path("conformance/HexInterval/BypassRuntimeController.lean"),
                    "HexInterval.RuntimeController"),
                (Path("bench/HexInterval/BypassRuntimeController.lean"),
                    "HexInterval.RuntimeController"),
                (Path("conformance/HexInterval/Bypass.lean"), "HexInterval.Search"),
                (Path("bench/HexInterval/Bypass.lean"), "HexInterval.Search"),
                (Path("conformance/HexIntervalMathlib/Bypass.lean"),
                    "HexIntervalMathlib.Proof"),
                (Path("bench/HexIntervalMathlib/Bypass.lean"),
                    "HexIntervalMathlib.Proof"),
                (Path("conformance/HexIntervalMathlib/BypassRuntimeProof.lean"),
                    "HexIntervalMathlib.RuntimeProof"),
                (Path("bench/HexIntervalMathlib/BypassRuntimeProof.lean"),
                    "HexIntervalMathlib.RuntimeProof"),
                (Path("conformance/HexIntervalMathlib/BypassRuntimeTerminal.lean"),
                    "HexIntervalMathlib.RuntimeTerminal"),
                (Path("bench/HexIntervalMathlib/BypassRuntimeTerminal.lean"),
                    "HexIntervalMathlib.RuntimeTerminal"),
            ]
            files = [path for path, _ in cases]
            for path, module in cases:
                full_path = root / path
                full_path.parent.mkdir(parents=True, exist_ok=True)
                full_path.write_text(f"import all {module}\n", encoding="utf-8")

            self.assertEqual(
                check_sealed_import_all(root, files),
                [
                    "conformance/HexInterval/BypassExecutable.lean:1 uses `import all "
                    "HexInterval.Executable` outside its exact trusted-internals allowlist",
                    "bench/HexInterval/BypassExecutable.lean:1 uses `import all "
                    "HexInterval.Executable` outside its exact trusted-internals allowlist",
                    "conformance/HexInterval/BypassRuntime.lean:1 uses `import all "
                    "HexInterval.Runtime` outside its exact trusted-internals allowlist",
                    "bench/HexInterval/BypassRuntime.lean:1 uses `import all "
                    "HexInterval.Runtime` outside its exact trusted-internals allowlist",
                    "conformance/HexInterval/BypassRuntimeController.lean:1 uses `import all "
                    "HexInterval.RuntimeController` outside its exact trusted-internals "
                    "allowlist",
                    "bench/HexInterval/BypassRuntimeController.lean:1 uses `import all "
                    "HexInterval.RuntimeController` outside its exact trusted-internals "
                    "allowlist",
                    "conformance/HexInterval/Bypass.lean:1 uses `import all "
                    "HexInterval.Search` outside its exact trusted-internals allowlist",
                    "bench/HexInterval/Bypass.lean:1 uses `import all "
                    "HexInterval.Search` outside its exact trusted-internals allowlist",
                    "conformance/HexIntervalMathlib/Bypass.lean:1 uses `import all "
                    "HexIntervalMathlib.Proof` outside its exact trusted-internals allowlist",
                    "bench/HexIntervalMathlib/Bypass.lean:1 uses `import all "
                    "HexIntervalMathlib.Proof` outside its exact trusted-internals allowlist",
                    "conformance/HexIntervalMathlib/BypassRuntimeProof.lean:1 uses "
                    "`import all HexIntervalMathlib.RuntimeProof` outside its exact "
                    "trusted-internals allowlist",
                    "bench/HexIntervalMathlib/BypassRuntimeProof.lean:1 uses "
                    "`import all HexIntervalMathlib.RuntimeProof` outside its exact "
                    "trusted-internals allowlist",
                    "conformance/HexIntervalMathlib/BypassRuntimeTerminal.lean:1 uses "
                    "`import all HexIntervalMathlib.RuntimeTerminal` outside its exact "
                    "trusted-internals allowlist",
                    "bench/HexIntervalMathlib/BypassRuntimeTerminal.lean:1 uses "
                    "`import all HexIntervalMathlib.RuntimeTerminal` outside its exact "
                    "trusted-internals allowlist",
                ],
            )


class HeadlineReportTest(unittest.TestCase):
    def write_manifest(self, root: Path, mathlib: bool) -> None:
        (root / "libraries.yml").write_text(
            "libraries:\n"
            "  HexFoo:\n"
            "    deps: []\n"
            f"    mathlib: {'true' if mathlib else 'false'}\n"
            "    done_through: 4\n"
            "    status: active\n",
            encoding="utf-8",
        )

    def test_compiled_library_needs_report(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_manifest(root, mathlib=False)
            _, error = check_headline_reports(root)
            self.assertIn("HexFoo: missing Phase-4 headline report", error)

    def test_mathlib_library_needs_no_report(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_manifest(root, mathlib=True)
            _, error = check_headline_reports(root)
            self.assertIsNone(error)


if __name__ == "__main__":
    unittest.main()
