from __future__ import annotations

import sys
import tempfile
import unittest
from collections import OrderedDict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_dag import check_correspondence_only, check_sealed_import_all
from check_phase4 import check_headline_reports
from libgraph import LibraryInfo, load_libraries


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


class CorrespondenceOnlyTest(unittest.TestCase):
    def write_manifest(self, root: Path, bridge_fields: str) -> Path:
        path = root / "libraries.yml"
        path.write_text(
            "libraries:\n"
            "  HexCore:\n"
            "    deps: []\n"
            "    mathlib: false\n"
            "    done_through: 3\n"
            "    status: active\n"
            "  HexBridge:\n"
            "    deps: [HexCore]\n"
            "    mathlib: true\n"
            f"{bridge_fields}",
            encoding="utf-8",
        )
        return path

    def test_registry_accepts_legal_classification(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = self.write_manifest(
                root,
                "    correspondence_only: true\n"
                "    done_through: 4\n"
                "    status: active\n",
            )
            self.assertTrue(load_libraries(manifest)["HexBridge"].correspondence_only)

    def test_registry_rejects_incompatible_classification(self) -> None:
        cases = {
            "non-mathlib": (
                "    correspondence_only: true\n"
                "    done_through: 4\n"
                "    status: active\n",
                "declares correspondence_only but mathlib is false",
            ),
            "proof probes": (
                "    correspondence_only: true\n"
                "    proof_probes: [bench/HexBridge/ProofProbe]\n"
                "    done_through: 4\n"
                "    status: active\n",
                "declares correspondence_only and proof_probes",
            ),
            "phase4": (
                "    correspondence_only: true\n"
                "    done_through: 4\n"
                "    status: active\n"
                "    phase4:\n"
                "      input_families:\n"
                "        - name: owned\n"
                "          description: owned surface\n",
                "declares correspondence_only and a phase4 block",
            ),
        }
        for label, (fields, message) in cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest = self.write_manifest(root, fields)
                if label == "non-mathlib":
                    text = manifest.read_text(encoding="utf-8")
                    manifest.write_text(
                        text.replace(
                            "  HexBridge:\n    deps: [HexCore]\n    mathlib: true",
                            "  HexBridge:\n    deps: [HexCore]\n    mathlib: false",
                        ),
                        encoding="utf-8",
                    )
                with self.assertRaisesRegex(ValueError, message):
                    load_libraries(manifest)

    def correspondence_tree(self, root: Path) -> OrderedDict[str, LibraryInfo]:
        (root / "lakefile.lean").write_text("", encoding="utf-8")
        spec_dir = root / "HexBridge" / "SPEC"
        spec_dir.mkdir(parents=True)
        (spec_dir / "hex-bridge.md").write_text(
            "# bridge\n\n"
            "`correspondence-only-layer`\n\n"
            "Computational conformance owner: `HexCore`\n"
            "Computational performance owner: `HexCore`\n",
            encoding="utf-8",
        )
        return OrderedDict(
            HexCore=LibraryInfo("HexCore", (), False, 4, "active"),
            HexBridge=LibraryInfo(
                "HexBridge", ("HexCore",), True, 4, "active",
                correspondence_only=True,
            ),
        )

    def test_repository_state_accepts_clean_classification(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            libraries = self.correspondence_tree(root)
            self.assertEqual(
                check_correspondence_only(root, libraries, root / "lakefile.lean"), []
            )

    def test_repository_state_rejects_owned_targets_and_bad_spec(self) -> None:
        cases = {
            "conformance": (
                Path("conformance/HexBridge/Conformance.lean"),
                "owns conformance source conformance/HexBridge/Conformance.lean",
            ),
            "named conformance": (
                Path("conformance/HexBridge/TransportConformance.lean"),
                "owns conformance source conformance/HexBridge/TransportConformance.lean",
            ),
            "bench": (
                Path("bench/HexBridge/Bench.lean"),
                "owns bench source bench/HexBridge/Bench.lean",
            ),
        }
        for label, (relative, message) in cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                libraries = self.correspondence_tree(root)
                path = root / relative
                path.parent.mkdir(parents=True)
                path.write_text("", encoding="utf-8")
                errors = check_correspondence_only(root, libraries, root / "lakefile.lean")
                self.assertTrue(any(message in error for error in errors), errors)

        lake_cases = {
            "conformance target": (
                "lean_lib HexConformance where\n"
                "  globs := #[`HexBridge.TransportConformance].map Glob.one\n",
                "a Lake target names an owned conformance module",
            ),
            "benchmark executable": (
                "lean_exe hexbridge_bench where\n"
                "  srcDir := \"bench\"\n"
                "  root := `Other.Main\n",
                "owns compiled benchmark target hexbridge_bench",
            ),
            "benchmark module": (
                "lean_lib Other where\n"
                "  globs := #[`HexBridge.Bench].map Glob.one\n",
                "a Lake target names HexBridge.Bench",
            ),
        }
        for label, (lake_text, message) in lake_cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                libraries = self.correspondence_tree(root)
                lakefile = root / "lakefile.lean"
                lakefile.write_text(lake_text, encoding="utf-8")
                errors = check_correspondence_only(root, libraries, lakefile)
                self.assertTrue(any(message in error for error in errors), errors)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            libraries = self.correspondence_tree(root)
            spec = root / "HexBridge/SPEC/hex-bridge.md"
            spec.write_text("# bridge\n", encoding="utf-8")
            errors = check_correspondence_only(root, libraries, root / "lakefile.lean")
            self.assertTrue(any("does not declare correspondence-only-layer" in e for e in errors))
            self.assertTrue(any("does not identify computational conformance owners" in e for e in errors))
            self.assertTrue(any("does not identify computational performance owners" in e for e in errors))

    def test_phase4_report_exemption_is_explicit(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_manifest(
                root,
                "    done_through: 4\n"
                "    status: active\n",
            )
            _, error = check_headline_reports(root)
            self.assertIn("HexBridge: missing Phase-4 headline report", error)

            self.write_manifest(
                root,
                "    correspondence_only: true\n"
                "    done_through: 4\n"
                "    status: active\n",
            )
            _, error = check_headline_reports(root)
            self.assertIsNone(error)


if __name__ == "__main__":
    unittest.main()
