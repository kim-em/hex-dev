from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_dag import check_sealed_import_all


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


if __name__ == "__main__":
    unittest.main()
