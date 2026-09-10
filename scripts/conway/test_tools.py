"""Regression checks for source provenance and the offline input boundary."""

import contextlib
import io
import hashlib
import subprocess
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate
from provenance import dependencies, sources, imports
from verify_provenance import verify


class ConwayToolsTest(unittest.TestCase):
    def test_shared_cache_mismatch(self):
        with tempfile.TemporaryDirectory() as directory:
            here = Path(directory)
            data = json.loads((generate.HERE / "candidates.json").read_text())
            row = next(r for r in data["entries"] if (r["p"], r["n"]) == (2, 1))
            row["coeffs"] = [0, 1]
            (here / "candidates.json").write_text(json.dumps(data))
            with patch.object(generate, "HERE", here), patch.object(
                generate, "ROOT", generate.ROOT
            ):
                with patch.object(sys, "argv", ["generate.py", "--check"]):
                    with self.assertRaisesRegex(
                        ValueError, "Shared factorization corpus"
                    ):
                        generate.main()

    def test_duplicate_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            scope = Path(directory) / "scope.json"
            scope.write_text("[[2, 1], [2, 1]]")
            with patch.object(generate, "ROOT", generate.ROOT):
                with patch.object(
                    sys, "argv", ["generate.py", "--check", "--scope", str(scope)]
                ):
                    with self.assertRaisesRegex(ValueError, "Duplicate scope"):
                        generate.main()

    def test_dependency_closure_records_primality(self):
        paths = dependencies(sources(["HexConway"]))
        self.assertIn(Path("HexBerlekamp/CertificateSyntax.lean"), paths)
        self.assertIn(Path("HexPrimality/Cert.lean"), paths)
        self.assertIn(Path("HexArith/Nat/Prime.lean"), paths)
        self.assertFalse(any(p.parts[0] == "HexConway" for p in paths))

    def test_import_qualifiers(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Imports.lean"
            path.write_text(
                "\n".join(
                    [
                        "import A",
                        "public import B",
                        "private import C",
                        "meta import D",
                        "public meta import E",
                        "private meta import F",
                        "public import all G",
                        "meta import all H",
                        "public meta import all I",
                        "  import J -- trailing comment",
                    ]
                )
            )
            self.assertEqual(imports(path), list("ABCDEFGHIJ"))

    def test_provenance_and_mismatch(self):
        content = subprocess.check_output(["git", "show", "HEAD:lean-toolchain"])
        with tempfile.TemporaryDirectory() as directory:
            data = {
                "commit": "HEAD",
                "source_sha256": {
                    "lean-toolchain": hashlib.sha256(content).hexdigest()
                },
            }
            path = Path(directory) / "report.json"
            path.write_text(json.dumps(data))
            with contextlib.redirect_stdout(io.StringIO()):
                verify(path)
            binary = Path(directory) / "binary"
            binary.write_bytes(b"measured executable")
            data["binary_sha256"] = hashlib.sha256(binary.read_bytes()).hexdigest()
            path.write_text(json.dumps(data))
            with contextlib.redirect_stdout(io.StringIO()):
                verify(path, binary=binary)
            binary.write_bytes(b"different executable")
            with self.assertRaisesRegex(ValueError, "benchmark binary differs"):
                verify(path, binary=binary)
            data["source_sha256"]["lean-toolchain"] = "0" * 64
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "source differs"):
                verify(path)


if __name__ == "__main__":
    unittest.main()
