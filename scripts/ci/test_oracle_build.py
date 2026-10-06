"""Check native oracle preparation without running fixtures or dependencies."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / "scripts/ci/run_oracles.sh"


class OracleBuildTests(unittest.TestCase):
    def targets(self, owners=None):
        registry = subprocess.check_output(["bash", str(RUNNER), "--list"], text=True)
        return [row.split("|")[1] for row in registry.splitlines()
                if owners is None or row.split("|")[0] in owners]

    def prepare(self, owners="", status=0):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            calls = root / "calls"
            lake = root / "lake"
            lake.write_text('#!/bin/sh\nprintf "%s\\n" "$@" > "$BUILD_ONLY_LOG"\n'
                            'exit "$BUILD_ONLY_STATUS"\n')
            lake.chmod(0o755)
            # Build preparation must not require the independent Python oracles.
            python = root / "python3"
            python.write_text("#!/bin/sh\nexit 99\n")
            python.chmod(0o755)
            env = dict(os.environ, PATH=f"{root}:{os.environ['PATH']}",
                       HEX_LIBRARY_FILTER=owners, HEX_REQUIRE_ORACLES="1",
                       BUILD_ONLY_LOG=str(calls), BUILD_ONLY_STATUS=str(status))
            result = subprocess.run(["bash", str(RUNNER), "--build-only"],
                                    env=env, text=True, capture_output=True)
            args = calls.read_text().splitlines() if calls.exists() else []
            return result, args

    def test_all_registered_emitters_and_native_checks(self):
        result, args = self.prepare()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(args, ["build", *self.targets(),
                                "hexrealclosure_trivial_tests", "hexrealclosure_codec_bytes"])

    def test_selected_factorization_emitter(self):
        result, args = self.prepare("HexIntFactor")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(args, ["build", "hexintfactor_emit_fixtures"])

    def test_selected_shared_native_checks(self):
        owners = {"HexRealClosure", "HexSignDet"}
        result, args = self.prepare(" ".join(sorted(owners)))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(args, ["build", *self.targets(owners),
                                "hexrealclosure_trivial_tests", "hexrealclosure_codec_bytes"])

    def test_build_failure_stops_preparation(self):
        result, _ = self.prepare("HexIntFactor", status=71)
        self.assertEqual(result.returncode, 1)
        self.assertIn("FAIL: building emit executables", result.stderr)

    def test_unknown_mode_is_rejected(self):
        result = subprocess.run(["bash", str(RUNNER), "--invalid"],
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 2)


if __name__ == "__main__":
    unittest.main()
