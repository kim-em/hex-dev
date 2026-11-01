"""Reject patched comparator sources and retain effective compiler/ISA settings."""
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.bench.groebner_freeze import msolve_build


class ComparatorBuildTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "src/neogb").mkdir(parents=True)
        flags = "CC = cc\nCFLAGS = -O3\nSIMD_FLAGS = -mavx512f\nCPUEXT_FLAGS = -mbmi\nOPENMP_CFLAGS = \n"
        for name in ["Makefile", "src/neogb/Makefile"]:
            (self.root / name).write_text(flags)
        configure = self.root / "config.status"
        configure.write_text("#!/bin/sh\nprintf '%s\\n' '--disable-openmp'\n")
        configure.chmod(0o755)
        self.git("init", "--quiet")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "fixture")

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, stderr=subprocess.STDOUT)

    def test_clean_source_records_isa_and_openmp(self):
        result = msolve_build(self.root)
        self.assertEqual(result["tracked_status"], "")
        self.assertEqual(result["tracked_diff_sha256"], hashlib.sha256(b"").hexdigest())
        self.assertEqual(result["configure"], "--disable-openmp")
        for flags in result["flags"].values():
            self.assertIn("SIMD_FLAGS = -mavx512f", flags)
            self.assertIn("CPUEXT_FLAGS = -mbmi", flags)
            self.assertIn("OPENMP_CFLAGS = ", flags)

    def test_staged_and_unstaged_patches_are_rejected(self):
        (self.root / "Makefile").write_text("CC = patched\n")
        with self.assertRaisesRegex(ValueError, "tracked modifications"):
            msolve_build(self.root)
        self.git("add", "Makefile")
        with self.assertRaisesRegex(ValueError, "tracked modifications"):
            msolve_build(self.root)
        observed = msolve_build(self.root, require_clean=False)
        self.assertNotEqual(observed["tracked_diff_sha256"], hashlib.sha256(b"").hexdigest())


if __name__ == "__main__":
    unittest.main()
