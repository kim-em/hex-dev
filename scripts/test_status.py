#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import status


ROOT = Path(__file__).resolve().parent.parent


class LeanLibModulesTests(unittest.TestCase):
    def test_reads_globs_and_ignores_comments(self) -> None:
        text = (
            "lean_lib Other where\n"
            "  globs := #[`Examples.Release2]\n"
            "\n"
            "lean_lib HexReleaseExamples where\n"
            "  -- `Examples.Release9 is retired\n"
            "  globs := #[`Examples.Release10,\n"
            "    `Examples.RowReduce]\n"
            "\n"
            "lean_exe foo where\n"
            "  root := `Examples.Release1\n"
        )
        modules = status.lean_lib_modules(text, "HexReleaseExamples")
        self.assertEqual(modules, ["Examples.Release10", "Examples.RowReduce"])
        self.assertNotIn("Examples.Release1", modules)

    def test_missing_or_duplicate_block_fails(self) -> None:
        with self.assertRaises(ValueError):
            status.lean_lib_modules("lean_lib Other where\n  globs := #[`A]\n", "HexReleaseExamples")
        block = "lean_lib HexReleaseExamples where\n  globs := #[`A]\n"
        with self.assertRaises(ValueError):
            status.lean_lib_modules(block + block, "HexReleaseExamples")


class RepositoryTests(unittest.TestCase):
    def test_release_examples_are_ci_covered(self) -> None:
        modules = status.lean_lib_modules((ROOT / "lakefile.lean").read_text(), status.EXAMPLES_LIB)
        for release in status.RELEASE_LIBRARIES:
            if (ROOT / "Examples" / f"Release{release}.lean").exists():
                self.assertIn(f"Examples.Release{release}", modules)
        workflow = (ROOT / status.CI_WORKFLOW).read_text()
        self.assertTrue(status.ci_builds_lib(workflow, status.EXAMPLES_LIB))


if __name__ == "__main__":
    unittest.main()
