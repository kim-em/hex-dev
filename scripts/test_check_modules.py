"""Regression coverage for the source-only module header check."""
import unittest
from pathlib import Path

from scripts.check_modules import first_token, is_source


class ModuleHeaderTests(unittest.TestCase):
    def test_header(self):
        for text in ("module\nimport Init", "\ufeffmodule", "module-- comment\n", "module/- note -/"):
            self.assertEqual(first_token(text), "module")

    def test_comments(self):
        self.assertEqual(first_token("/- copyright /- nested module -/ -/\n-- module\n module"), "module")

    def test_false_headers(self):
        for text in ("import Init\nmodule", "-- module\nimport Init", '/- module -/\n"module"',
                     "moduleName", "module'", "module₁", "«module»", "", "/- unterminated"):
            self.assertNotEqual(first_token(text), "module")

    def test_scope(self):
        for path in ("HexIntFactor/Export.lean", "bench/A.lean", "conformance/A.lean",
                     "HexManual/A.lean", "Examples/A.lean", "experiments/A.lean", "scripts/A.lean"):
            self.assertTrue(is_source(Path(path)))
        for path in ("lakefile.lean", "bench/lakefile.lean", "reports/retained.lean", "template.lean.in"):
            self.assertFalse(is_source(Path(path)))


if __name__ == "__main__":
    unittest.main()
