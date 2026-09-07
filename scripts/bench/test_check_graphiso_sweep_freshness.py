#!/usr/bin/env python3
"""Fail-closed checks for independent Lake target additions."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.bench import check_graphiso_sweep_freshness as check

BASE = "lean_exe measured where\n  root := `HexGraphIso.Cactus\n"
EXE = ('lean_exe independent where\n  srcDir := "bench"\n'
       '  root := `HexOther.Check\n')
LIB = ('lean_lib IndependentSupport where\n  srcDir := "bench"\n'
       '  roots := #[`HexOther.First,\n    `HexOther.Second]\n')
NEXT = 'lean_exe next where\n  root := `Main\n'


class IndependentTargetTests(unittest.TestCase):
    def allowed(self, before, after):
        return check.independent_target_additions(before, after, {"HexOther"})

    def test_plain_executable_append(self):
        self.assertTrue(self.allowed(BASE, BASE + "\n" + EXE))

    def test_literal_library_insertion(self):
        self.assertTrue(self.allowed(BASE + "\n" + NEXT,
                                     BASE + "\n" + LIB + "\n" + NEXT))
        self.assertTrue(self.allowed(BASE, BASE + "\n" + LIB.replace("roots", "globs")))

    def test_multiple_new_targets(self):
        self.assertTrue(self.allowed(BASE, BASE + "\n" + LIB + "\n" + EXE))

    def test_existing_configuration_change(self):
        self.assertFalse(self.allowed(BASE, BASE.replace("Cactus", "Bench") + "\n" + EXE))

    def test_added_build_flags(self):
        self.assertFalse(self.allowed(BASE, BASE + "\n" + EXE + '  moreLeanArgs := #["-O3"]\n'))

    def test_default_target_attribute(self):
        self.assertFalse(self.allowed(BASE, BASE + "\n@[default_target]\n" + EXE))

    def test_existing_attribute_cannot_move(self):
        before = BASE + "\n@[default_target]\n" + NEXT
        after = BASE + "\n@[default_target]\n" + EXE + "\n" + NEXT
        self.assertFalse(self.allowed(before, after))

    def test_existing_scoped_option_cannot_move(self):
        before = BASE + "\nset_option maxRecDepth 100 in\n" + NEXT
        after = BASE + "\nset_option maxRecDepth 100 in\n" + EXE + "\n" + NEXT
        self.assertFalse(self.allowed(before, after))

    def test_existing_field_cannot_be_stolen(self):
        field = '  moreLeanArgs := #["-O3"]\n'
        self.assertFalse(self.allowed(BASE + field + "\n" + NEXT,
                                     BASE + "\n" + EXE + field + "\n" + NEXT))

    def test_reachable_namespace_cannot_gain_an_owner(self):
        self.assertFalse(self.allowed(BASE, BASE + "\n" + EXE.replace("HexOther", "HexGraphIso")))

    def test_target_name_cannot_be_reused(self):
        self.assertFalse(self.allowed(BASE, BASE + "\n" + EXE.replace("independent", "measured")))
        self.assertFalse(self.allowed(BASE, BASE + "\n" + EXE + "\n" + EXE))

    def test_fields_must_be_literal_and_match_target_kind(self):
        for changed in (EXE.replace("`HexOther.Check", "(by exact `HexOther.Check)"),
                        EXE.replace("root :=", "roots :="),
                        LIB.replace("roots :=", "root :="),
                        LIB.replace("`HexOther.First", ".submodules `HexOther.First"),
                        EXE.replace('"bench"', '"."')):
            with self.subTest(changed=changed):
                self.assertFalse(self.allowed(BASE, BASE + "\n" + changed))

    def test_removed_target_is_not_an_addition(self):
        self.assertFalse(self.allowed(BASE + "\n" + EXE, BASE))

    def test_real_driver_namespaces_are_independent(self):
        prefixes = check.graph_import_prefixes()
        self.assertIsNotNone(prefixes)
        self.assertIn("HexGraphIso", prefixes)
        self.assertNotIn("HexNumberFieldTower", prefixes)
        self.assertNotIn("HexRationalFn", prefixes)

    def test_import_all_and_ambiguous_local_locations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = {"HexGraphIso.lean": "public import all HexHelper.Core\n",
                     "bench/HexGraphIso/Cactus.lean": "import HexGraphIso\n",
                     "HexHelper/Core.lean": "import Lean\n",
                     "bench/HexHelper/Core.lean": "import HexOther.Used\n"}
            for name, text in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            with patch.object(check.freshness, "ROOT", root):
                self.assertEqual(check.graph_import_prefixes(),
                                 {"HexGraphIso", "HexHelper", "Lean", "HexOther"})
                (root / "HexGraphIso.lean").write_text("import HexHelper.«Core»\n")
                self.assertIsNone(check.graph_import_prefixes())


if __name__ == "__main__":
    unittest.main()
