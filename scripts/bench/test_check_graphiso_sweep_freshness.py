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
        return check.independent_target_additions(before, after, {"HexOther"},
                                                  {"HexGraphIso", "Init", "Lean", "Std", "Lake"})

    def test_plain_executable_append(self):
        self.assertTrue(self.allowed(BASE, BASE + "\n" + EXE))

    def test_literal_library_insertion(self):
        self.assertTrue(self.allowed(BASE + "\n" + NEXT,
                                     BASE + "\n" + LIB + "\n" + NEXT))
        self.assertTrue(self.allowed(BASE, BASE + "\n" + LIB.replace("roots", "globs")))

    def test_globs_do_not_override_default_roots(self):
        for name in ("HexGraphIso", "Init", "Lean", "Std", "Lake"):
            self.assertFalse(self.allowed(BASE, BASE + "\n" + LIB.replace("roots", "globs")
                                          .replace("IndependentSupport", name)))

    def test_sweep_selector_uses_the_same_allowance(self):
        from scripts.bench import graphiso_pernode_fit as fit
        from types import SimpleNamespace
        observation = SimpleNamespace(label="covered.jsonl")
        with patch.object(check, "observations", return_value=([observation], [])), \
                patch.object(fit.freshness, "assess", return_value=SimpleNamespace(
                    matched=None, baseline=observation, fresh=True)) as assess:
            self.assertEqual(fit.current_sweep(), fit.RESULTS / observation.label)
            self.assertIs(assess.call_args.kwargs["allow"], check.runtime_neutral)

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
        self.assertTrue({"Hex", "HexBasic", "HexGraph", "HexGraphIso", "HexMatrix"}
                        <= prefixes)
        self.assertNotIn("HexNumberFieldTower", prefixes)
        self.assertNotIn("HexRationalFn", prefixes)

    def test_nested_init_keeps_toolchain_imports_external(self):
        sources = {
            Path("HexGraphIso.lean"): ["root"],
            Path("HexGraphIso/Cactus.lean"): ["driver"],
            Path("Init/Present.lean"): ["shadow"],
            Path("Hidden/Local.lean"): ["local"],
        }
        blobs = {
            "root": "import Init.Data.List.Sort.Basic\nimport Init.Present\n",
            "driver": "",
            "shadow": "import Hidden.Local\n",
            "local": "",
        }
        with patch.object(check, "index_lean_sources", return_value=(
                sources, {"HexGraphIso", "Init", "Hidden"})), \
                patch.object(check.freshness, "blob_text", side_effect=blobs.__getitem__):
            prefixes = check.graph_import_prefixes()
            self.assertIsNotNone(prefixes)
            self.assertIn("Hidden", prefixes)
            self.assertIn("Init", prefixes)
            blobs["root"] = "import Hidden.Missing\n"
            self.assertIsNone(check.graph_import_prefixes())

    def test_lake_allowance_guards_and_imported_namespace(self):
        old, new = "old-lake", "new-lake"
        difference = check.freshness.Difference(
            "lakefile.lean", old, new, "100644", "100644")
        before, after = BASE, BASE + "\n" + EXE
        listing = "100644 source 0\tHexOther.lean\n"
        def fake_git(*args):
            if args == ("cat-file", "blob", old):
                return before
            if args == ("cat-file", "blob", new):
                return after
            if args[:3] == ("ls-files", "-s", "--"):
                return listing
            raise AssertionError(args)
        with patch.object(check.freshness, "git", side_effect=fake_git), \
                patch.object(check, "graph_import_prefixes",
                             return_value={"HexGraphIso"}):
            self.assertTrue(check.independent_lake_targets(difference))
        with patch.object(check.freshness, "git", side_effect=fake_git), \
                patch.object(check, "graph_import_prefixes",
                             return_value={"HexGraphIso", "HexOther"}):
            self.assertFalse(check.independent_lake_targets(difference))
        with patch.object(check, "graph_import_prefixes", return_value=None):
            self.assertFalse(check.independent_lake_targets(difference))
        self.assertFalse(check.independent_lake_targets(
            check.freshness.Difference("other", old, new, "100644", "100644")))
        self.assertFalse(check.independent_lake_targets(
            check.freshness.Difference("lakefile.lean", old, new, "100644", "100755")))

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
            blobs = {}
            listing = []
            for number, (name, text) in enumerate(files.items()):
                blob = f"blob{number}"
                blobs[blob] = text
                listing.append(f"100644 {blob} 0\t{name}")
            def fake_git(*args):
                if args[:3] == ("ls-files", "-s", "--"):
                    return "\n".join(listing) + "\n"
                if args[:2] == ("cat-file", "blob"):
                    return blobs[args[2]]
                raise AssertionError(args)
            with patch.object(check.freshness, "git", side_effect=fake_git):
                self.assertEqual(check.graph_import_prefixes(),
                                 {"HexGraphIso", "HexHelper", "Lean", "HexOther",
                                  "Init", "Std", "Lake"})
                blobs["blob0"] = "import HexHelper.«Core»\n"
                self.assertIsNone(check.graph_import_prefixes())

    def test_closure_reads_index_and_all_source_directories(self):
        files = {
            "HexGraphIso.lean": "import Hidden.Entry\n",
            "bench/HexGraphIso/Cactus.lean": "import HexGraphIso\n",
            "examples/Hidden/Entry.lean": "import HexOther.Reached\n",
            "generated/HexOther/Reached.lean": "import Std\n",
        }
        blobs = {}
        listing = []
        for number, (name, body) in enumerate(files.items()):
            blob = f"blob{number}"
            blobs[blob] = body
            listing.append(f"100644 {blob} 0\t{name}")
        def fake_git(*args):
            if args[:3] == ("ls-files", "-s", "--"):
                return "\n".join(listing) + "\n"
            if args[:2] == ("cat-file", "blob"):
                return blobs[args[2]]
            raise AssertionError(args)
        with patch.object(check.freshness, "git", side_effect=fake_git):
            self.assertTrue({"Hidden", "HexOther"} <= check.graph_import_prefixes())


if __name__ == "__main__":
    unittest.main()
