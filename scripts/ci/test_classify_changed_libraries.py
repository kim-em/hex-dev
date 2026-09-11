from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from classify_changed_libraries import classify_paths, load_oracle_owners


ORACLE_OWNERS = {
    "scripts/oracle/roots_flint.py": {"HexRoots"},
    "scripts/oracle/matrix_flint.py": {"HexBareiss", "HexDeterminant"},
}


class ClassifyChangedLibrariesTests(unittest.TestCase):
    def classify(self, *paths: str):
        return classify_paths(list(paths), oracle_owners=ORACLE_OWNERS)

    def test_library_source_selects_only_owner(self) -> None:
        result = self.classify("HexRoots/Basic.lean")
        self.assertFalse(result.all_libraries)
        self.assertEqual(result.libraries, ("HexRoots",))

    def test_auxiliary_roots_select_owner(self) -> None:
        for path in (
            "bench/HexRoots/Bench.lean",
            "conformance/HexRoots/Conformance.lean",
            "conformance-fixtures/HexRoots/roots.jsonl",
        ):
            with self.subTest(path=path):
                result = self.classify(path)
                self.assertFalse(result.all_libraries)
                self.assertEqual(result.libraries, ("HexRoots",))

    def test_oracle_script_selects_every_tuple_owner(self) -> None:
        result = self.classify("scripts/oracle/matrix_flint.py")
        self.assertFalse(result.all_libraries)
        self.assertEqual(set(result.libraries), {"HexBareiss", "HexDeterminant"})

    def test_common_oracle_selects_all(self) -> None:
        result = self.classify("scripts/oracle/common.py")
        self.assertTrue(result.all_libraries)
        self.assertEqual(result.library_filter, "")

    def test_shared_paths_select_all(self) -> None:
        for path in (
            "Hex/Json.lean",
            "scripts/ci/run_oracles.sh",
            "lakefile.lean",
            ".github/workflows/ci.yml",
        ):
            with self.subTest(path=path):
                self.assertTrue(self.classify(path).all_libraries)

    def test_no_dependents_are_added(self) -> None:
        result = self.classify("HexPoly/Basic.lean")
        self.assertEqual(result.libraries, ("HexPoly",))

    def test_documentation_does_not_widen_mixed_change(self) -> None:
        result = self.classify("HexRoots/Basic.lean", "SPEC/testing.md")
        self.assertEqual(result.libraries, ("HexRoots",))

    def test_unclassified_path_widens_mixed_change(self) -> None:
        result = self.classify("HexRoots/Basic.lean", "scripts/libgraph.py")
        self.assertTrue(result.all_libraries)

    def test_hex_graph_is_owned_by_graph_iso(self) -> None:
        result = self.classify("HexGraph/Basic.lean")
        self.assertEqual(result.libraries, ("HexGraphIso",))

    def test_oracle_alias_selects_owner(self) -> None:
        result = self.classify("scripts/oracle/bz_trace_gate.py")
        self.assertEqual(result.libraries, ("HexBerlekampZassenhaus",))

    def test_auxiliary_suffix_uses_longest_owner(self) -> None:
        result = self.classify("conformance/HexPrimalityMathlibConformance/Test.lean")
        self.assertEqual(result.libraries, ("HexPrimalityMathlib",))

    def test_live_oracle_registry_uses_library_owners(self) -> None:
        owners = load_oracle_owners()
        self.assertEqual(owners["scripts/oracle/roots_flint.py"], {"HexRoots"})
        self.assertEqual(owners["scripts/oracle/matrix_carriers.py"], {"HexBareiss", "HexDeterminant"})


if __name__ == "__main__":
    unittest.main()
