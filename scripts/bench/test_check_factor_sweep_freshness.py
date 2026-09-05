#!/usr/bin/env python3
"""Regression tests for the factorization freshness guard."""

from __future__ import annotations

import unittest
from pathlib import Path

from scripts.bench import check_factor_sweep_freshness as guard


BASE = """\
import Lake
open Lake DSL

package hex where
  leanOptions := #[⟨`autoImplicit, false⟩]

require "leanprover-community" / "batteries" @ git "main"

lean_lib HexPoly where
  srcDir := "."

lean_exe hexbz_factor_service where
  srcDir := "bench"
  root := `HexBench.FactorService
"""


class LakefileBlocks(unittest.TestCase):
    def test_splits_top_level_declarations(self):
        blocks = guard.lakefile_blocks(BASE)
        self.assertIn("package hex", blocks)
        self.assertIn("lean_lib HexPoly", blocks)
        self.assertIn("lean_exe hexbz_factor_service", blocks)
        self.assertIn('require "leanprover-community"', blocks)

    def test_indented_body_stays_with_its_declaration(self):
        blocks = guard.lakefile_blocks(BASE)
        self.assertIn('root := `HexBench.FactorService',
                      blocks["lean_exe hexbz_factor_service"])
        self.assertNotIn("srcDir", blocks["package hex"])

    def test_leading_comment_attaches_to_the_following_declaration(self):
        text = BASE + '\n-- a note\nlean_lib HexNew where\n  srcDir := "."\n'
        blocks = guard.lakefile_blocks(text)
        self.assertIn("-- a note", blocks["lean_lib HexNew"])


class LakefileAffectsRuntime(unittest.TestCase):
    def test_registering_a_new_target_is_not_a_runtime_change(self):
        after = BASE + '\nlean_lib HexPolyFast where\n  srcDir := "."\n'
        self.assertFalse(guard.lakefile_texts_differ(BASE, after))

    def test_registering_a_new_exe_is_not_a_runtime_change(self):
        after = BASE + '\nlean_exe hexpolyfast_bench where\n  srcDir := "bench"\n'
        self.assertFalse(guard.lakefile_texts_differ(BASE, after))

    def test_editing_an_existing_target_is_a_runtime_change(self):
        after = BASE.replace('root := `HexBench.FactorService',
                             'root := `HexBench.FactorServiceV2')
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_editing_package_options_is_a_runtime_change(self):
        after = BASE.replace('⟨`autoImplicit, false⟩',
                             '⟨`autoImplicit, false⟩, ⟨`debug, true⟩')
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_removing_a_target_is_a_runtime_change(self):
        after = BASE.replace(
            'lean_lib HexPoly where\n  srcDir := "."\n\n', '')
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_adding_a_dependency_is_a_runtime_change(self):
        after = BASE + '\nrequire "leanprover" / "hex" @ git "main"\n'
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_no_change_is_not_a_runtime_change(self):
        self.assertFalse(guard.lakefile_texts_differ(BASE, BASE))

    def test_editing_an_unrelated_library_is_not_a_runtime_change(self):
        # HexInterval is not part of the factorization closure.
        before = BASE + '\nlean_lib HexInterval where\n  srcDir := "."\n'
        after = before.replace('lean_lib HexInterval where\n  srcDir := "."',
                               'lean_lib HexInterval where\n  srcDir := "src"')
        self.assertNotEqual(before, after)
        self.assertFalse(guard.lakefile_texts_differ(before, after))

    def test_editing_a_factorization_library_is_a_runtime_change(self):
        after = BASE.replace('lean_lib HexPoly where\n  srcDir := "."',
                             'lean_lib HexPoly where\n  srcDir := "src"')
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))


class Observations(unittest.TestCase):
    """Binding a committed report to the source fingerprint it was taken at."""

    REPORT = {"env": {"source_fingerprints": {"hex-factor": "abcdef123456"}}}

    def test_reads_the_fingerprint_this_system_recorded(self):
        found = guard.observation(
            "hex-factor", 7, Path("sweep.json"), self.REPORT)
        self.assertEqual(found.fingerprint, "abcdef123456")
        self.assertEqual(found.label, "sweep.json")
        self.assertEqual(found.timestamp, 7)

    def test_a_system_the_report_did_not_fingerprint_has_no_observation(self):
        self.assertIsNone(
            guard.observation("flint", 7, Path("sweep.json"), self.REPORT))

    def test_a_pre_migration_report_has_no_observation(self):
        self.assertIsNone(
            guard.observation("hex-factor", 7, Path("old.json"), {"env": {}}))


class LakefileTransitions(unittest.TestCase):
    def test_an_added_or_removed_lakefile_is_a_runtime_change(self):
        self.assertFalse(guard.build_only_lakefile_edit(
            guard.freshness.Difference("lakefile.lean", None, "a" * 40)))

    def test_another_path_is_not_a_lakefile_transition(self):
        self.assertFalse(guard.build_only_lakefile_edit(
            guard.freshness.Difference("HexPoly/Dense.lean", "a" * 40, "b" * 40)))


if __name__ == "__main__":
    unittest.main()
