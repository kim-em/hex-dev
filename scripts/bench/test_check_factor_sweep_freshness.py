#!/usr/bin/env python3
"""Regression tests for the factorization freshness guard."""

from __future__ import annotations

import json
import tempfile
import unittest
import unittest.mock
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


class SourcePaths(unittest.TestCase):
    def test_prime_table_is_factorization_input(self):
        self.assertTrue(guard.source_path("hex-factor", "HexPrimality/Table.lean"))

    def test_sieve_proofs_are_not_factorization_input(self):
        self.assertFalse(guard.source_path("hex-factor", "HexPrimality/Sieve.lean"))


class Exemptions(unittest.TestCase):
    ENTRY = {
        "path": "lakefile.lean",
        "baseline_blob": "a" * 40,
        "current_blob": "b" * 40,
        "reason": "registers a build-only target",
    }

    def test_reads_one_entry_per_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "one.json").write_text(json.dumps(self.ENTRY))
            other = dict(self.ENTRY, current_blob="c" * 40)
            (root / "two.json").write_text(json.dumps(other))
            with unittest.mock.patch.object(
                    guard, "PROOF_ONLY_EXEMPTIONS", root):
                loaded = guard.load_proof_only_exemptions()
        self.assertEqual(len(loaded), 2)
        self.assertIn(("lakefile.lean", "a" * 40, "b" * 40), loaded)

    def test_missing_field_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            incomplete = {k: v for k, v in self.ENTRY.items() if k != "reason"}
            (root / "bad.json").write_text(json.dumps(incomplete))
            with unittest.mock.patch.object(
                    guard, "PROOF_ONLY_EXEMPTIONS", root):
                with self.assertRaises(SystemExit):
                    guard.load_proof_only_exemptions()

    def test_committed_entries_all_parse(self):
        loaded = guard.load_proof_only_exemptions()
        self.assertGreater(len(loaded), 0)


if __name__ == "__main__":
    unittest.main()
