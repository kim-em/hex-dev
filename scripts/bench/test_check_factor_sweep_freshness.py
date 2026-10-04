#!/usr/bin/env python3
"""Regression tests for the factorization freshness guard."""

from __future__ import annotations

import unittest
from unittest import mock
import tempfile
from pathlib import Path
from unittest.mock import patch

from scripts.bench import check_factor_sweep_freshness as guard
from scripts.bench import sweep_freshness as freshness


BASE = """\
import Lake
open Lake DSL

package hex where
  leanOptions := #[⟨`autoImplicit, false⟩]

require "leanprover-community" / "batteries" @ git "main"

lean_lib HexPoly where
  srcDir := "."

private def hexArithOTarget := "cc"

lean_exe hexbz_factor_service where
  srcDir := "bench"
  root := `HexBench.FactorService
"""


class RepositoryLakefile(unittest.TestCase):
    def test_current_import_closure_and_library_ownership(self):
        guard.factor_import_modules.cache_clear()
        self.addCleanup(guard.factor_import_modules.cache_clear)
        modules = guard.factor_import_modules()
        self.assertIsNotNone(modules)
        self.assertTrue({'HexBench.BerlekampKernel', 'HexPrimality.Table'} <= modules)
        source = freshness.git('show', ':lakefile.lean')
        parsed = freshness.lakefile_blocks(source)
        self.assertFalse(any(key.startswith('command ') for key in parsed))
        relevant = guard.factorization_blocks(source)
        for library in ('HexPrimality', 'HexBerlekampKernelProbe', 'HexArithNative', 'HexModArithNative'):
            self.assertIn('lean_lib ' + library, relevant)
        self.assertNotIn('lean_lib HexConformance', relevant)


class LakefileBlocks(unittest.TestCase):
    def test_multiline_doc_comment_attaches_to_following_declaration(self):
        text = BASE + '\n/-- The new\nmodule. -/\nlean_lib HexNew\n'
        blocks = freshness.lakefile_blocks(text)
        self.assertIn('module. -/', blocks['lean_lib HexNew'])
        self.assertNotIn('module. -/', blocks['lean_exe hexbz_factor_service'])

    def test_column_zero_expression_continuation_stays_in_its_declaration(self):
        before = BASE + '\nlean_lib HexChecks where\n  globs := #[\n`HexArith.Conformance,\n    `HexPoly.Conformance]\n\nlean_lib Other\n'
        blocks = freshness.lakefile_blocks(before)
        self.assertIn('`HexArith.Conformance', blocks['lean_lib HexChecks'])
        self.assertIn('`HexPoly.Conformance', blocks['lean_lib HexChecks'])
        self.assertNotIn('`HexArith.Conformance', blocks['lean_lib Other'])

    def test_splits_top_level_declarations(self):
        blocks = freshness.lakefile_blocks(BASE)
        self.assertIn("package hex", blocks)
        self.assertIn("lean_lib HexPoly", blocks)
        self.assertIn("def hexArithOTarget", blocks)
        self.assertIn("lean_exe hexbz_factor_service", blocks)
        self.assertIn('require "leanprover-community"', blocks)

    def test_indented_body_stays_with_its_declaration(self):
        blocks = freshness.lakefile_blocks(BASE)
        self.assertIn('root := `HexBench.FactorService',
                      blocks["lean_exe hexbz_factor_service"])
        self.assertNotIn("srcDir", blocks["package hex"])

    def test_leading_comment_attaches_to_the_following_declaration(self):
        text = BASE + '\n-- a note\nlean_lib HexNew where\n  srcDir := "."\n'
        blocks = freshness.lakefile_blocks(text)
        self.assertIn("-- a note", blocks["lean_lib HexNew"])


class LakefileAffectsRuntime(unittest.TestCase):
    def test_imported_module_outside_factor_namespaces_protects_its_library(self):
        before = BASE + '\nlean_lib HexPrimality\n'
        after = before.replace('lean_lib HexPrimality\n',
                               'lean_lib HexPrimality where\n  moreLeancArgs := #["-O0"]\n')
        with patch.object(guard, 'factor_import_modules', return_value={'HexPrimality.Table'}):
            self.assertTrue(guard.lakefile_texts_differ(before, after))

    def test_computed_module_claims_are_conservatively_protected(self):
        for glob in ('someHelper', 'Name.mkSimple "HexArith"',
                     '#[`Other].map (fun _ => `HexArith.UInt64.Wide)'):
            after = BASE + f'\nlean_lib New where\n  globs := {glob}\n'
            with self.subTest(glob=glob), \
                    patch.object(guard, 'factor_import_modules', return_value={'HexArith.UInt64.Wide'}):
                self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_unrecognised_top_level_commands_cannot_hide_flags(self):
        for declaration in ('abbrev flags := "-O3"', 'noncomputable def flags := "-O3"',
                            'opaque flags := "-O3"', 'instance : String := "-O3"',
                            'set_option maxRecDepth 1000'):
            before = BASE + '\nlean_lib Other\n' + declaration + \
                '\nprivate def hexArithOTarget2 := flags\nextern_lib extraffi pkg := hexArithOTarget2\n'
            after = before.replace('-O3', '-O0').replace('maxRecDepth 1000', 'maxRecDepth 2000')
            with self.subTest(declaration=declaration):
                self.assertTrue(guard.lakefile_texts_differ(before, after))

    def test_inline_attributes_and_comments_cannot_hide_native_archives(self):
        for prefix in ('@[default_target] ', '/-- native archive -/ '):
            after = BASE + '\nlean_lib Other\n' + prefix + 'extern_lib extraffi pkg := "archive"\n'
            with self.subTest(prefix=prefix):
                self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_column_zero_compiler_flag_continuation_is_protected(self):
        before = BASE.replace('hexArithOTarget := "cc"', 'hexArithOTarget := (\n"cc -O3")')
        self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))

    def test_claiming_only_unimported_conformance_modules_is_unrelated(self):
        before = BASE + '\nlean_lib HexChecks where\n  globs := #[\n`HexArith.Conformance,\n    `HexPoly.Conformance]\n'
        after = before.replace('`HexPoly.Conformance', '`HexPoly.OtherConformance')
        with patch.object(guard, 'factor_import_modules', return_value={'HexArith.UInt64.Wide'}):
            self.assertFalse(guard.lakefile_texts_differ(before, after))
            imported = before.replace('`HexArith.Conformance', '`HexArith.UInt64.Wide')
            self.assertTrue(guard.lakefile_texts_differ(before, imported))
        with patch.object(guard, 'factor_import_modules', return_value=None):
            self.assertTrue(guard.lakefile_texts_differ(before, after))

    def test_qualified_literal_globs_distinguish_imported_modules(self):
        for constructor in ('Glob.one', 'Glob.submodules', 'Glob.andSubmodules'):
            unrelated = BASE + f'\nlean_lib Checks where\n  globs := #[{constructor} `Other.Tests]\n'
            imported = unrelated.replace('`Other.Tests', '`HexPrimality.Table')
            with self.subTest(constructor=constructor), \
                    patch.object(guard, 'factor_import_modules', return_value={'HexPrimality.Table'}):
                self.assertFalse(guard.lakefile_texts_differ(BASE, unrelated))
                self.assertTrue(guard.lakefile_texts_differ(BASE, imported))

    def test_quoted_and_braced_library_names_cannot_hide_implicit_roots(self):
        for name in ('«HexBench»', '"HexBench"', 'HexBench{'):
            after = BASE + f'\nlean_lib {name} where\n  srcDir := "bench"\n'
            with self.subTest(name=name), patch.object(guard, 'factor_import_modules',
                                                      return_value={'HexBench.BerlekampKernel'}):
                self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_character_literal_does_not_absorb_native_declarations(self):
        after = BASE + "\nscript s do\n  let c := '('\n  pure 0\nextern_lib extraffi pkg := \"archive\"\n"
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))
        self.assertTrue(guard.lakefile_texts_differ(BASE, BASE + '\nscript s do\n  let c := (\n'))

    def test_nested_filter_application_cannot_hide_computed_globs(self):
        after = BASE + '\nlean_lib Other where\n  globs := Array.filter (fun _ => true) <| (fun (_ : Array Glob) => #[.submodules `HexBench]) <| #[`Unrelated].map Glob.one\n'
        with patch.object(guard, 'factor_import_modules', return_value={'HexBench.BerlekampKernel'}):
            self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_semicolon_fields_retain_compiler_flags(self):
        before = BASE.replace('srcDir := "."', 'precompileModules := true; moreLeancArgs := #["-O3"]')
        self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))

    def test_helper_parameters_need_no_space_after_name(self):
        before = BASE + '\ndef flags(x : Nat) := "-O3"\nextern_lib extraffi pkg := flags 0\n'
        self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))

    def test_helper_suffixes_and_repeated_keys_preserve_relevant_bodies(self):
        for suffix in ('?', '!'):
            before = BASE + f'\ndef flags := "-O3"\ndef flags{suffix} := true\nextern_lib extraffi pkg := flags\n'
            with self.subTest(suffix=suffix):
                self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))
        duplicate = BASE + '\ndef flags := "-O3"\ndef flags := "unchanged"\n'
        self.assertTrue(guard.lakefile_texts_differ(duplicate, duplicate.replace('-O3', '-O0')))

    def test_comma_fields_retain_compiler_flags(self):
        before = BASE.replace('srcDir := "."', 'precompileModules := true, moreLeancArgs := #["-O3"]')
        self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))

    def test_attributed_commands_remain_relevant(self):
        before = BASE + '\n@[default_instance] instance : String := "-O3"\nlean_lib Other\n'
        self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))

    def test_library_claimant_order_is_part_of_build_configuration(self):
        first = 'lean_lib First where\n  globs := #[Glob.one `HexPrimality.Table]\n'
        second = 'lean_lib Second where\n  globs := #[Glob.one `HexPrimality.Table]\n'
        with patch.object(guard, 'factor_import_modules', return_value={'HexPrimality.Table'}):
            self.assertTrue(guard.lakefile_texts_differ(BASE + first + second, BASE + second + first))

    def test_scope_commands_protect_declaration_position(self):
        first = BASE.replace('\nlean_lib HexPoly', '\nnamespace A\nlean_lib HexPoly').replace(
            '\nprivate def', '\nend A\nprivate def')
        second = BASE.replace('\nlean_lib HexPoly', '\nnamespace A\nlean_lib HexPoly') + 'end A\n'
        self.assertTrue(guard.lakefile_texts_differ(first, second))

    def test_indented_scope_commands_in_unrelated_blocks(self):
        before = BASE + '\nlean_lib Other\n  namespace A\nlean_lib Third\n  end A\n'
        after = BASE + '\nlean_lib Other\nlean_lib Third\n  namespace A\n  end A\n'
        self.assertTrue(guard.lakefile_texts_differ(before, after))

    def test_handwritten_library_order(self):
        first = '\n@[lean_lib] def first := "config"\n'
        second = '\nlean_lib HexPoly\n'
        self.assertTrue(guard.lakefile_texts_differ(BASE + first + second, BASE + second + first))

    def test_handwritten_target_attributes_are_relevant(self):
        before = BASE + '\n@[target, lean_lib] def configured := "-O3"\n'
        self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))

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

    def test_adding_a_dependency_is_not_a_runtime_change(self):
        after = BASE + '\nrequire "leanprover" / "hex" @ git "main"\n'
        self.assertFalse(guard.lakefile_texts_differ(BASE, after))

    def test_editing_a_dependency_is_a_runtime_change(self):
        after = BASE.replace('@ git "main"', '@ git "stable"', 1)
        self.assertNotEqual(after, BASE)
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_package_native_archives_and_transitive_helpers_affect_runtime(self):
        before = BASE + '\nprivate def compileFlags := "-O3"\n' + \
            'private def archiveObject := compileFlags\n' + \
            'extern_lib otherffi pkg := archiveObject\n'
        self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))
        self.assertTrue(guard.lakefile_texts_differ(BASE, before))
        self.assertTrue(guard.lakefile_texts_differ(before, BASE))

    def test_library_scoped_link_target_and_helpers_affect_runtime(self):
        before = BASE.replace('lean_lib HexPoly where\n',
            'lean_lib HexPoly where\n  moreLinkObjs := #[polyffi]\n') + \
            '\nprivate def compileFlags := "-O3"\n' + \
            'target polyffi pkg := compileFlags\n'
        self.assertTrue(guard.lakefile_texts_differ(before, before.replace('-O3', '-O0')))
        unrelated = before + '\ntarget unrelated pkg := "-O3"\n'
        self.assertFalse(guard.lakefile_texts_differ(unrelated, unrelated.replace(
            'target unrelated pkg := "-O3"', 'target unrelated pkg := "-O0"')))

    def test_audited_proof_pin_keeps_all_runtime_checks(self):
        old_pin = "3808ce862c09ad5b4de0c76f10ba00946ed2eff3"
        new_pin = "ab1451487da02cd4483d0e2cdb2cc9e44bbbac17"
        before = BASE + ('\nrequire AINTLIB from git\n'
            '  "https://github.com/CBirkbeck/AINTLIB.git" @ "' + old_pin + '"\n')
        after = before.replace(old_pin, new_pin)
        with patch.object(freshness, "lean_import_prefixes", return_value={"HexPoly"}):
            self.assertFalse(guard.lakefile_texts_differ(before, after))
            for bad in (after.replace(new_pin, "main"),
                        after.replace(new_pin, "b" * 40),
                        after.replace("CBirkbeck", "other"),
                        after.replace('hexArithOTarget := "cc"', 'hexArithOTarget := "clang"'),
                        after.replace("`autoImplicit, false", "`autoImplicit, true")):
                self.assertTrue(guard.lakefile_texts_differ(before, bad))
        for closure in (None, *({root} for root in freshness.AUDITED_AINT_ROOTS)):
            with patch.object(freshness, "lean_import_prefixes", return_value=closure):
                self.assertTrue(guard.lakefile_texts_differ(before, after))

    def test_no_change_is_not_a_runtime_change(self):
        self.assertFalse(guard.lakefile_texts_differ(BASE, BASE))

    def test_editing_an_unrelated_library_is_not_a_runtime_change(self):
        # HexInterval is not part of the factorization closure.
        before = BASE + '\nlean_lib HexInterval where\n  srcDir := "."\n'
        after = before.replace('lean_lib HexInterval where\n  srcDir := "."',
                               'lean_lib HexInterval where\n  srcDir := "src"')
        self.assertNotEqual(before, after)
        self.assertFalse(guard.lakefile_texts_differ(before, after))

    def test_precompiling_a_factorization_library_is_not_a_runtime_change(self):
        lib = guard.freshness.FACTOR_LIBRARIES[0]
        before = BASE + f"\nlean_lib {lib} where\n  precompileModules := true\n"
        after = BASE + f"\nlean_lib {lib}\n"
        self.assertFalse(guard.lakefile_texts_differ(before, after))
        self.assertTrue(guard.lakefile_texts_differ(
            before, BASE + f"\nlean_lib {lib} where\n  moreLinkArgs := #[\"-lm\"]\n"))

    def test_native_carrier_edits_are_runtime_changes(self):
        base = BASE + (
            "\ntarget wideO pkg : FilePath := hexArithOTarget pkg \"wide_arith.c\"\n"
            "\nlean_lib HexArithNative where\n"
            "  roots := #[`HexArithNative]\n"
            "  globs := #[.one `HexArithNative, .one `HexArith.UInt64.Wide]\n"
            "  moreLinkObjs := #[wideO]\n"
            "  moreLinkArgs := #[\"-lgmp\"]\n")
        for mutated in (
                base.replace("wide_arith.c", "wide_arith2.c"),
                base.replace("  moreLinkObjs := #[wideO]\n", ""),
                base.replace('#["-lgmp"]', '#["-lm"]')):
            self.assertTrue(guard.lakefile_texts_differ(base, mutated))

    def test_editing_a_factorization_library_is_a_runtime_change(self):
        after = BASE.replace('lean_lib HexPoly where\n  srcDir := "."',
                             'lean_lib HexPoly where\n  srcDir := "src"')
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))

    def test_editing_a_factorization_build_helper_is_a_runtime_change(self):
        after = BASE.replace('hexArithOTarget := "cc"',
                             'hexArithOTarget := "clang"')
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
    def setUp(self):
        patcher = patch.object(guard, 'factor_import_modules', return_value={'HexArith.UInt64.Wide'})
        patcher.start()
        self.addCleanup(patcher.stop)

    BASELINE = "a" * 40
    ENDPOINT = "b" * 40
    CURRENT = "c" * 40
    APPROVED = BASE.replace('hexArithOTarget := "cc"', 'hexArithOTarget := "clang"')

    def checked_transition(self, after, *, exemption=None, missing=False,
                           before_mode="100644", after_mode="100644", family=None):
        exemption = exemption or ("lakefile.lean", self.BASELINE, self.ENDPOINT)
        blobs = {self.BASELINE: BASE, self.CURRENT: after}
        if not missing:
            blobs[exemption[2]] = self.APPROVED

        def read_blob(*args):
            self.assertEqual(args[:2], ("cat-file", "blob"))
            if args[2] not in blobs:
                raise SystemExit("missing blob")
            return blobs[args[2]]

        exemptions = {exemption}
        with patch.object(freshness, "git", side_effect=read_blob), \
                patch.object(freshness, "load_exemptions", return_value=exemptions):
            return guard.build_only_lakefile_edit(freshness.Difference(
                "lakefile.lean", self.BASELINE, self.CURRENT, before_mode, after_mode), family)

    def test_reviewed_transition_survives_unrelated_proof_targets(self):
        after = self.APPROVED + '\nlean_lib HexProof where\n  srcDir := "adapters"\n'
        self.assertTrue(guard.lakefile_texts_differ(BASE, after))
        self.assertTrue(self.checked_transition(after))

    def test_reviewed_transition_does_not_cover_later_runtime_changes(self):
        for after in (
                self.APPROVED.replace('`HexBench.FactorService', '`HexBench.Other'),
                self.APPROVED.replace('hexArithOTarget := "clang"',
                                      'hexArithOTarget := "clang -O0"'),
                self.APPROVED.replace('`autoImplicit, false', '`autoImplicit, true')):
            with self.subTest(after=after):
                self.assertFalse(self.checked_transition(after))

    def test_reviewed_transition_requires_the_same_baseline_and_path(self):
        for exemption in (("lakefile.lean", "d" * 40, self.ENDPOINT),
                          ("other.lean", self.BASELINE, self.ENDPOINT),
                          ("lakefile.lean", self.BASELINE, None)):
            with self.subTest(exemption=exemption):
                self.assertFalse(self.checked_transition(self.APPROVED, exemption=exemption))

    def test_reviewed_transition_requires_available_endpoint(self):
        self.assertFalse(self.checked_transition(self.APPROVED, missing=True))

    def test_endpoint_must_be_a_full_object_id_not_a_revision_expression(self):
        for endpoint in ("HEAD:lakefile.lean", ":lakefile.lean", self.ENDPOINT[:12], "--help"):
            with self.subTest(endpoint=endpoint):
                self.assertFalse(self.checked_transition(self.APPROVED,
                    exemption=("lakefile.lean", self.BASELINE, endpoint)))

    def test_reviewed_transition_respects_family_exemption_restrictions(self):
        self.assertFalse(self.checked_transition(self.APPROVED,
            family=freshness.factor_family("flint")))

    def test_assessment_still_rejects_another_changed_source_path(self):
        family = freshness.factor_family("hex-factor")
        before = f"100644 {self.BASELINE} 0\tlakefile.lean\n100644 {'d'*40} 0\tHexPoly/A.lean\n"
        after = f"100644 {self.CURRENT} 0\tlakefile.lean\n100644 {'e'*40} 0\tHexPoly/A.lean\n"
        blobs = {self.BASELINE: BASE, self.ENDPOINT: self.APPROVED, self.CURRENT: self.APPROVED}
        with tempfile.TemporaryDirectory() as temporary, \
                patch.object(freshness, "RESULTS", Path(temporary)), \
                patch.object(freshness, "git", side_effect=lambda *args: blobs[args[2]]), \
                patch.object(freshness, "load_exemptions", return_value={
                    ("lakefile.lean", self.BASELINE, self.ENDPOINT)}):
            digest = freshness.record(family, before)
            verdict = freshness.assess(family, [freshness.Observation(digest, "sample")],
                listing=after, allow=lambda diff: guard.build_only_lakefile_edit(diff, family))
            self.assertEqual([diff.path for diff in verdict.exempted], ["lakefile.lean"])
            self.assertEqual(len(verdict.errors), 1)
            self.assertIn("HexPoly/A.lean", verdict.errors[0])

    def test_file_mode_changes_are_not_build_only_edits(self):
        for after in (BASE, self.APPROVED):
            with self.subTest(after=after):
                self.assertFalse(self.checked_transition(after, after_mode="120000"))
                self.assertFalse(self.checked_transition(after, before_mode="120000"))

    def test_an_added_or_removed_lakefile_is_a_runtime_change(self):
        self.assertFalse(guard.build_only_lakefile_edit(
            guard.freshness.Difference("lakefile.lean", None, "a" * 40)))

    def test_an_exemption_follows_unrelated_lakefile_edits(self):
        lib = guard.freshness.FACTOR_LIBRARIES[0]
        blobs = {
            self.BASELINE: BASE,
            self.ENDPOINT: BASE + f"\nlean_lib {lib} where\n  moreLinkArgs := #[\"-lm\"]\n",
            self.CURRENT: BASE + f"\nlean_lib {lib} where\n  moreLinkArgs := #[\"-lm\"]\n"
                     "\nlean_lib Unrelated where\n",
            "d" * 40: BASE + f"\nlean_lib {lib} where\n  moreLinkArgs := #[\"-lz\"]\n",
        }
        exemptions = {("lakefile.lean", self.BASELINE, self.ENDPOINT)}
        with mock.patch.object(guard.freshness, "git", side_effect=lambda *a: blobs[a[-1]]), \
                mock.patch.object(guard.freshness, "load_exemptions", return_value=exemptions):
            self.assertTrue(guard.build_only_lakefile_edit(
                guard.freshness.Difference("lakefile.lean", self.BASELINE, self.CURRENT)))
            self.assertFalse(guard.build_only_lakefile_edit(
                guard.freshness.Difference("lakefile.lean", self.BASELINE, "d" * 40)))

    def test_another_path_is_not_a_lakefile_transition(self):
        self.assertFalse(guard.build_only_lakefile_edit(
            guard.freshness.Difference("HexPoly/Dense.lean", "a" * 40, "b" * 40)))


if __name__ == "__main__":
    unittest.main()
