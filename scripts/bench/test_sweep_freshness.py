#!/usr/bin/env python3
"""Regression tests for the shared figure-freshness mechanism."""

from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
import unittest.mock
from pathlib import Path

from scripts.bench import sweep_freshness as freshness


def listing(*rows: tuple[str, str]) -> str:
    return "".join(f"100644 {blob} 0\t{path}\n" for path, blob in rows)


FAMILY = freshness.Family(
    name="test-family",
    include=("Lib/", "Other/*.lean", "one/file.txt"),
    exclude=("Lib/SPEC", "Lib/README.md"),
)


class EntryMatching(unittest.TestCase):
    def test_directory_prefix_matches_below_it(self):
        self.assertTrue(FAMILY.matches("Lib/Deep/Nested.lean"))

    def test_suffix_glob_restricts_by_extension(self):
        self.assertTrue(FAMILY.matches("Other/Deep/A.lean"))
        self.assertFalse(FAMILY.matches("Other/Deep/A.c"))

    def test_exact_path_matches_only_itself(self):
        self.assertTrue(FAMILY.matches("one/file.txt"))
        self.assertFalse(FAMILY.matches("one/file.txt.bak"))

    def test_exclusions_win(self):
        self.assertFalse(FAMILY.matches("Lib/SPEC/lib.md"))
        self.assertFalse(FAMILY.matches("Lib/README.md"))
        self.assertTrue(FAMILY.matches("Lib/SPECIAL.lean"))

    def test_pathspec_is_the_include_set_before_its_globs(self):
        self.assertEqual(FAMILY.pathspec(), ["Lib/", "Other/", "one/file.txt"])

    def test_staging_pathspec_keeps_the_globs_and_the_exclusions(self):
        self.assertEqual(FAMILY.staging_pathspec(), [
            "Lib/", "Other/*.lean", "one/file.txt",
            ":!Lib/SPEC", ":!Lib/README.md"])


class Differences(unittest.TestCase):
    BASE = listing(("a.lean", "1" * 40), ("b.lean", "2" * 40))

    def test_identical_listings_do_not_differ(self):
        self.assertEqual(freshness.differences(self.BASE, self.BASE), [])

    def test_edited_added_and_removed_paths_are_reported(self):
        current = listing(("a.lean", "3" * 40), ("c.lean", "4" * 40))
        found = {d.path: (d.baseline, d.current)
                 for d in freshness.differences(self.BASE, current)}
        self.assertEqual(found["a.lean"], ("1" * 40, "3" * 40))
        self.assertEqual(found["b.lean"], ("2" * 40, None))
        self.assertEqual(found["c.lean"], (None, "4" * 40))

    def test_render_names_the_blob_transition(self):
        difference = freshness.Difference("a.lean", "1" * 40, None)
        self.assertEqual(difference.render(), "a.lean (111111111111 -> absent)")


class Assess(unittest.TestCase):
    """The three outcomes: measured, exempted, stale."""

    CURRENT = listing(("Lib/A.lean", "a" * 40), ("Lib/B.lean", "b" * 40))
    BASELINE = listing(("Lib/A.lean", "a" * 40), ("Lib/B.lean", "0" * 40))

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        patch = unittest.mock.patch.object(freshness, "RESULTS", self.root)
        patch.start()
        self.addCleanup(patch.stop)
        self.family = freshness.Family(
            name="test-family", include=("Lib/",),
            exemptions=self.root / "exemptions")

    def record(self, text: str) -> str:
        return freshness.record(self.family, text)

    def exempt(self, path: str, baseline: str | None, current: str | None):
        directory = self.root / "exemptions"
        directory.mkdir(exist_ok=True)
        (directory / f"{path.replace('/', '-')}.json").write_text(json.dumps({
            "path": path, "baseline_blob": baseline,
            "current_blob": current, "reason": "runtime-neutral"}))

    def test_a_matching_fingerprint_is_fresh(self):
        digest = self.record(self.CURRENT)
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=self.CURRENT)
        self.assertTrue(verdict.fresh)
        self.assertEqual(verdict.matched.label, "data.jsonl")

    def test_a_match_without_a_manifest_is_rejected(self):
        digest = freshness.fingerprint(self.CURRENT)
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=self.CURRENT)
        self.assertFalse(verdict.fresh)
        self.assertIn("committed no manifest", verdict.errors[0])

    def test_a_match_whose_manifest_is_not_the_current_listing_is_rejected(self):
        # A truncated fingerprint could in principle be claimed by a
        # listing that is not the one recorded, so compare the bytes.
        digest = self.record(self.CURRENT)
        freshness.manifest_path(self.family, digest).write_text(self.BASELINE)
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=self.CURRENT)
        self.assertFalse(verdict.fresh)
        self.assertIn("not the current listing", verdict.errors[0])

    def test_a_mode_change_is_a_difference(self):
        digest = self.record(self.CURRENT)
        chmodded = self.CURRENT.replace("100644 " + "b" * 40,
                                        "100755 " + "b" * 40)
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=chmodded)
        self.assertFalse(verdict.fresh)
        self.assertIn("mode 100644 -> 100755", verdict.errors[0])

    def test_a_moved_fingerprint_without_a_manifest_is_stale(self):
        verdict = freshness.assess(
            self.family, [freshness.Observation("0" * 12, "data.jsonl")],
            listing=self.CURRENT)
        self.assertFalse(verdict.fresh)
        self.assertIn("no measurement covers the current source",
                      verdict.errors[0])

    def test_an_unexempted_difference_names_the_path(self):
        digest = self.record(self.BASELINE)
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=self.CURRENT)
        self.assertFalse(verdict.fresh)
        self.assertIn("Lib/B.lean", verdict.errors[0])
        self.assertNotIn("Lib/A.lean", verdict.errors[0])

    def test_an_exempted_difference_is_accepted(self):
        digest = self.record(self.BASELINE)
        self.exempt("Lib/B.lean", "0" * 40, "b" * 40)
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=self.CURRENT)
        self.assertTrue(verdict.fresh)
        self.assertEqual([d.path for d in verdict.exempted], ["Lib/B.lean"])

    def test_a_deletion_is_exempted_by_a_null_current_blob(self):
        digest = self.record(self.CURRENT)
        self.exempt("Lib/B.lean", "b" * 40, None)
        removed = listing(("Lib/A.lean", "a" * 40))
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=removed)
        self.assertTrue(verdict.fresh)
        self.assertEqual([d.path for d in verdict.exempted], ["Lib/B.lean"])

    def test_an_exemption_expires_when_the_file_changes_again(self):
        digest = self.record(self.BASELINE)
        self.exempt("Lib/B.lean", "0" * 40, "b" * 40)
        moved_on = listing(("Lib/A.lean", "a" * 40), ("Lib/B.lean", "c" * 40))
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=moved_on)
        self.assertFalse(verdict.fresh)

    def test_a_family_rule_can_accept_a_difference(self):
        digest = self.record(self.BASELINE)
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            allow=lambda difference: difference.path == "Lib/B.lean",
            listing=self.CURRENT)
        self.assertTrue(verdict.fresh)

    def test_the_newest_manifest_becomes_the_baseline(self):
        old = self.record(listing(("Lib/A.lean", "9" * 40)))
        recent = self.record(self.BASELINE)
        verdict = freshness.assess(self.family, [
            freshness.Observation(old, "old.jsonl", 1),
            freshness.Observation(recent, "recent.jsonl", 2)],
            listing=self.CURRENT)
        self.assertEqual(verdict.baseline.label, "recent.jsonl")

    def test_a_manifest_that_does_not_hash_to_its_name_is_rejected(self):
        digest = self.record(self.BASELINE)
        freshness.manifest_path(self.family, digest).write_text(self.CURRENT)
        verdict = freshness.assess(
            self.family, [freshness.Observation(digest, "data.jsonl")],
            listing=self.CURRENT)
        self.assertFalse(verdict.fresh)
        self.assertIn("does not hash to its own fingerprint", verdict.errors[0])

    def test_an_observation_without_a_manifest_is_not_a_baseline(self):
        recorded = self.record(self.BASELINE)
        verdict = freshness.assess(self.family, [
            freshness.Observation(recorded, "recorded.jsonl", 1),
            freshness.Observation("f" * 12, "unrecorded.jsonl", 2)],
            listing=self.CURRENT)
        self.assertEqual(verdict.baseline.label, "recorded.jsonl")


class Quoting(unittest.TestCase):
    def test_a_c_quoted_name_matches_under_its_plain_name(self):
        family = freshness.Family(name="q", include=("Lib/",))
        self.assertTrue(family.matches(r'"Lib/od\td.lean"'))

    def test_a_plain_name_is_left_alone(self):
        self.assertEqual(freshness.unquote("Lib/A.lean"), "Lib/A.lean")


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
            (root / "two.json").write_text(
                json.dumps(dict(self.ENTRY, current_blob="c" * 40)))
            loaded = freshness.load_exemptions(root)
        self.assertEqual(len(loaded), 2)
        self.assertIn(("lakefile.lean", "a" * 40, "b" * 40), loaded)

    def test_missing_field_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            incomplete = {k: v for k, v in self.ENTRY.items() if k != "reason"}
            (root / "bad.json").write_text(json.dumps(incomplete))
            with self.assertRaises(SystemExit):
                freshness.load_exemptions(root)

    def test_an_absent_directory_means_no_exemptions(self):
        self.assertEqual(freshness.load_exemptions(None), set())
        self.assertEqual(
            freshness.load_exemptions(Path("/nonexistent-exemptions")), set())

    def test_committed_factorization_entries_all_parse(self):
        loaded = freshness.load_exemptions(freshness.FACTOR_EXEMPTIONS)
        self.assertGreater(len(loaded), 0)


class LeanComments(unittest.TestCase):
    def strip(self, text: str) -> str:
        return freshness.strip_lean_comments(text)

    def test_line_and_block_comments_go(self):
        self.assertEqual(self.strip("x -- gone\ny"), "x  \ny")
        self.assertEqual(self.strip("/-- doc -/\nx"), " \nx")
        self.assertEqual(self.strip("/-! mod\nprose -/\nx"), " \nx")

    def test_block_comments_nest(self):
        self.assertEqual(self.strip("/- a /- b -/ c -/x"), " x")

    def test_string_literals_are_not_comments(self):
        self.assertEqual(self.strip('s := "a -- b"'), 's := "a -- b"')
        self.assertEqual(self.strip('s := "/- x -/"'), 's := "/- x -/"')
        self.assertEqual(self.strip(r's := "\" -- in"'), r's := "\" -- in"')

    def test_code_and_indentation_survive(self):
        self.assertNotEqual(self.strip("theorem a := 1"),
                            self.strip("theorem a := 2"))
        self.assertNotEqual(self.strip("theorem a"), self.strip("  theorem a"))


class LeanCommentOnly(unittest.TestCase):
    def difference(self, before: str, after: str, **kwargs):
        blobs = {"a" * 40: before, "b" * 40: after}
        difference = freshness.Difference(
            kwargs.pop("path", "Lib/A.lean"), "a" * 40, "b" * 40,
            kwargs.pop("baseline_mode", "100644"),
            kwargs.pop("current_mode", "100644"))
        with unittest.mock.patch.object(
                freshness, "blob_text", blobs.__getitem__):
            return freshness.lean_comment_only(difference)

    def test_a_reworded_docstring_is_allowed(self):
        self.assertTrue(self.difference("/-- before -/\ndef a := 1",
                                        "/-- after -/\ndef a := 1"))

    def test_a_changed_declaration_is_not(self):
        self.assertFalse(self.difference("/-- d -/\ndef a := 1",
                                         "/-- d -/\ndef a := 2"))

    def test_a_changed_indentation_is_not(self):
        self.assertFalse(self.difference("def a :=\n 1", "def a :=\n   1"))

    def test_only_lean_paths_qualify(self):
        self.assertFalse(self.difference("# a\nx = 1", "# b\nx = 1",
                                         path="scripts/plots/p.py"))

    def test_a_mode_change_is_not_comment_only(self):
        self.assertFalse(self.difference("/-- a -/", "/-- b -/",
                                         current_mode="100755"))

    def test_an_added_or_removed_path_is_not_comment_only(self):
        self.assertFalse(freshness.lean_comment_only(
            freshness.Difference("Lib/A.lean", None, "b" * 40)))
        self.assertFalse(freshness.lean_comment_only(
            freshness.Difference("Lib/A.lean", "a" * 40, None)))


class Families(unittest.TestCase):
    """The declarations themselves, checked against the repository."""

    def test_graphiso_listing_matches_its_historical_pathspec(self):
        # Every committed hex-graph-iso fingerprint was recorded by this
        # exact pathspec. A refactor that changes the listing by one byte
        # invalidates all of them, so pin it.
        raw = freshness.git(
            "ls-files", "-s", "--", "HexGraphIso/", "HexGraph/",
            "bench/HexGraphIso/Cactus.lean",
            "scripts/plots/hexgraphiso-cactus.py",
            ":!HexGraphIso/SPEC", ":!HexGraphIso/README.md")
        self.assertEqual(freshness.index_listing(freshness.GRAPHISO), raw)

    def test_factorization_source_is_lean_under_the_service_libraries(self):
        family = freshness.factor_family("hex-factor")
        self.assertTrue(family.matches("HexPolyZ/Rational.lean"))
        self.assertTrue(family.matches("HexPrimality/Table.lean"))
        self.assertTrue(family.matches("bench/corpus/hexbz-factor-corpus.jsonl"))
        self.assertFalse(family.matches("HexPrimality/Sieve.lean"))
        self.assertFalse(family.matches("HexPolyZ/SPEC/hex-poly-z.md"))

    def test_comparator_families_see_only_their_own_adapter(self):
        flint = freshness.factor_family("flint")
        self.assertTrue(flint.matches("scripts/oracle/bz_flint_service.py"))
        self.assertFalse(flint.matches("scripts/oracle/bz_pari_service.py"))
        self.assertFalse(flint.matches("HexPolyZ/Rational.lean"))
        isabelle = freshness.factor_family("isabelle-bz")
        self.assertTrue(isabelle.matches("scripts/oracle/bz-isabelle/ROOT"))

    def test_every_family_is_registered_under_its_own_name(self):
        for name, family in freshness.FAMILIES.items():
            self.assertEqual(name, family.name)

    def test_tree_and_index_listings_agree_on_a_clean_checkout(self):
        # The two paths into `assess` -- reading the index for the current
        # source, reading a tree when backfilling a manifest from the
        # commit that measured it -- have to produce the same bytes.
        for family in freshness.FAMILIES.values():
            with self.subTest(family=family.name):
                index = freshness.index_listing(family)
                staged = freshness.git(
                    "diff", "--cached", "--name-only", "--", *family.pathspec())
                if staged.strip():
                    self.skipTest(f"{family.name} has staged changes")
                self.assertEqual(freshness.tree_listing(family, "HEAD"), index)

    def test_every_committed_manifest_hashes_to_its_own_name(self):
        found = 0
        for path in sorted(freshness.RESULTS.glob(f"*{freshness.MANIFEST_SUFFIX}")):
            found += 1
            recorded = path.name[:-len(freshness.MANIFEST_SUFFIX)].rsplit("-", 1)[1]
            self.assertEqual(freshness.fingerprint(path.read_text()), recorded,
                             f"{path.name} does not hash to its file name")
        self.assertGreater(found, 0)


class CommandLine(unittest.TestCase):
    def run_cli(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["python3", str(Path(freshness.__file__)), *args],
            cwd=freshness.ROOT, text=True, capture_output=True)

    def test_fingerprint_matches_the_module(self):
        result = self.run_cli("--fingerprint", "hexgraphiso-cactus")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            result.stdout.strip(),
            freshness.fingerprint(freshness.index_listing(freshness.GRAPHISO)))

    def test_an_unknown_mode_is_rejected(self):
        self.assertEqual(
            self.run_cli("--paths", "hexgraphiso-cactus").returncode, 2)

    def test_an_unknown_family_is_rejected(self):
        self.assertEqual(self.run_cli("--fingerprint", "nope").returncode, 2)

    def test_a_ref_selects_the_listing_at_that_commit(self):
        result = self.run_cli(
            "--fingerprint", "hexgraphiso-cactus", "--ref", "HEAD")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            result.stdout.strip(),
            freshness.fingerprint(
                freshness.tree_listing(freshness.GRAPHISO, "HEAD")))

    def test_a_malformed_argument_list_is_rejected(self):
        self.assertEqual(self.run_cli(
            "--fingerprint", "hexgraphiso-cactus", "--oops").returncode, 2)


if __name__ == "__main__":
    unittest.main()
