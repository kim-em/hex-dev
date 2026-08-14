#!/usr/bin/env python3
"""Tests for `scripts/check_phase7.py`.

The checker gates CI, so the cases that matter most are the ones where a naive
implementation would pass: a malformed anchor table, a tutorial file that exists
but is never built, and a path that points outside the tutorial directory. Each
of those is a way for the check to report success while the obligation it exists
to enforce is unmet.
"""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_phase7 import PolicyError, check, parse_anchor_table, tutorial_module

ANCHOR_TABLE = """
| Tutorial | Anchor library | Source file |
|----------|---------------|-------------|
| AES bytes | `hex-gf2` | `HexManual/Tutorials/AESField.lean` |
"""


def build_root(
    tmp: Path,
    *,
    done_through: int = 7,
    table: str = ANCHOR_TABLE,
    tutorial: bool = True,
    tutorial_import: bool = True,
    tutorial_include: bool = True,
    chapter: bool = True,
) -> Path:
    (tmp / "PLAN").mkdir(parents=True, exist_ok=True)
    (tmp / "HexManual" / "Chapters").mkdir(parents=True, exist_ok=True)
    (tmp / "HexManual" / "Tutorials").mkdir(parents=True, exist_ok=True)
    (tmp / "HexGF2" / "SPEC").mkdir(parents=True, exist_ok=True)

    (tmp / "HexGF2" / "SPEC" / "hex-gf2.md").write_text("# hex-gf2\n", encoding="utf-8")
    (tmp / "libraries.yml").write_text(
        "libraries:\n"
        "  HexGF2:\n"
        "    deps: []\n"
        "    mathlib: false\n"
        f"    done_through: {done_through}\n"
        "    status: active\n",
        encoding="utf-8",
    )
    (tmp / "PLAN" / "Phase7.md").write_text(table, encoding="utf-8")
    if chapter:
        (tmp / "HexManual" / "Chapters" / "HexGF2.lean").write_text("chapter\n", encoding="utf-8")
    if tutorial:
        (tmp / "HexManual" / "Tutorials" / "AESField.lean").write_text("tut\n", encoding="utf-8")

    manual = ["import HexManual.Chapters.HexGF2"]
    if tutorial_import:
        manual.append("import HexManual.Tutorials.AESField")
    if tutorial_include:
        manual.append("{include 2 HexManual.Tutorials.AESField}")
    (tmp / "HexManual.lean").write_text("\n".join(manual) + "\n", encoding="utf-8")
    return tmp


class AnchorTableTests(unittest.TestCase):
    def test_parses_a_well_formed_table(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            plan = Path(raw) / "Phase7.md"
            plan.write_text(ANCHOR_TABLE, encoding="utf-8")
            rows = parse_anchor_table(plan)
        self.assertEqual(rows, [("AES bytes", "hex-gf2", "HexManual/Tutorials/AESField.lean")])

    def test_missing_table_is_an_error_not_an_empty_parse(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            plan = Path(raw) / "Phase7.md"
            plan.write_text("no table here\n", encoding="utf-8")
            with self.assertRaises(PolicyError):
                parse_anchor_table(plan)

    def test_reformatted_row_is_an_error_not_a_skip(self) -> None:
        table = ANCHOR_TABLE.replace("`hex-gf2`", "hex-gf2")
        with tempfile.TemporaryDirectory() as raw:
            plan = Path(raw) / "Phase7.md"
            plan.write_text(table, encoding="utf-8")
            with self.assertRaises(PolicyError):
                parse_anchor_table(plan)

    def test_duplicate_paths_are_rejected(self) -> None:
        table = ANCHOR_TABLE + "| Other | `hex-gf2` | `HexManual/Tutorials/AESField.lean` |\n"
        with tempfile.TemporaryDirectory() as raw:
            plan = Path(raw) / "Phase7.md"
            plan.write_text(table, encoding="utf-8")
            with self.assertRaises(PolicyError):
                parse_anchor_table(plan)


class TutorialPathTests(unittest.TestCase):
    def test_rejects_absolute_and_traversing_paths(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            for bad in ("/etc/passwd", "../../etc/passwd", "HexManual/Tutorials/../../x.lean"):
                with self.assertRaises(PolicyError):
                    tutorial_module(root, bad)

    def test_rejects_non_lean_and_out_of_directory(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            for bad in ("HexManual/Tutorials/AESField.md", "HexManual/Chapters/HexGF2.lean"):
                with self.assertRaises(PolicyError):
                    tutorial_module(root, bad)


class CheckTests(unittest.TestCase):
    def test_complete_repository_passes(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            self.assertEqual(check(build_root(Path(raw))), [])

    def test_missing_tutorial_fails(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            errors = check(build_root(Path(raw), tutorial=False))
        self.assertTrue(any("is missing at" in error for error in errors))

    def test_unbuilt_tutorial_fails(self) -> None:
        """A file that exists but is never imported proves nothing."""
        with tempfile.TemporaryDirectory() as raw:
            errors = check(build_root(Path(raw), tutorial_import=False, tutorial_include=False))
        self.assertTrue(any("does not import" in error for error in errors))

    def test_unincluded_tutorial_fails(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            errors = check(build_root(Path(raw), tutorial_include=False))
        self.assertTrue(any("never {include}d" in error for error in errors))

    def test_missing_chapter_fails(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            errors = check(build_root(Path(raw), chapter=False))
        self.assertTrue(any("but no HexManual/Chapters" in error for error in errors))

    def test_library_below_seven_is_not_checked(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            errors = check(build_root(Path(raw), done_through=6, tutorial=False, chapter=False))
        self.assertEqual(errors, [])

    def test_unknown_anchor_slug_fails(self) -> None:
        table = ANCHOR_TABLE.replace("`hex-gf2`", "`hex-nonesuch`")
        with tempfile.TemporaryDirectory() as raw:
            errors = check(build_root(Path(raw), table=table))
        self.assertTrue(any("matches no library SPEC slug" in error for error in errors))

    def test_misspelled_slug_does_not_resolve(self) -> None:
        """Hyphen-insensitive matching would resolve `hex-g-f2`; exact slugs do not."""
        table = ANCHOR_TABLE.replace("`hex-gf2`", "`hex-g-f2`")
        with tempfile.TemporaryDirectory() as raw:
            errors = check(build_root(Path(raw), table=table))
        self.assertTrue(any("matches no library SPEC slug" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
