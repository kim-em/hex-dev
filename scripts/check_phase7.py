#!/usr/bin/env python3
"""Enforce the Phase 7 exit criteria for libraries recorded as done.

`PLAN/Phase7.md` says a library reaches `done_through: 7` when it has a
reference chapter that builds inside `HexManual`, and when every tutorial
anchored to it exists. Nothing checked either, so both drifted: two anchored
tutorials were missing while their anchor libraries sat at 7.

Three rules, applied to every library with `done_through >= 7`:

* **Chapter.** The library has `HexManual/Chapters/<Lib>.lean`, or, for a
  `mathlib: true` companion, a `# The Mathlib correspondence` section inside
  its computational partner's chapter. The second form is the established
  convention: no `*Mathlib` library has its own chapter, and several sit at 7
  on the strength of a section in the partner's.
* **Imported.** `HexManual.lean` imports the chapter, so `lake build HexManual`
  actually elaborates it.
* **Tutorials.** Every tutorial anchored to the library in `PLAN/Phase7.md`
  exists at the path that table records.

The anchor table is parsed from `PLAN/Phase7.md` rather than duplicated here,
so re-anchoring a tutorial is a one-file edit.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from libgraph import load_libraries

CORRESPONDENCE_HEADING = "# The Mathlib correspondence"

# Libraries recorded at Phase 7 without a chapter, with the reason. These are
# reported as notices rather than errors so the exception stays visible instead
# of being silently tolerated. Emptying this map is the goal.
CHAPTER_EXEMPT: dict[str, str] = {
    "HexBasic": (
        "shared helpers with no user-facing API; predates this check and needs "
        "either a chapter or a rollback, which is a call for the planner"
    ),
}

ANCHOR_ROW_RE = re.compile(
    r"^\|\s*(?P<tutorial>[^|]+?)\s*\|\s*`(?P<anchor>[a-z0-9-]+)`\s*\|"
    r"\s*`(?P<path>[^`]+)`\s*\|\s*$"
)


def resolve_anchor(slug: str, library_names: list[str]) -> str | None:
    """Map a SPEC slug like `hex-lll` to its library name like `HexLLL`.

    Compared case-insensitively with separators removed, since the two spellings
    differ in capitalization (`HexLLL`, `HexGF2`) in ways no rule reproduces.
    """
    flattened = slug.replace("-", "").lower()
    for name in library_names:
        if name.lower() == flattened:
            return name
    return None


def parse_anchor_table(plan: Path) -> list[tuple[str, str, str]]:
    """Read the tutorial anchor table: (tutorial, anchor slug, source path)."""
    rows: list[tuple[str, str, str]] = []
    for line in plan.read_text(encoding="utf-8").splitlines():
        match = ANCHOR_ROW_RE.match(line)
        if match and match.group("tutorial") != "Tutorial":
            rows.append(
                (match.group("tutorial"), match.group("anchor"), match.group("path"))
            )
    return rows


def partner_chapter(root: Path, name: str) -> Path | None:
    """The computational partner's chapter for a `*Mathlib` library."""
    if not name.endswith("Mathlib"):
        return None
    chapter = root / "HexManual" / "Chapters" / f"{name[: -len('Mathlib')]}.lean"
    return chapter if chapter.exists() else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    root = args.root

    libraries = load_libraries(root / "libraries.yml")
    manual_root = (root / "HexManual.lean").read_text(encoding="utf-8")
    anchors = parse_anchor_table(root / "PLAN" / "Phase7.md")

    errors: list[str] = []
    notices: list[str] = []

    for name, library in sorted(libraries.items()):
        if library.done_through < 7:
            continue
        if name in CHAPTER_EXEMPT:
            notices.append(f"{name}: chapter exemption -- {CHAPTER_EXEMPT[name]}")
            continue

        chapter = root / "HexManual" / "Chapters" / f"{name}.lean"
        if chapter.exists():
            module = f"HexManual.Chapters.{name}"
            if f"import {module}" not in manual_root:
                errors.append(
                    f"{name}: has {chapter.relative_to(root)} but HexManual.lean does not "
                    f"import {module}, so `lake build HexManual` never elaborates it"
                )
        else:
            partner = partner_chapter(root, name)
            if partner is None:
                errors.append(
                    f"{name}: done_through 7 but no HexManual/Chapters/{name}.lean, and it is "
                    f"not a Mathlib companion whose partner chapter could carry it"
                )
            elif CORRESPONDENCE_HEADING not in partner.read_text(encoding="utf-8"):
                errors.append(
                    f"{name}: done_through 7 but neither HexManual/Chapters/{name}.lean nor a "
                    f"'{CORRESPONDENCE_HEADING}' section in {partner.relative_to(root)}"
                )

    for tutorial, anchor, path in anchors:
        anchor_library = resolve_anchor(anchor, list(libraries))
        library = libraries.get(anchor_library) if anchor_library else None
        if library is None:
            errors.append(
                f"PLAN/Phase7.md anchors '{tutorial}' to unknown library `{anchor}`"
            )
            continue
        if library.done_through >= 7 and not (root / path).exists():
            errors.append(
                f"{anchor_library}: done_through 7 but its anchored tutorial '{tutorial}' "
                f"is missing at {path}"
            )

    for notice in notices:
        print(f"notice: {notice}")

    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        print(
            f"\n{len(errors)} Phase 7 obligation(s) unmet. Either finish the work or roll "
            f"the library back per PLAN/Conventions.md.",
            file=sys.stderr,
        )
        return 1

    print("OK: Phase 7 obligations met for all done_through >= 7 libraries.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
