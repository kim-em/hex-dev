#!/usr/bin/env python3
"""Enforce the Phase 7 exit criteria for libraries recorded as done.

`PLAN/Phase7.md` says a library reaches `done_through: 7` when it has a
reference chapter that builds inside `HexManual`, and when every tutorial
anchored to it exists. Nothing checked either, so both drifted.

Three rules, applied to every library with `done_through >= 7`:

* **Chapter.** A `mathlib: true` companion named `<X>Mathlib` needs a
  `# The Mathlib correspondence` section in `<X>`'s chapter. A `mathlib: true`
  library without that suffix is integrated (HexRCF): it has no computational
  partner and carries its own chapter like any other library. Every other
  library needs `HexManual/Chapters/<Lib>.lean`.
* **Reachable.** `HexManual.lean` imports the chapter, so `lake build
  HexManual` elaborates it.
* **Tutorials.** Every tutorial anchored to the library exists, is imported by
  `HexManual.lean`, and is `{include}`d in it. A file that is present but not
  built proves nothing, so presence alone is not accepted.

The anchor table is parsed from `PLAN/Phase7.md` rather than duplicated here,
so re-anchoring a tutorial is a one-file edit. The parse is strict: a table
that has moved, gained a column, or lost its backticks is an error rather than
zero rows and a green result, because a checker that fails open is worse than
no checker.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from libgraph import load_libraries

CORRESPONDENCE_HEADING = "# The Mathlib correspondence"
TUTORIAL_DIR = "HexManual/Tutorials"

ANCHOR_HEADER_RE = re.compile(r"^\|\s*Tutorial\s*\|\s*Anchor library\s*\|\s*Source file\s*\|\s*$")
ANCHOR_RULE_RE = re.compile(r"^\|[-\s|]+\|$")
ANCHOR_ROW_RE = re.compile(
    r"^\|\s*(?P<tutorial>[^|`]+?)\s*\|\s*`(?P<anchor>[a-z0-9-]+)`\s*\|"
    r"\s*`(?P<path>[^`]+)`\s*\|\s*$"
)


class PolicyError(Exception):
    """The policy files themselves are malformed, as distinct from a library
    failing to meet the policy."""


def spec_slugs(root: Path) -> dict[str, str]:
    """Map each library's SPEC slug to its directory name.

    Derived from the committed SPEC paths (`HexGF2/SPEC/hex-gf2.md`) rather
    than by transliterating the name, so `hex-lll` and `hex-gf2` resolve
    exactly and a misspelling resolves to nothing.
    """
    mapping: dict[str, str] = {}
    for spec in sorted(root.glob("Hex*/SPEC/*.md")):
        library = spec.parent.parent.name
        slug = spec.stem
        if slug in mapping and mapping[slug] != library:
            raise PolicyError(f"SPEC slug '{slug}' claimed by both {mapping[slug]} and {library}")
        mapping[slug] = library
    return mapping


def parse_anchor_table(plan: Path) -> list[tuple[str, str, str]]:
    """Read the tutorial anchor table: (tutorial, anchor slug, source path)."""
    lines = plan.read_text(encoding="utf-8").splitlines()
    header_at = next((i for i, line in enumerate(lines) if ANCHOR_HEADER_RE.match(line)), None)
    if header_at is None:
        raise PolicyError(
            f"{plan}: no tutorial anchor table; expected a header row "
            f"'| Tutorial | Anchor library | Source file |'"
        )
    if not ANCHOR_RULE_RE.match(lines[header_at + 1]):
        raise PolicyError(f"{plan}:{header_at + 2}: anchor table header is not followed by a rule row")

    rows: list[tuple[str, str, str]] = []
    for offset, line in enumerate(lines[header_at + 2 :], start=header_at + 3):
        if not line.startswith("|"):
            break
        match = ANCHOR_ROW_RE.match(line)
        if match is None:
            raise PolicyError(f"{plan}:{offset}: malformed anchor row: {line!r}")
        rows.append((match.group("tutorial"), match.group("anchor"), match.group("path")))

    if not rows:
        raise PolicyError(f"{plan}: the tutorial anchor table has no rows")
    for column, index in (("tutorial", 0), ("path", 2)):
        seen = [row[index] for row in rows]
        duplicates = {value for value in seen if seen.count(value) > 1}
        if duplicates:
            raise PolicyError(f"{plan}: duplicate {column} in the anchor table: {sorted(duplicates)}")
    return rows


def tutorial_module(root: Path, path: str) -> str:
    """Validate a tutorial path and return its Lean module name."""
    if path.startswith("/") or ".." in Path(path).parts:
        raise PolicyError(f"anchor table path escapes the repository: {path!r}")
    if not path.startswith(TUTORIAL_DIR + "/") or not path.endswith(".lean"):
        raise PolicyError(f"anchor table path is not a {TUTORIAL_DIR}/*.lean file: {path!r}")
    resolved = (root / path).resolve()
    if not resolved.is_relative_to((root / TUTORIAL_DIR).resolve()):
        raise PolicyError(f"anchor table path resolves outside {TUTORIAL_DIR}: {path!r}")
    return "HexManual.Tutorials." + Path(path).stem


def imports_module(manual_root: str, module: str) -> bool:
    """Whether `HexManual.lean` imports exactly this module, ignoring comments."""
    pattern = re.compile(rf"^\s*import\s+{re.escape(module)}\s*$", re.MULTILINE)
    return pattern.search(manual_root) is not None


def includes_module(manual_root: str, module: str) -> bool:
    """Whether `HexManual.lean` `{include}`s exactly this module."""
    pattern = re.compile(rf"\{{include\s+\d+\s+{re.escape(module)}\}}")
    return pattern.search(manual_root) is not None


def partner_chapter(root: Path, name: str) -> Path | None:
    """The computational partner's chapter for a `*Mathlib` library."""
    if not name.endswith("Mathlib"):
        return None
    chapter = root / "HexManual" / "Chapters" / f"{name[: -len('Mathlib')]}.lean"
    return chapter if chapter.is_file() else None


def check(root: Path) -> list[str]:
    libraries = load_libraries(root / "libraries.yml")
    manual_root = (root / "HexManual.lean").read_text(encoding="utf-8")
    anchors = parse_anchor_table(root / "PLAN" / "Phase7.md")
    slugs = spec_slugs(root)

    errors: list[str] = []

    for name, library in sorted(libraries.items()):
        if library.done_through < 7:
            continue

        chapter = root / "HexManual" / "Chapters" / f"{name}.lean"
        partner = partner_chapter(root, name)
        # An integrated `mathlib: true` library (no `Mathlib` suffix, e.g.
        # HexRCF) has no computational partner; it carries its own chapter and
        # falls through to the plain-library branch.
        if library.mathlib and name.endswith("Mathlib"):
            if partner is None:
                errors.append(
                    f"{name}: done_through 7, but no computational partner chapter exists to "
                    f"carry its '{CORRESPONDENCE_HEADING}' section"
                )
            elif CORRESPONDENCE_HEADING not in partner.read_text(encoding="utf-8"):
                errors.append(
                    f"{name}: done_through 7, but {partner.relative_to(root)} has no "
                    f"'{CORRESPONDENCE_HEADING}' section (PLAN/Phase7.md)"
                )
        elif not chapter.is_file():
            errors.append(f"{name}: done_through 7, but no {chapter.relative_to(root)}")
        elif not imports_module(manual_root, f"HexManual.Chapters.{name}"):
            errors.append(
                f"{name}: has {chapter.relative_to(root)}, but HexManual.lean does not import "
                f"HexManual.Chapters.{name}, so lake build HexManual never elaborates it"
            )

    for tutorial, anchor, path in anchors:
        anchor_library = slugs.get(anchor)
        if anchor_library is None:
            errors.append(
                f"PLAN/Phase7.md anchors '{tutorial}' to `{anchor}`, which matches no "
                f"library SPEC slug"
            )
            continue
        library = libraries.get(anchor_library)
        if library is None:
            errors.append(f"PLAN/Phase7.md anchors '{tutorial}' to unknown library {anchor_library}")
            continue
        if library.done_through < 7:
            continue
        module = tutorial_module(root, path)
        if not (root / path).is_file():
            errors.append(
                f"{anchor_library}: done_through 7, but its anchored tutorial '{tutorial}' "
                f"is missing at {path}"
            )
        elif not imports_module(manual_root, module):
            errors.append(
                f"{anchor_library}: {path} exists but HexManual.lean does not import {module}, "
                f"so it is never built"
            )
        elif not includes_module(manual_root, module):
            errors.append(
                f"{anchor_library}: {path} is imported but never {{include}}d in HexManual.lean, "
                f"so it does not appear in the rendered manual"
            )

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()

    try:
        errors = check(args.root)
    except PolicyError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

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
