#!/usr/bin/env python3
"""Keep the manual's released/unreleased split honest.

`HexManual.lean` documents released libraries in the body and parks the rest
under "Draft sections for unreleased libraries". Nothing used to connect that
split to `released.yml`, so the manual lagged the releases by a dozen
libraries. This check derives the split from the manifest and fails when a
chapter sits on the wrong side of it, or when a chapter file is not included
at all.

Chapters are matched to libraries by name (`HexManual/Chapters/HexLLL.lean`
documents `HexLLL`). A chapter that documents something other than a
same-named library declares its libraries in CHAPTER_LIBRARIES below.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = REPO_ROOT / "scripts" / "release" / "released.yml"
MANUAL = REPO_ROOT / "HexManual.lean"
CHAPTERS = REPO_ROOT / "HexManual" / "Chapters"
UNRELEASED_HEADING = "# Draft sections for unreleased libraries"
INCLUDE = re.compile(r"^\{include (?P<level>\d+) HexManual\.Chapters\.(?P<chapter>\w+)\}$", re.M)

# Chapters whose name is not a library name, mapped to the libraries they
# document. A chapter is released when all of them are.
CHAPTER_LIBRARIES = {
    "FactorTactics": ["HexBerlekampMathlib", "HexBerlekampZassenhausMathlib"],
    "HexSmith": ["HexSmith", "HexSmithMathlib"],
}

# Include level: released chapters sit at the top level, unreleased ones are
# nested under the draft heading.
RELEASED_LEVEL = "0"
UNRELEASED_LEVEL = "2"


def _names(libraries: list[str]) -> str:
    """`HexLLL is` / `HexA and HexB are`, for readable failure messages."""
    return f"{' and '.join(libraries)} {'is' if len(libraries) == 1 else 'are'}"


def released_libraries() -> set[str]:
    document = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    return {entry["lib"] for entry in document["repos"] if entry.get("lib")}


def main() -> int:
    released = released_libraries()
    text = MANUAL.read_text(encoding="utf-8")
    split = text.find(UNRELEASED_HEADING)
    if split < 0:
        print(f"manual split: FAIL: {MANUAL.name} has no {UNRELEASED_HEADING!r} heading",
              file=sys.stderr)
        return 1

    problems: list[str] = []
    seen: list[str] = []
    for match in INCLUDE.finditer(text):
        chapter = match.group("chapter")
        seen.append(chapter)
        libraries = CHAPTER_LIBRARIES.get(chapter, [chapter])
        unknown = [lib for lib in libraries if not (REPO_ROOT / lib).is_dir()]
        if unknown:
            problems.append(f"{chapter}: documents no such library {unknown}")
            continue
        is_released = all(lib in released for lib in libraries)
        in_body = match.start() < split
        if is_released and not in_body:
            problems.append(
                f"{chapter}: {_names(libraries)} released, so the chapter belongs "
                f"above {UNRELEASED_HEADING!r} at include level {RELEASED_LEVEL}")
        elif not is_released and in_body:
            unreleased = [lib for lib in libraries if lib not in released]
            problems.append(
                f"{chapter}: {_names(unreleased)} not in released.yml, so the chapter "
                f"belongs under {UNRELEASED_HEADING!r} at include level "
                f"{UNRELEASED_LEVEL}")
        else:
            expected = RELEASED_LEVEL if is_released else UNRELEASED_LEVEL
            if match.group("level") != expected:
                problems.append(
                    f"{chapter}: include level {match.group('level')} should be {expected}")

    duplicated = sorted({chapter for chapter in seen if seen.count(chapter) > 1})
    if duplicated:
        problems.append(f"chapters included more than once: {duplicated}")
    missing = sorted({path.stem for path in CHAPTERS.glob("*.lean")} - set(seen))
    if missing:
        problems.append(f"chapters never included in {MANUAL.name}: {missing}")

    if problems:
        print("manual split: FAIL", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    body = sum(1 for match in INCLUDE.finditer(text) if match.start() < split)
    print(f"manual split: {body} released chapters, {len(seen) - body} draft chapters, "
          "consistent with released.yml")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
