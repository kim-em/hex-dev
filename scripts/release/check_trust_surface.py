#!/usr/bin/env python3
"""Reject trust holes across every source library in the release manifest."""

from __future__ import annotations

import re
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = REPO_ROOT / "scripts" / "release" / "released.yml"
FORBIDDEN = re.compile(r"\b(?:axiom|sorry|native_decide)\b")


def code_without_comments_and_strings(source: str) -> str:
    """Keep Lean code while blanking nested comments and string literals."""
    out: list[str] = []
    index = 0
    comment_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if comment_depth:
            if pair == "/-":
                comment_depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                comment_depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            out.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            comment_depth = 1
            out.extend("  ")
            index += 2
        elif pair == "--":
            newline = source.find("\n", index + 2)
            if newline == -1:
                out.extend(" " * (len(source) - index))
                break
            out.extend(" " * (newline - index))
            out.append("\n")
            index = newline + 1
        elif char == '"':
            in_string = True
            out.append(" ")
            index += 1
        else:
            out.append(char)
            index += 1
    return "".join(out)


def main() -> int:
    document = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    entries = document.get("repos") if isinstance(document, dict) else None
    if not isinstance(entries, list):
        print(f"{MANIFEST.relative_to(REPO_ROOT)}: repos must be a list")
        return 1

    files: set[Path] = set()
    for entry in entries:
        if not isinstance(entry, dict) or entry.get("pins_only"):
            continue
        library = entry.get("lib")
        if not isinstance(library, str):
            print("release manifest contains a non-aggregate entry without a library")
            return 1
        umbrella = REPO_ROOT / f"{library}.lean"
        if umbrella.is_file():
            files.add(umbrella)
        directory = REPO_ROOT / library
        if directory.is_dir():
            files.update(directory.rglob("*.lean"))

    failures: list[str] = []
    for path in sorted(files):
        code = code_without_comments_and_strings(path.read_text(encoding="utf-8"))
        for line_number, line in enumerate(code.splitlines(), start=1):
            match = FORBIDDEN.search(line)
            if match:
                failures.append(
                    f"{path.relative_to(REPO_ROOT)}:{line_number}: forbidden "
                    f"{match.group(0)}"
                )

    if failures:
        print("\n".join(failures))
        return 1
    print(
        f"published trust surface: {len(files)} Lean files contain no axioms, "
        "sorries, or native_decide"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
