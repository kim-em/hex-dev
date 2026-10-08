#!/usr/bin/env python3
"""Require the module header in tracked Lean sources, without invoking Lean.

Lake configuration is a build script. Files in reports/ are retained artifacts,
not current source. Every other tracked .lean file is checked, including tests,
benchmarks, conformance drivers, examples, experiments and the manual.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def first_token(text: str) -> str:
    """Skip whitespace and nested Lean comments, then read the header token."""
    i = 1 if text.startswith("\ufeff") else 0
    while i < len(text):
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                return ""
        else:
            start = i
            while i < len(text) and not text[i].isspace():
                if text.startswith(("--", "/-"), i):
                    break
                i += 1
            return text[start:i]
    return ""


def is_source(path: Path) -> bool:
    return path.suffix == ".lean" and path.name != "lakefile.lean" and path.parts[0] != "reports"


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    paths = subprocess.check_output(["git", "ls-files", "-z", "*.lean"], cwd=root)
    sources = [Path(p.decode()) for p in paths.split(b"\0") if p and is_source(Path(p.decode()))]
    offenders = [p for p in sources if first_token((root / p).read_text(encoding="utf-8")) != "module"]
    for path in offenders:
        print(f"{path}: missing module header", file=sys.stderr)
    if offenders:
        print(f"{len(offenders)} non-module Lean sources", file=sys.stderr)
        return 1
    print(f"module headers checked: {len(sources)} Lean sources")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
