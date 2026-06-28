#!/usr/bin/env python3
"""Enforce Mathlib-style copyright headers on every tracked Lean source file.

Every `.lean` file tracked by git (excluding `lakefile.lean`) must open with
a plain block-comment header of the form:

    /-
    Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Kim Morrison
    -/

The copyright and license lines are matched exactly (the year may be any four
digits); the `Authors:` line may name anyone, so long as it is non-empty.

Default mode checks every file and exits non-zero, listing offenders, if any
header is missing or malformed. `--fix` prepends the canonical header (with the
current `YEAR`) to any non-compliant file and is idempotent.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

YEAR = "2026"

HEADER = (
    "/-\n"
    f"Copyright (c) {YEAR} Lean FRO, LLC. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: Kim Morrison\n"
    "-/\n"
)

COPYRIGHT_RE = re.compile(
    r"^Copyright \(c\) \d{4} Lean FRO, LLC\. All rights reserved\.$"
)
LICENSE_LINE = "Released under Apache 2.0 license as described in the file LICENSE."

# Tracked `.lean` files that should NOT carry a header.
EXCLUDED = {"lakefile.lean"}


def tracked_lean_files(repo_root: Path) -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "*.lean"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    files = [repo_root / line for line in out.splitlines() if line]
    return [f for f in files if f.name not in EXCLUDED]


def header_ok(text: str) -> bool:
    """Return True if `text` begins with a well-formed copyright header."""
    lines = text.splitlines()
    if len(lines) < 5:
        return False
    if lines[0] != "/-":
        return False
    if not COPYRIGHT_RE.match(lines[1]):
        return False
    if lines[2] != LICENSE_LINE:
        return False
    # One or more author lines, then the closing `-/`. The author block must
    # start with `Authors:` and contain a non-empty author list.
    if not lines[3].startswith("Authors:"):
        return False
    if not lines[3][len("Authors:"):].strip():
        return False
    for i in range(3, len(lines)):
        if lines[i] == "-/":
            return True
    return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fix",
        action="store_true",
        help="prepend the canonical header to any non-compliant file",
    )
    args = parser.parse_args()

    repo_root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    )

    offenders: list[Path] = []
    fixed: list[Path] = []
    for path in tracked_lean_files(repo_root):
        text = path.read_text(encoding="utf-8")
        if header_ok(text):
            continue
        if args.fix:
            path.write_text(HEADER + "\n" + text, encoding="utf-8")
            fixed.append(path)
        else:
            offenders.append(path)

    if args.fix:
        for path in fixed:
            print(f"fixed: {path.relative_to(repo_root)}")
        print(f"{len(fixed)} file(s) updated.")
        return 0

    if offenders:
        print(
            "Missing or malformed copyright header in the following file(s):",
            file=sys.stderr,
        )
        for path in offenders:
            print(f"  {path.relative_to(repo_root)}", file=sys.stderr)
        print(
            "\nEvery tracked .lean file (except lakefile.lean) must start with:\n\n"
            + HEADER
            + "\nRun `python3 scripts/check_copyright_headers.py --fix` to add it.",
            file=sys.stderr,
        )
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
