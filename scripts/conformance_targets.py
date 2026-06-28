#!/usr/bin/env python3
"""Derive the list of libraries whose ``Hex*/Conformance.lean`` module
is imported from the matching root ``Hex*.lean``.

Used by ``.github/workflows/conformance.yml`` to build the conformance
matrix dynamically instead of hand-listing targets.  The list is
recomputed every CI run, so new ``Hex*/Conformance.lean`` files land in
the matrix automatically.

Default output is one library name per line on stdout.  ``--json``
emits a JSON array suitable for a GitHub Actions matrix include.
``--space-separated`` emits a single space-joined line, which feeds
the consolidated single-job ``conformance.yml`` workflow's
``lake build`` invocation.  ``--check`` performs the consistency
check without printing the list and exits non-zero on drift between
``Hex*/Conformance.lean`` files and root-module imports.

Stdlib only; runs from the repository root regardless of the working
directory the user invokes it from.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


CONFORMANCE_GLOB_RE = re.compile(r"`([A-Za-z0-9_]+)\.Conformance\b")


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def discover_conformance_files(root: Path) -> list[str]:
    """Library names with a ``conformance/Hex*/Conformance.lean`` source file."""
    libs: list[str] = []
    for path in root.glob("conformance/Hex*/Conformance.lean"):
        libs.append(path.parent.name)
    return sorted(libs)


def discover_conformance_imports(root: Path) -> list[str]:
    """Library names whose Conformance module is built by the `HexConformance`
    lean_lib in ``lakefile.lean`` (parsed from its ``globs`` list)."""
    text = (root / "lakefile.lean").read_text(encoding="utf-8")
    return sorted({m.group(1) for m in CONFORMANCE_GLOB_RE.finditer(text)})


def diagnose(root: Path) -> tuple[list[str], list[str], list[str]]:
    """Return ``(targets, errors, warnings)``.

    ``targets`` is the list of libraries that have both a Conformance
    file under ``conformance/`` and an entry in the ``HexConformance``
    lean_lib globs, i.e. those actually built.
    """
    files = discover_conformance_files(root)
    imports = discover_conformance_imports(root)
    files_set = set(files)
    imports_set = set(imports)
    targets = sorted(files_set & imports_set)

    errors: list[str] = []
    for lib in sorted(files_set - imports_set):
        errors.append(
            f"conformance/{lib}/Conformance.lean exists but {lib}.Conformance "
            f"is not in the HexConformance lean_lib globs in lakefile.lean"
        )

    warnings: list[str] = []
    for lib in sorted(imports_set - files_set):
        warnings.append(
            f"HexConformance globs {lib}.Conformance but "
            f"conformance/{lib}/Conformance.lean does not exist"
        )

    return targets, errors, warnings


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "List libraries whose Hex*/Conformance.lean module is "
            "imported from the matching root Hex*.lean.  Used to derive "
            "the conformance CI matrix."
        )
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit the list as a JSON array on stdout",
    )
    parser.add_argument(
        "--space-separated",
        action="store_true",
        help=(
            "emit the list as a single space-joined line on stdout "
            "(suitable for `lake build $(... --space-separated)`)"
        ),
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "verify root-imports and Conformance.lean files are in sync; "
            "do not print the matrix; exit non-zero on drift"
        ),
    )
    parser.add_argument(
        "--no-warn-orphan-imports",
        action="store_true",
        help=(
            "suppress warnings about root files that import a "
            "Conformance module without a backing source file "
            "(such drift makes lake build fail anyway)"
        ),
    )
    args = parser.parse_args()

    exclusive = sum(
        1 for flag in (args.json, args.space_separated, args.check) if flag
    )
    if exclusive > 1:
        parser.error(
            "--json, --space-separated, and --check are mutually exclusive"
        )

    targets, errors, warnings = diagnose(repo_root())

    for err in errors:
        print(f"error: {err}", file=sys.stderr)
    if not args.no_warn_orphan_imports:
        for warning in warnings:
            print(f"warning: {warning}", file=sys.stderr)

    if args.check:
        return 1 if errors else 0

    if errors:
        return 1

    if args.json:
        json.dump(targets, sys.stdout)
        sys.stdout.write("\n")
    elif args.space_separated:
        print(" ".join(targets))
    else:
        for name in targets:
            print(name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
