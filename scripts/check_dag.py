#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re
import sys

from libgraph import (
    EXTERNAL_IMPORT_ROOTS,
    KNOWN_EXCEPTIONS,
    check_lakefile_alignment,
    library_owner_for_path,
    load_lakefile_libs,
    load_libraries,
    may_import,
    reachable_dependencies,
    topological_order,
)


IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")
LEAN_EXE_ROOT_RE = re.compile(r"^\s*root\s*:=\s*`([A-Za-z0-9_.]+)\s*$")
QUALIFIED_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$")


def parse_imports(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = QUALIFIED_IMPORT_RE.match(line.split("--", 1)[0].rstrip())
        if match:
            imports.append(match.group(1))
    return imports


def lean_exe_roots(lakefile: Path) -> set[str]:
    r"""Module names declared as ``lean_exe ... root := `X.Y.Z`/``."""
    roots: set[str] = set()
    for line in lakefile.read_text(encoding="utf-8").splitlines():
        match = LEAN_EXE_ROOT_RE.match(line)
        if match:
            roots.add(match.group(1))
    return roots


def module_name_for(rel_path: Path) -> str:
    """`HexFoo/Bar/Baz.lean` → `HexFoo.Bar.Baz`."""
    return ".".join(rel_path.with_suffix("").parts)


def import_closure_in_library(
    root: Path, entry_module: str, owner: str
) -> set[str]:
    """Modules belonging to `owner` reachable from `entry_module`.

    Walks `import` lines, but only crawls into modules whose name starts
    with `owner.`; that's enough for the umbrella-completeness check,
    which only compares against files under `owner/`.
    """
    seen: set[str] = set()
    stack: list[str] = [entry_module]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        rel = Path(*module.split(".")).with_suffix(".lean")
        path = root / rel
        if not path.exists():
            continue
        seen.add(module)
        for imported in parse_imports(path):
            if imported == owner or imported.startswith(owner + "."):
                stack.append(imported)
    return seen


def check_umbrella_completeness(
    root: Path, libraries, exe_roots: set[str]
) -> list[str]:
    """Every regular module under `Foo/` must be reachable from either
    `Foo.lean` (umbrella) or some `lean_exe` root.

    A module reachable only from a `lean_exe` root is still absent from
    the library's shared object `libHex_Foo.dylib`, but that's fine —
    its symbols ship with the executable and downstream libraries don't
    expect to call into bench / emit-fixture code.
    """
    errors: list[str] = []
    for owner in libraries:
        directory = root / owner
        if not directory.is_dir():
            continue
        umbrella_path = root / f"{owner}.lean"
        if not umbrella_path.exists():
            continue
        reachable = import_closure_in_library(root, owner, owner)
        for exe_root in exe_roots:
            reachable |= import_closure_in_library(root, exe_root, owner)
        for lean_file in sorted(directory.rglob("*.lean")):
            module = module_name_for(lean_file.relative_to(root))
            if module in exe_roots:
                continue
            if module in reachable:
                continue
            errors.append(
                f"{owner}.lean does not (transitively) import {module}; "
                "add it to the umbrella, or declare it as a lean_exe root"
            )
    return errors


def project_lean_files(root: Path) -> list[Path]:
    files = []
    for path in root.rglob("*.lean"):
        if ".lake" in path.parts or "released" in path.parts:
            continue
        files.append(path.relative_to(root))
    return sorted(files)


def import_roots(line: str) -> list[str]:
    match = IMPORT_RE.match(line.split("--", 1)[0].rstrip())
    if not match:
        return []
    roots = []
    for token in match.group(1).replace(",", " ").split():
        token = token.strip()
        if token:
            roots.append(token.split(".", 1)[0])
    return roots


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    errors: list[str] = []

    try:
        libraries = load_libraries(root / "libraries.yml")
        lakefile_libs = load_lakefile_libs(root)
        topological_order(libraries)
        reachable = reachable_dependencies(libraries)
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1

    errors.extend(check_lakefile_alignment(libraries, lakefile_libs))

    # Root-file existence per PLAN/Conventions.md §"Library status":
    #   active local entry  ⟺  <Name>.lean exists at repo root
    #   planned/draft entry  ⟹  <Name>.lean must not exist
    # External libraries are consumed via a git `require`; their sources
    # (root file included) live in the released repo, not locally, so they
    # are exempt from the local root-file existence check.
    active_names = [
        name for name, info in libraries.items()
        if info.is_active and not info.is_external
    ]
    nonactive_names = [name for name, info in libraries.items() if not info.is_active]
    for name in active_names + sorted(KNOWN_EXCEPTIONS):
        if not (root / f"{name}.lean").exists():
            errors.append(f"missing root file {name}.lean")
    for name in nonactive_names:
        if (root / f"{name}.lean").exists():
            info = libraries[name]
            errors.append(
                f"{name}.lean exists at repo root but {name} has status: {info.status}; "
                f"non-active libraries must not have a root file"
            )

    exe_roots = lean_exe_roots(root / "lakefile.lean")
    errors.extend(check_umbrella_completeness(root, libraries, exe_roots))

    for rel_path in project_lean_files(root):
        owner = library_owner_for_path(rel_path, libraries)
        if owner is None:
            continue
        path = root / rel_path
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for imported_root in import_roots(line):
                if imported_root == owner:
                    continue
                if imported_root == "Mathlib":
                    if owner != "HexManual" and not libraries[owner].mathlib:
                        errors.append(
                            f"{rel_path}:{line_no} imports Mathlib but {owner} is not a mathlib bridge"
                        )
                    continue
                if imported_root == "Verso":
                    if owner != "HexManual":
                        errors.append(f"{rel_path}:{line_no} imports Verso outside HexManual")
                    continue
                if imported_root in libraries:
                    if (
                        owner in libraries
                        and owner != "HexManual"
                        and not may_import(owner, imported_root, libraries, reachable)
                    ):
                        errors.append(
                            f"{rel_path}:{line_no} imports {imported_root} without a dependency path from {owner}"
                        )
                    continue
                if imported_root in EXTERNAL_IMPORT_ROOTS:
                    continue

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
