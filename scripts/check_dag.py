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
    pascal_to_spec_path,
    reachable_dependencies,
    topological_order,
)


IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(.+?)\s*$"
)
LEAN_EXE_ROOT_RE = re.compile(r"^\s*root\s*:=\s*`([A-Za-z0-9_.]+)\s*$")
LEAN_GLOB_MODULE_RE = re.compile(r"`([A-Z][A-Za-z0-9_.]+)")
LEAN_LIB_RE = re.compile(r"^lean_lib\s+([A-Za-z0-9_]+)\b")
LEAN_EXE_RE = re.compile(r"^lean_exe\s+([A-Za-z0-9_]+)\b")
QUALIFIED_IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([A-Za-z0-9_.]+)\s*$"
)
IMPORT_ALL_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+all\s+([A-Za-z0-9_.]+)\s*$"
)
OWNER_RE = re.compile(
    r"^Computational (conformance|performance) owners?:\s*(.+)$",
    re.MULTILINE,
)
OWNER_NAME_RE = re.compile(r"`([A-Z][A-Za-z0-9_]*)`")
RUNTIME_CHECK_RE = re.compile(r"^\s*#(?:eval|guard|reduce|run)\b")

# Private constructors in these modules are an ordinary/public-import API
# boundary. `import all` is a deliberate trusted-internals escape hatch, so
# every owning exception must be an exact reviewed path rather than a suffix or
# directory convention. There are currently no required exceptions.
SEALED_IMPORT_ALL_ALLOWLIST: dict[str, frozenset[Path]] = {
    "HexInterval.Executable": frozenset(),
    "HexInterval.Runtime": frozenset(),
    "HexInterval.RuntimeController": frozenset(),
    "HexInterval.Search": frozenset(),
    "HexIntervalMathlib.Driver": frozenset(),
    "HexIntervalMathlib.Controller": frozenset(),
    "HexIntervalMathlib.Proof": frozenset(),
    "HexIntervalMathlib.RuntimeProof": frozenset(),
    "HexIntervalMathlib.RuntimeTerminal": frozenset(),
}

UMBRELLA_BUILD_TARGETS = {
    "HexLLLBenchSupport",
    "HexGF2BenchSupport",
    "HexBerlekampKernelProbe",
    "HexPrimalityKernelProbe",
    "HexPrimalityElabProbe",
    "HexPrimalityElabProbeScientific",
    "HexPrimalityMathlibProofProbe",
    "HexIntFactorKernelProbe",
    "HexMvGcdKernelProbe",
    "HexMvGcdBenchSupport",
    "HexMvPolyBenchSupport",
    "HexModularBenchSupport",
    "HexMvPolyMathlibProofProbe",
    "HexBerlekampZassenhausMathlibProofProbe",
    "HexBerlekampZassenhausMathlibProofProbeScientific",
    "HexBerlekampMathlibProofProbe",
    "HexBerlekampMathlibProofProbeScientific",
    "HexIntervalExperiment",
    "HexIntervalMathlibExperiment",
    "HexIntervalPntFks2Local",
    "HexIntervalPntFks2ConformanceLocal",
    "HexIntervalReplayProbe",
    "HexIntervalMathlibReplayProbe",
    "HexRealRootsMathlibReplayProbe",
    "HexRealRootsMathlibReplayProbeScientific",
    "HexRCFProofProbe",
    "HexRCFProofProbeScientific",
    "HexConformance",
    "HexFactorizationModules",
    "HexMvFactorizationTests",
    "HexReleaseTests",
    "HexSparsePolyTests",
    "HexTruncatedSeriesTests",
    "HexSmithTests",
    "HexGraphIsoTests",
    "HexCharPolyTests",
    "HexReleaseExamples",
}


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


def lean_glob_modules(lakefile: Path, targets: set[str]) -> set[str]:
    r"""Explicit module names in selected build-only Lake targets.

    A production library glob is not an alternative to reachability from its
    public umbrella. Only the named verification/bench support targets may own
    modules that are intentionally absent from a shipped umbrella.
    """
    modules: set[str] = set()
    current_target: str | None = None
    in_globs = False
    for line in lakefile.read_text(encoding="utf-8").splitlines():
        target_match = LEAN_LIB_RE.match(line)
        if target_match:
            current_target = target_match.group(1)
            in_globs = False
        elif line and not line[0].isspace():
            current_target = None
            in_globs = False
        if current_target not in targets:
            continue
        if "globs := #[" in line:
            in_globs = True
        if in_globs:
            modules.update(LEAN_GLOB_MODULE_RE.findall(line))
            if "]" in line:
                in_globs = False
    return modules


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
    root: Path, libraries, build_roots: set[str]
) -> list[str]:
    """Every regular module under `Foo/` must be reachable from either
    `Foo.lean` (umbrella) or an explicit Lake executable/glob root.

    A module reachable only from a separate build root is still absent from
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
        for build_root in build_roots:
            reachable |= import_closure_in_library(root, build_root, owner)
        for lean_file in sorted(directory.rglob("*.lean")):
            module = module_name_for(lean_file.relative_to(root))
            if module in build_roots:
                continue
            if module in reachable:
                continue
            errors.append(
                f"{owner}.lean does not (transitively) import {module}; "
                "add it to the umbrella, or declare it as an explicit Lake build root"
            )
    return errors


def project_lean_files(root: Path) -> list[Path]:
    files = []
    for path in root.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        files.append(path.relative_to(root))
    return sorted(files)


def check_sealed_import_all(root: Path, files: list[Path]) -> list[str]:
    """Reject trusted-internals imports outside exact reviewed owning paths.

    This scan deliberately covers every project Lean file, including roots such
    as ``conformance/`` and ``bench/`` which have no library DAG owner.
    """
    errors = []
    for rel_path in files:
        path = root / rel_path
        for line_no, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1
        ):
            import_all = IMPORT_ALL_RE.match(line.split("--", 1)[0].rstrip())
            if not import_all:
                continue
            module = import_all.group(1)
            allowed = SEALED_IMPORT_ALL_ALLOWLIST.get(module)
            if allowed is not None and rel_path not in allowed:
                errors.append(
                    f"{rel_path}:{line_no} uses `import all {module}` outside its "
                    "exact trusted-internals allowlist"
                )
    return errors


def check_correspondence_only(root: Path, libraries, lakefile: Path) -> list[str]:
    """Check repository-owned state for explicitly correspondence-only layers."""
    errors: list[str] = []
    lake_text = lakefile.read_text(encoding="utf-8")
    exe_names = {
        match.group(1)
        for line in lake_text.splitlines()
        if (match := LEAN_EXE_RE.match(line))
    }
    build_modules = lean_glob_modules(lakefile, UMBRELLA_BUILD_TARGETS)
    reachable = reachable_dependencies(libraries)

    for name, info in libraries.items():
        if not info.correspondence_only:
            continue

        conformance_dir = root / "conformance" / name
        conformance_files = (
            sorted(conformance_dir.rglob("*.lean"))
            if conformance_dir.is_dir()
            else []
        )
        if conformance_files:
            errors.append(
                f"{name} declares correspondence_only but owns conformance source "
                f"{conformance_files[0].relative_to(root)}"
            )
        if re.search(
            rf"`{re.escape(name)}\.[A-Za-z0-9_.]*Conformance\b", lake_text
        ):
            errors.append(
                f"{name} declares correspondence_only but a Lake target names an owned "
                "conformance module"
            )

        bench_dir = root / "bench" / name
        bench_files = sorted(bench_dir.rglob("*.lean")) if bench_dir.is_dir() else []
        if bench_files:
            errors.append(
                f"{name} declares correspondence_only but owns bench source "
                f"{bench_files[0].relative_to(root)}"
            )
        normalized_name = re.sub(r"[^a-z0-9]", "", name.lower())
        for exe_name in sorted(exe_names):
            normalized_exe = re.sub(r"[^a-z0-9]", "", exe_name.lower())
            if "bench" in normalized_exe and normalized_name in normalized_exe:
                errors.append(
                    f"{name} declares correspondence_only but owns compiled benchmark "
                    f"target {exe_name}"
                )
                break
        if re.search(rf"`{re.escape(name)}\.Bench(?:\b|\.)", lake_text):
            errors.append(
                f"{name} declares correspondence_only but a Lake target names "
                f"{name}.Bench"
            )

        for module in sorted(
            module for module in build_modules if module.startswith(f"{name}.")
        ):
            module_path = root / Path(*module.split(".")).with_suffix(".lean")
            if not module_path.is_file():
                continue
            for line_no, line in enumerate(
                module_path.read_text(encoding="utf-8").splitlines(), start=1
            ):
                if RUNTIME_CHECK_RE.match(line):
                    errors.append(
                        f"{name} declares correspondence_only but build-only module "
                        f"{module} contains a runtime check at "
                        f"{module_path.relative_to(root)}:{line_no}"
                    )
                    break

        spec_dir = root / name / "SPEC"
        specs = sorted(spec_dir.glob("*.md")) if spec_dir.is_dir() else []
        if len(specs) != 1:
            errors.append(
                f"{name} declares correspondence_only but has {len(specs)} library SPECs; "
                "expected exactly one"
            )
            continue
        spec = specs[0]
        text = spec.read_text(encoding="utf-8")
        if "correspondence-only-layer" not in text:
            errors.append(
                f"{name} declares correspondence_only but {spec.relative_to(root)} does "
                "not declare correspondence-only-layer"
            )
        owners: dict[str, list[str]] = {}
        for kind, body in OWNER_RE.findall(text):
            owners.setdefault(kind, []).extend(OWNER_NAME_RE.findall(body))
        for kind in ("conformance", "performance"):
            names = owners.get(kind, [])
            if not names:
                errors.append(
                    f"{name} declares correspondence_only but {spec.relative_to(root)} "
                    f"does not identify computational {kind} owners"
                )
                continue
            for owner in names:
                if owner not in libraries:
                    errors.append(
                        f"{name} names unknown computational {kind} owner {owner}"
                    )
                    continue
                if libraries[owner].mathlib:
                    errors.append(
                        f"{name} names mathlib bridge {owner} as a computational "
                        f"{kind} owner"
                    )
                    continue
                if not may_import(name, owner, libraries, reachable):
                    errors.append(
                        f"{name} names computational {kind} owner {owner} outside its "
                        "dependency closure"
                    )
                if kind == "conformance":
                    owner_conformance = (
                        root / "conformance" / owner / "Conformance.lean"
                    )
                    if not owner_conformance.is_file():
                        errors.append(
                            f"{name} names computational conformance owner {owner} "
                            "without a core conformance module"
                        )
                # Phase 3 requires the owner declaration, while the owner's
                # headline report becomes evidence only at the bridge's
                # Phase-4 exit.
                elif info.done_through >= 4:
                    owner_slug = Path(pascal_to_spec_path(owner)).stem
                    owner_report = root / "reports" / f"{owner_slug}-performance.md"
                    if not owner_report.is_file():
                        errors.append(
                            f"{name} names computational performance owner {owner} "
                            "without a headline report"
                        )
    return errors


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

    lakefile = root / "lakefile.lean"
    errors.extend(check_correspondence_only(root, libraries, lakefile))
    build_roots = lean_exe_roots(lakefile) | lean_glob_modules(
        lakefile, UMBRELLA_BUILD_TARGETS
    )
    errors.extend(check_umbrella_completeness(root, libraries, build_roots))

    lean_files = project_lean_files(root)
    errors.extend(check_sealed_import_all(root, lean_files))

    for rel_path in lean_files:
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
