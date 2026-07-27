#!/usr/bin/env python3
"""Structural lint for SPEC/benchmarking.md §Mathlib-free benches.

The computational-benchmark invariants are:

  1. No `Hex*Mathlib/Bench.lean`, `Hex*Mathlib/Bench/`, or
     `lean_exe *mathlib*_bench` exists.  `Hex*Mathlib` libraries are
     proof-only bridges; they have no computational kernel to
     benchmark.

  2. No bench-exe root module (any module named by `lean_exe
     *_bench where root := `Module.Name`` in `lakefile.lean`), and
     no module transitively reachable from such a root via Lean
     `import`, may name a `Mathlib.*` module. Non-executable bench sources
     outside an explicit proof-probe root are checked too, so an undeclared
     helper cannot silently import Mathlib.

A narrow exception permits build-only proof-elaboration probes below explicit
`proof_probes` paths owned by `mathlib: true` libraries in `libraries.yml`.
Such files may import Mathlib, but may not import
LeanBench, register a benchmark, define `main`, time work in-process, or
serve as a `lean_exe` root.

On any violation, exits 1 and prints (a) the offending root or
file plus (b) for the import-graph case, the full import chain to
the first `Mathlib.*` hit.

Used as a CI step from `.github/workflows/ci.yml`'s `build` job.
Stdlib only; runs from the repository root regardless of cwd.
"""
from __future__ import annotations

import functools
import os
import re
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))
from scripts.libgraph import _strip_comment as _strip_manifest_comment  # noqa: E402
from scripts.libgraph import load_libraries  # noqa: E402


# Module name -> file path: `A.B.C` ↔ `A/B/C.lean` relative to repo root.
def _module_to_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


# Bench-exe declarations look like:
#   lean_exe hexarith_bench where
#     srcDir := "bench"
#     root := `HexArith.Bench
#
# Fields may live on the declaration line or indented lines below it.
_ATTR_PREFIX = r"(?:(?:@\[[^]]+\])\s*)*"
_LEAN_EXE_RE = re.compile(
    rf"^\s*{_ATTR_PREFIX}lean_exe\s+(\S+)\s+where\b"
)
_LEAN_EXE_START_RE = re.compile(rf"^\s*{_ATTR_PREFIX}lean_exe\b")
_LEAN_LIB_RE = re.compile(
    rf"^\s*{_ATTR_PREFIX}lean_lib\s+(\S+)\s+where\b"
)
_ROOT_RE = re.compile(r"root\s*:=\s*`([A-Za-z][A-Za-z0-9_.]*)")
_SRC_DIR_RE = re.compile(r'srcDir\s*:=\s*"([^"]+)"')
_SRC_DIR_FIELD_RE = re.compile(r"\bsrcDir\s*:=")


@dataclass(frozen=True)
class _ExeTarget:
    name: str
    root: str
    src_dir: Path

    def root_path(self, repo_root: Path) -> Path:
        return repo_root / self.src_dir / _module_to_path(self.root)


def _normalize_identifier(identifier: str) -> str:
    """Normalize a Lake/Lean escaped identifier for policy classification."""
    if identifier.startswith("«") and identifier.endswith("»"):
        return identifier[1:-1]
    return identifier


def _parse_exe_targets(lakefile: Path) -> dict[str, _ExeTarget]:
    """Return executable root modules and effective source directories."""
    out: dict[str, _ExeTarget] = {}
    text = _without_comments(lakefile.read_text())
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m_exe = _LEAN_EXE_RE.match(lines[i])
        if m_exe:
            exe = _normalize_identifier(m_exe.group(1))
            base_indent = len(lines[i]) - len(lines[i].lstrip())
            block = [lines[i]]
            j = i + 1
            while j < len(lines):
                line = lines[j]
                indent = len(line) - len(line.lstrip())
                if line.strip() and indent <= base_indent:
                    break
                block.append(line)
                j += 1
            block_text = "\n".join(block)
            m_root = _ROOT_RE.search(block_text)
            if m_root is None:
                raise ValueError(
                    f"lakefile.lean: lean_exe {exe} has no literal root := `..."
                )
            m_src = _SRC_DIR_RE.search(block_text)
            if _SRC_DIR_FIELD_RE.search(block_text) and m_src is None:
                raise ValueError(
                    f"lakefile.lean: lean_exe {exe} has an unsupported "
                    "nonliteral srcDir; the lint cannot resolve its root safely"
                )
            src_dir = Path(m_src.group(1)) if m_src else Path()
            out[exe] = _ExeTarget(exe, m_root.group(1), src_dir)
            i = j
            continue
        if _LEAN_EXE_START_RE.match(lines[i]):
            raise ValueError(
                f"lakefile.lean: unsupported lean_exe declaration: {lines[i].strip()}"
            )
        i += 1
    return out


# Current module-system syntax permits a `module` header before the leading
# import block and visibility/meta modifiers on each import.
_IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$"
)
_MODULE_RE = re.compile(r"^\s*module(?:\s+[A-Za-z][A-Za-z0-9_.]*)?\s*$")
_PRELUDE_RE = re.compile(r"^\s*prelude\s*$")
_MODULE_NAME_RE = re.compile(r"[A-Za-z][A-Za-z0-9_.]*")


def _without_comments(text: str) -> str:
    """Remove nested block and line comments while preserving newlines."""
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            newline = text.find("\n", i)
            if newline < 0:
                break
            out.append("\n")
            i = newline + 1
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


@functools.cache
def _parse_imports(path: Path) -> list[str]:
    """Return the list of module names this Lean file imports."""
    imports: list[str] = []
    try:
        lines = _without_comments(path.read_text()).splitlines()
        saw_module = False
        saw_prelude = False
        for line in lines:
            if not line.strip():
                continue
            if not saw_module and not saw_prelude and _MODULE_RE.match(line):
                saw_module = True
                continue
            if not saw_prelude and _PRELUDE_RE.match(line):
                saw_prelude = True
                continue
            m = _IMPORT_RE.match(line)
            if m:
                names = [
                    name for name in _MODULE_NAME_RE.findall(m.group(1))
                    if name != "all"
                ]
                imports.extend(names)
                continue
            # First non-import non-comment line → done.
            break
    except FileNotFoundError:
        # External (non-workspace) module; treat as a leaf.  Caller
        # classifies it by prefix.
        return []
    return imports


def _is_mathlib(module: str) -> bool:
    """True iff `module` is in the upstream Mathlib namespace.

    Intra-project `Hex*Mathlib.*` modules are NOT in the Mathlib
    namespace — they're bridge libraries.  Only `Mathlib.*` is forbidden.
    """
    return module == "Mathlib" or module.startswith("Mathlib.")


def _lean_lib_source_dirs(lakefile: Path) -> list[Path]:
    """Read literal `srcDir` fields from Lean-syntax library declarations."""
    lines = _without_comments(lakefile.read_text()).splitlines()
    roots: list[Path] = []
    i = 0
    while i < len(lines):
        match = _LEAN_LIB_RE.match(lines[i])
        if match is None:
            i += 1
            continue
        lib = _normalize_identifier(match.group(1))
        base_indent = len(lines[i]) - len(lines[i].lstrip())
        block = [lines[i]]
        j = i + 1
        while j < len(lines):
            line = lines[j]
            indent = len(line) - len(line.lstrip())
            if line.strip() and indent <= base_indent:
                break
            block.append(line)
            j += 1
        block_text = "\n".join(block)
        src_match = _SRC_DIR_RE.search(block_text)
        if _SRC_DIR_FIELD_RE.search(block_text) and src_match is None:
            raise ValueError(
                f"{lakefile}: lean_lib {lib} has an unsupported nonliteral srcDir"
            )
        roots.append(Path(src_match.group(1)) if src_match else Path())
        i = j
    return roots


@functools.cache
def _configured_source_roots(repo_root: Path) -> tuple[Path, ...]:
    """Repository and dependency library roots used by Lake module lookup."""
    roots: list[Path] = [repo_root]
    packages = repo_root / ".lake" / "packages"
    if packages.is_dir():
        for package in sorted(path for path in packages.iterdir() if path.is_dir()):
            roots.append(package)
            leanfile = package / "lakefile.lean"
            tomlfile = package / "lakefile.toml"
            if leanfile.is_file():
                roots.extend(package / src for src in _lean_lib_source_dirs(leanfile))
            elif tomlfile.is_file():
                data = tomllib.loads(tomlfile.read_text())
                for lib in data.get("lean_lib", []):
                    src = lib.get("srcDir", ".")
                    if not isinstance(src, str):
                        raise ValueError(
                            f"{tomlfile}: lean_lib has a non-string srcDir"
                        )
                    roots.append(package / src)
    return tuple(dict.fromkeys(roots))


def _resolve_module(module: str, target: _ExeTarget,
                    repo_root: Path) -> Path | None:
    """Resolve a module through the target source root, repo, then packages."""
    rel = _module_to_path(module)
    roots = [repo_root / target.src_dir, *_configured_source_roots(repo_root)]
    seen: set[Path] = set()
    for root in roots:
        if root in seen:
            continue
        seen.add(root)
        candidate = root / rel
        if candidate.is_file():
            return candidate
    return None


def _walk_for_mathlib(target: _ExeTarget, repo_root: Path
                      ) -> list[str] | None:
    """BFS over the import graph rooted at `target`.  Return the
    import chain (list of module names) to the first `Mathlib.*` hit,
    or None if no Mathlib in the closure."""
    visited: set[str] = set()
    # Each frontier entry is the chain that led to this module.
    frontier: list[list[str]] = [[target.root]]
    while frontier:
        chain = frontier.pop(0)
        module = chain[-1]
        if module in visited:
            continue
        visited.add(module)
        if _is_mathlib(module):
            return chain
        path = _resolve_module(module, target, repo_root)
        if path is None:
            continue
        for imp in _parse_imports(path):
            if imp not in visited:
                frontier.append(chain + [imp])
    return None


# Detect the file/dir-glob violations: `Hex*Mathlib/Bench.lean` etc.
def _find_mathlib_bridge_bench_paths(repo_root: Path) -> list[Path]:
    out: list[Path] = []
    for entry in sorted(repo_root.iterdir()):
        if not entry.is_dir():
            continue
        name = entry.name
        if not (name.startswith("Hex") and name.endswith("Mathlib")):
            continue
        # File: Hex*Mathlib/Bench.lean
        bench = entry / "Bench.lean"
        if bench.is_file():
            out.append(bench)
        # Dir: Hex*Mathlib/Bench/
        bench_dir = entry / "Bench"
        if bench_dir.is_dir():
            out.append(bench_dir)
    return out


_MANIFEST_LIBRARY_RE = re.compile(r"^ {2}(\S(?:.*\S)?):\s*$")
_MANIFEST_FIELD_RE = re.compile(r"^ {4}(\S[^:]*):")


def _check_manifest_uniqueness(path: Path) -> None:
    """Reject duplicate library entries or fields before YAML-like parsing."""
    seen_libraries: set[str] = set()
    seen_fields: set[str] = set()
    current: str | None = None
    libraries_headers = 0
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = _strip_manifest_comment(raw).rstrip()
        if line == "libraries:":
            libraries_headers += 1
            current = None
            continue
        library = _MANIFEST_LIBRARY_RE.match(line)
        if library:
            current = library.group(1)
            if current in seen_libraries:
                raise ValueError(f"{path}: duplicate library entry {current}")
            seen_libraries.add(current)
            seen_fields = set()
            continue
        field = _MANIFEST_FIELD_RE.match(line)
        if current is not None and field:
            name = field.group(1).strip()
            if name in seen_fields:
                raise ValueError(f"{path}: duplicate {current}.{name} field")
            seen_fields.add(name)
    if libraries_headers != 1:
        raise ValueError(
            f"{path}: expected exactly one libraries: header, got {libraries_headers}"
        )


def _mathlib_probe_roots(repo_root: Path) -> tuple[Path, ...]:
    """Return explicit manifest-owned roots admitted to the probe carveout."""
    manifest = repo_root / "libraries.yml"
    _check_manifest_uniqueness(manifest)
    libraries = load_libraries(manifest)
    entries = tuple(
        (info, repo_root / probe)
        for info in libraries.values()
        for probe in info.proof_probes
    )
    roots = tuple(root for _, root in entries)
    physical_bench = (repo_root / "bench").resolve()
    for owner, root in entries:
        if root.is_symlink() and not root.exists():
            raise ValueError(f"broken proof probe root symlink: {root}")
        if not root.exists():
            # A manifest entry may reserve a path for a probe delivered by a
            # later stacked change. Undeclared Mathlib-reaching files are still
            # caught by the all-bench-source scan.
            if owner.done_through >= 4:
                raise ValueError(
                    f"Phase-4 library {owner.name} has missing proof probe "
                    f"root: {root}"
                )
            continue
        if not root.is_dir():
            raise ValueError(f"proof probe root is not a directory: {root}")
        try:
            root.resolve().relative_to(physical_bench)
        except ValueError as exc:
            raise ValueError(
                f"proof probe root resolves outside bench/: {root}"
            ) from exc
        # Path.rglob deliberately does not descend through directory
        # symlinks.  Reject every descendant symlink rather than letting a
        # Lake glob build source that neither the probe scan nor the ordinary
        # all-bench scan can see.
        for directory, dirnames, filenames in os.walk(root, followlinks=False):
            for name in (*dirnames, *filenames):
                descendant = Path(directory) / name
                if descendant.is_symlink():
                    raise ValueError(
                        f"proof probe root contains symlink: {descendant}"
                    )
        if owner.done_through >= 4 and not any(root.rglob("*.lean")):
            raise ValueError(
                f"Phase-4 library {owner.name} has empty proof probe root: "
                f"{root}"
            )
    return roots


def _is_mathlib_probe_path(path: Path, repo_root: Path,
                           roots: tuple[Path, ...]) -> bool:
    """Whether `path` lies below an explicit manifest-owned probe root."""
    def is_below(candidate: Path, root: Path) -> bool:
        try:
            candidate.relative_to(root)
        except ValueError:
            return False
        return True

    # Lexical normalization keeps a configured probe-root symlink pointing
    # outward covered; physical normalization catches a source-root alias
    # pointing inward.
    lexical = Path(os.path.abspath(path))
    physical = path.resolve()
    return any(
        is_below(lexical, Path(os.path.abspath(root)))
        or is_below(physical, root.resolve())
        for root in roots
    )


def _find_mathlib_probe_files(repo_root: Path,
                              roots: tuple[Path, ...]) -> list[Path]:
    """Find Lean proof probes below explicit manifest-owned roots."""
    out: set[Path] = set()
    for root in roots:
        if root.is_dir():
            out.update(root.rglob("*.lean"))
    return sorted(out)


def _undeclared_mathlib_bench_failures(
    repo_root: Path, roots: tuple[Path, ...]
) -> list[str]:
    """Reject Mathlib-reaching bench sources outside explicit probe roots."""
    bench_root = repo_root / "bench"
    if not bench_root.is_dir():
        return []
    failures: list[str] = []
    for source in sorted(bench_root.rglob("*.lean")):
        if _is_mathlib_probe_path(source, repo_root, roots):
            continue
        relative = source.relative_to(bench_root)
        module = ".".join(relative.with_suffix("").parts)
        target = _ExeTarget(
            name=f"bench source {relative}", root=module, src_dir=Path("bench")
        )
        chain = _walk_for_mathlib(target, repo_root)
        if chain is not None:
            chain_str = "\n    → ".join(chain)
            failures.append(
                f"  FORBIDDEN: undeclared bench source `{relative}` reaches "
                f"Mathlib via:\n    {chain_str}\n"
                f"  Declare an exact proof_probes path owned by a mathlib: "
                f"true library, or keep the source Mathlib-free."
            )
    return failures


_PROBE_FORBIDDEN = (
    (
        "imports LeanBench",
        re.compile(
            r"^\s*(?:(?:public|private|meta)\s+)*import\s+"
            r"(?:all\s+)?LeanBench(?:\.|\s|$)",
            re.MULTILINE,
        ),
    ),
    (
        "registers a LeanBench benchmark",
        re.compile(
            rf"^\s*{_ATTR_PREFIX}(?:(?:public|private|meta)\s+)*"
            r"setup_(?:fixed_)?benchmark\b",
            re.MULTILINE,
        ),
    ),
    (
        "defines main",
        re.compile(
            rf"^\s*{_ATTR_PREFIX}"
            r"(?:(?:public|private|protected|noncomputable|partial|unsafe|meta)\s+)*"
            r"(?:def|opaque|abbrev)\s+"
            r"(?:main(?![\w'.!?])|«main»(?![\w'.!?])|"
            r"_root_\.(?:main(?![\w'.!?])|«main»(?![\w'.!?])))",
            re.MULTILINE,
        ),
    ),
    (
        "uses an in-process monotonic clock",
        re.compile(
            r"(?<![\w.])(?:_root_\.)?(?:IO\.)?"
            r"(?:mono(?:Nanos|Ms)Now|«mono(?:Nanos|Ms)Now»)(?![\w'.])"
        ),
    ),
)


def _probe_violations(path: Path) -> list[str]:
    """Return forbidden computational-benchmark features used by one probe."""
    text = _without_comments(path.read_text())
    return [description for description, pattern in _PROBE_FORBIDDEN
            if pattern.search(text)]


def _probe_closure_violations(
    probe: Path, repo_root: Path
) -> list[tuple[Path, str]]:
    """Return forbidden features in a probe's repository-local closure.

    Mathlib and other Lake packages are leaves for this policy: their source
    may legitimately define executables or use internal clocks.  Every source
    resolved below the repository itself (apart from `.lake/packages`) is
    scanned and traversed, so moving LeanBench registration or timing into a
    helper does not evade the build-only probe contract.
    """
    bench_root = repo_root / "bench"
    relative = probe.relative_to(bench_root)
    target = _ExeTarget(
        name=f"proof probe {relative}",
        root=".".join(relative.with_suffix("").parts),
        src_dir=Path("bench"),
    )
    repo_abs = Path(os.path.abspath(repo_root))
    packages_abs = repo_abs / ".lake" / "packages"
    visited: set[str] = set()
    frontier = [target.root]
    failures: list[tuple[Path, str]] = []
    while frontier:
        module = frontier.pop(0)
        if module in visited:
            continue
        visited.add(module)
        path = _resolve_module(module, target, repo_root)
        if path is None:
            continue
        lexical = Path(os.path.abspath(path))
        try:
            lexical.relative_to(repo_abs)
        except ValueError:
            continue
        try:
            lexical.relative_to(packages_abs)
        except ValueError:
            pass
        else:
            continue
        for violation in _probe_violations(path):
            failures.append((path, violation))
        for imported in _parse_imports(path):
            if imported not in visited:
                frontier.append(imported)
    return failures


def _probe_root_path(target: _ExeTarget, repo_root: Path,
                     roots: tuple[Path, ...]) -> Path | None:
    """Resolve a module when its source is an admitted Mathlib probe file."""
    candidate = target.root_path(repo_root)
    if candidate.is_file() and _is_mathlib_probe_path(
        candidate, repo_root, roots
    ):
        return candidate
    return None


def _missing_exe_root_failures(
    targets: dict[str, _ExeTarget], repo_root: Path
) -> list[str]:
    """Report declared executable roots that do not exist under `srcDir`."""
    failures: list[str] = []
    for target in targets.values():
        path = target.root_path(repo_root)
        if not path.is_file():
            failures.append(
                f"  INVALID: executable `{target.name}` root `{target.root}` "
                f"does not exist at `{path.relative_to(repo_root)}` "
                f"(srcDir `{target.src_dir or Path('.')}`)."
            )
    return failures


def main() -> int:
    repo_root = REPO_ROOT
    lakefile = repo_root / "lakefile.lean"
    if not lakefile.is_file():
        print(f"FATAL: lakefile.lean not found at {lakefile}",
              file=sys.stderr)
        return 2

    failures: list[str] = []

    # Invariant 1a: no `Hex*Mathlib/Bench.lean` or `Hex*Mathlib/Bench/`.
    for offender in _find_mathlib_bridge_bench_paths(repo_root):
        rel = offender.relative_to(repo_root)
        failures.append(
            f"  FORBIDDEN: {rel} — Hex*Mathlib libraries are "
            f"proof-only bridges; no benches allowed.\n"
            f"  See SPEC/benchmarking.md §Mathlib-free benches."
        )

    # Invariant 1b: no `lean_exe *mathlib*_bench` in lakefile.
    try:
        exe_targets = _parse_exe_targets(lakefile)
        _configured_source_roots(repo_root)
        probe_roots = _mathlib_probe_roots(repo_root)
    except (OSError, ValueError, tomllib.TOMLDecodeError) as exc:
        print(f"FATAL: cannot resolve Lake module roots: {exc}", file=sys.stderr)
        return 2
    failures.extend(_missing_exe_root_failures(exe_targets, repo_root))
    bench_targets = {
        exe: target for exe, target in exe_targets.items()
        if exe.endswith("_bench")
    }
    for exe in sorted(bench_targets):
        if "mathlib" in exe.lower():
            failures.append(
                f"  FORBIDDEN: lakefile.lean declares `lean_exe {exe}` — "
                f"bench exes for Hex*Mathlib libraries are not allowed.\n"
                f"  See SPEC/benchmarking.md §Mathlib-free benches."
            )

    # The build-only proof-probe carveout is intentionally not an executable
    # or a second computational benchmark harness.
    probe_files = _find_mathlib_probe_files(repo_root, probe_roots)
    for probe in probe_files:
        for source, violation in _probe_closure_violations(probe, repo_root):
            failures.append(
                f"  FORBIDDEN: proof probe {probe.relative_to(repo_root)} "
                f"reaches {source.relative_to(repo_root)}, which {violation}.\n"
                f"  Mathlib proof probes must be build-only and externally "
                f"timed; see SPEC/benchmarking.md §Mathlib-free benches."
            )
    for exe, target in sorted(exe_targets.items()):
        probe = _probe_root_path(target, repo_root, probe_roots)
        if probe is not None:
            failures.append(
                f"  FORBIDDEN: executable `{exe}` is rooted at Mathlib proof "
                f"probe `{probe.relative_to(repo_root)}`.\n"
                f"  Proof probes must remain build-only; see "
                f"SPEC/benchmarking.md §Mathlib-free benches."
            )

    # Files outside an explicit proof-probe root receive no exception merely
    # because their directory resembles a Mathlib library name. Scan every
    # bench source, including non-executable helpers, through its import graph.
    failures.extend(_undeclared_mathlib_bench_failures(repo_root, probe_roots))

    # Invariant 2: no bench-exe root reaches `Mathlib.*` via imports.
    for exe, target in sorted(bench_targets.items()):
        if not target.root_path(repo_root).is_file():
            continue
        chain = _walk_for_mathlib(target, repo_root)
        if chain is not None:
            chain_str = "\n    → ".join(chain)
            failures.append(
                f"  FORBIDDEN: bench exe `{exe}` (root `{target.root}`) reaches "
                f"Mathlib via:\n    {chain_str}\n"
                f"  See SPEC/benchmarking.md §Mathlib-free benches."
            )

    if failures:
        print("Mathlib-free benches lint failed:", file=sys.stderr)
        for f in failures:
            print(f, file=sys.stderr)
        print(
            "\nFix: keep executable computational benches Mathlib-free. "
            "A Mathlib proof-elaboration probe may instead be a build-only "
            "module under an explicit libraries.yml proof_probes path owned by "
            "a mathlib: true library, with timing performed by an external "
            "harness.",
            file=sys.stderr,
        )
        return 1

    print(f"check_benches_mathlib_free: OK "
          f"({len(bench_targets)} bench exe(s) checked, "
          f"{len(probe_files)} build-only Mathlib proof probe(s) checked).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
