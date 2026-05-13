#!/usr/bin/env python3
"""Structural lint for SPEC/benchmarking.md §Mathlib-free benches.

Two invariants enforced:

  1. No `Hex*Mathlib/Bench.lean`, `Hex*Mathlib/Bench/`, or
     `lean_exe *mathlib*_bench` exists.  `Hex*Mathlib` libraries are
     proof-only bridges; they have no computational kernel to
     benchmark.

  2. No bench-exe root module (any module named by `lean_exe
     *_bench where root := `Module.Name`` in `lakefile.lean`), and
     no module transitively reachable from such a root via Lean
     `import`, may name a `Mathlib.*` module.

On any violation, exits 1 and prints (a) the offending root or
file plus (b) for the import-graph case, the full import chain to
the first `Mathlib.*` hit.

Used as a CI step from `.github/workflows/ci.yml`'s `build` job.
Stdlib only; runs from the repository root regardless of cwd.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path


# Module name -> file path: `A.B.C` ↔ `A/B/C.lean` relative to repo root.
def _module_to_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


# Bench-exe root lines look like:
#   lean_exe hexarith_bench where
#     root := `HexArith.Bench
#
# The `root := \`Module.Name` may live on the same line or the line
# below; we treat the file as a stream and pair them up.
_LEAN_EXE_RE = re.compile(r"^lean_exe\s+(\S+_bench)\s+where\b")
_ROOT_RE = re.compile(r"root\s*:=\s*`([A-Za-z][A-Za-z0-9_.]*)")


def _parse_bench_roots(lakefile: Path) -> dict[str, str]:
    """Return {exe_name: root_module} from lakefile.lean."""
    out: dict[str, str] = {}
    text = lakefile.read_text()
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m_exe = _LEAN_EXE_RE.match(lines[i])
        if m_exe:
            exe = m_exe.group(1)
            # Look on the same line and up to the next 5 lines for `root := \`...`.
            for j in range(i, min(i + 6, len(lines))):
                m_root = _ROOT_RE.search(lines[j])
                if m_root:
                    out[exe] = m_root.group(1)
                    break
            else:
                print(f"lakefile.lean: lean_exe {exe} has no root := ...",
                      file=sys.stderr)
                sys.exit(2)
        i += 1
    return out


# Lean syntax: `import` lines appear at file start, before any other
# top-level decl.  We scan until the first non-blank, non-comment,
# non-import line.
_IMPORT_RE = re.compile(r"^import\s+([A-Za-z][A-Za-z0-9_.]*)")
_LINE_COMMENT_RE = re.compile(r"^\s*--")
_BLOCK_COMMENT_START = re.compile(r"^\s*/-")
_BLOCK_COMMENT_END = re.compile(r"-/\s*$")


def _parse_imports(path: Path) -> list[str]:
    """Return the list of module names this Lean file imports."""
    imports: list[str] = []
    in_block_comment = False
    try:
        for raw in path.read_text().splitlines():
            line = raw.rstrip()
            if in_block_comment:
                if _BLOCK_COMMENT_END.search(line):
                    in_block_comment = False
                continue
            if _BLOCK_COMMENT_START.match(line):
                # A `/- … -/` block at the top is allowed (module docstring).
                if not _BLOCK_COMMENT_END.search(line):
                    in_block_comment = True
                continue
            if _LINE_COMMENT_RE.match(line) or not line.strip():
                continue
            m = _IMPORT_RE.match(line)
            if m:
                imports.append(m.group(1))
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


def _walk_for_mathlib(root_module: str, repo_root: Path
                      ) -> list[str] | None:
    """BFS over the import graph rooted at `root_module`.  Return the
    import chain (list of module names) to the first `Mathlib.*` hit,
    or None if no Mathlib in the closure."""
    visited: set[str] = set()
    # Each frontier entry is the chain that led to this module.
    frontier: list[list[str]] = [[root_module]]
    while frontier:
        chain = frontier.pop(0)
        module = chain[-1]
        if module in visited:
            continue
        visited.add(module)
        if _is_mathlib(module):
            return chain
        path = repo_root / _module_to_path(module)
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


def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]
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
    bench_roots = _parse_bench_roots(lakefile)
    for exe in sorted(bench_roots):
        if "mathlib" in exe.lower():
            failures.append(
                f"  FORBIDDEN: lakefile.lean declares `lean_exe {exe}` — "
                f"bench exes for Hex*Mathlib libraries are not allowed.\n"
                f"  See SPEC/benchmarking.md §Mathlib-free benches."
            )

    # Invariant 2: no bench-exe root reaches `Mathlib.*` via imports.
    for exe, root in sorted(bench_roots.items()):
        chain = _walk_for_mathlib(root, repo_root)
        if chain is not None:
            chain_str = "\n    → ".join(chain)
            failures.append(
                f"  FORBIDDEN: bench exe `{exe}` (root `{root}`) reaches "
                f"Mathlib via:\n    {chain_str}\n"
                f"  See SPEC/benchmarking.md §Mathlib-free benches."
            )

    if failures:
        print("Mathlib-free benches lint failed:", file=sys.stderr)
        for f in failures:
            print(f, file=sys.stderr)
        print(
            "\nFix: delete the offending bench file(s) (Hex*Mathlib "
            "libraries are proof-only and have no computational kernel "
            "to benchmark), or remove the Mathlib import from the "
            "bench's transitive import graph.",
            file=sys.stderr,
        )
        return 1

    print(f"check_benches_mathlib_free: OK "
          f"({len(bench_roots)} bench exe(s) checked, "
          f"none import Mathlib).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
