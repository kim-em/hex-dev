#!/usr/bin/env python3
"""Enforce per-file line-count limits on tracked Lean sources.

Two rules (see `SPEC/CI.md` § Source-file lints):

* **Absolute cap.** No tracked `.lean` file (except `lakefile.lean`) may
  exceed 3000 lines. Oversized files are hard to review and slow to
  elaborate; split them into dependency-ordered submodules.
* **New-file budget.** A change may not *add* a new `.lean` file that is
  already over 2000 lines. Existing files between 2000 and 3000 lines are
  grandfathered, but new files must start well under the absolute cap.

The absolute cap always runs. The new-file budget runs only when a git
merge base is available (i.e. in pull-request / branch context); on a
plain checkout of `main` with no base it is skipped.

`--base REF` overrides the merge-base detection; `--max-lines` and
`--new-file-max` override the two thresholds.
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

EXCLUDED = {"lakefile.lean"}
MAX_LINES = 3000
NEW_FILE_MAX = 2000


def run_git(args: list[str], root: Path, *, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if check and result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def tracked_lean_files(root: Path) -> list[str]:
    out = run_git(["ls-files", "*.lean"], root)
    return [p for p in out.splitlines() if p and Path(p).name not in EXCLUDED]


def line_count(root: Path, rel: str) -> int:
    return len((root / rel).read_text(encoding="utf-8").splitlines())


def default_base(root: Path) -> str | None:
    candidates: list[str] = []
    github_base = os.environ.get("GITHUB_BASE_REF")
    if github_base:
        candidates.extend([f"origin/{github_base}", github_base])
    candidates.extend(["origin/main", "origin/master", "main", "master"])
    for candidate in candidates:
        if subprocess.run(["git", "rev-parse", "--verify", candidate], cwd=root,
                          stdout=subprocess.DEVNULL,
                          stderr=subprocess.DEVNULL).returncode == 0:
            merge_base = run_git(["merge-base", candidate, "HEAD"], root,
                                 check=False).strip()
            if merge_base:
                return merge_base
    return None


def added_lean_files(root: Path, base: str) -> list[str]:
    out = run_git(
        ["diff", "--name-status", "--diff-filter=A", "--no-ext-diff",
         f"{base}...HEAD", "--", "*.lean"],
        root, check=False,
    )
    added: list[str] = []
    for line in out.splitlines():
        parts = line.split("\t")
        if len(parts) >= 2 and Path(parts[1]).name not in EXCLUDED:
            added.append(parts[1])
    return added


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", help="base revision for the new-file budget")
    parser.add_argument("--max-lines", type=int, default=MAX_LINES,
                        help=f"absolute cap for every tracked .lean file (default {MAX_LINES})")
    parser.add_argument("--new-file-max", type=int, default=NEW_FILE_MAX,
                        help=f"cap for newly-added .lean files (default {NEW_FILE_MAX})")
    args = parser.parse_args()

    root = Path(run_git(["rev-parse", "--show-toplevel"], Path.cwd()).strip())
    errors: list[str] = []

    # Rule 1: absolute cap over every tracked file.
    for rel in tracked_lean_files(root):
        n = line_count(root, rel)
        if n > args.max_lines:
            errors.append(f"{rel}: {n} lines exceeds the {args.max_lines}-line cap")

    # Rule 2: new-file budget, diff against the merge base when available.
    base = args.base or default_base(root)
    if base is None:
        print("check_file_line_counts: no merge base; skipping new-file budget",
              file=sys.stderr)
    else:
        for rel in added_lean_files(root, base):
            if Path(root / rel).exists():
                n = line_count(root, rel)
                if n > args.new_file_max:
                    errors.append(
                        f"{rel}: new file with {n} lines exceeds the "
                        f"{args.new_file_max}-line new-file budget")

    if errors:
        print("Lean file line-count limits exceeded:", file=sys.stderr)
        for e in errors:
            print(f"  {e}", file=sys.stderr)
        print("\nSplit oversized files into dependency-ordered submodules; see "
              "SPEC/CI.md § Source-file lints.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
