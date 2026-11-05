#!/usr/bin/env python3
"""Remove unused hosted tool caches without removing active build runtimes."""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys

TOOLS = ("python", "python3", "node", "npm", "cmake", "ninja", "make", "cc", "c++",
         "gcc", "g++", "clang", "clang++", "git", "curl", "tar", "gzip")


def active_paths() -> set[Path]:
    paths = {Path(sys.executable).resolve()}
    for name in TOOLS:
        executable = shutil.which(name)
        if executable:
            paths.add(Path(executable).resolve())
    return paths


def unused_paths(cache: Path, active: set[Path]) -> list[Path]:
    if not cache.is_dir():
        return []
    active = {path.resolve() for path in active}
    return [path for path in sorted(cache.iterdir())
            if not any(item.is_relative_to(path.resolve()) for item in active)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    if args.apply and os.environ.get("GITHUB_ACTIONS") != "true":
        parser.error("--apply requires the GitHub Actions runner environment")
    cache = Path("/opt/hostedtoolcache")
    active = active_paths()
    for path in sorted(active):
        print(f"Retain active runtime: {path}", flush=True)
    for path in unused_paths(cache, active):
        print(f"Reclaim unused hosted cache: {path}", flush=True)
        if args.apply:
            subprocess.run(["sudo", "rm", "-rf", "--", str(path)], check=True)


if __name__ == "__main__":
    main()
