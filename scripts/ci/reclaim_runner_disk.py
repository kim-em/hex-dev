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
    paths = {Path(sys.executable).absolute(), Path(sys.executable).resolve()}
    for name in TOOLS:
        executable = shutil.which(name)
        if executable:
            paths.update((Path(executable).absolute(), Path(executable).resolve()))
    return paths


def unused_paths(cache: Path, active: set[Path]) -> list[Path]:
    if not cache.is_dir():
        return []
    active = {variant for path in active for variant in (path.absolute(), path.resolve())}
    return [path for path in sorted(cache.iterdir())
            if not any(item.is_relative_to(prefix) for item in active
                       for prefix in (path.absolute(), path.resolve()))]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    if args.apply and not (os.environ.get("GITHUB_ACTIONS") == "true" and
                           os.environ.get("RUNNER_ENVIRONMENT") == "github-hosted" and
                           os.environ.get("RUNNER_OS") == "Linux"):
        parser.error("--apply requires a GitHub-hosted Linux runner")
    cache = Path(os.environ.get("RUNNER_TOOL_CACHE", "/opt/hostedtoolcache"))
    if not cache.is_absolute() or cache == Path("/"):
        parser.error("RUNNER_TOOL_CACHE must name an absolute tool-cache directory")
    active = active_paths()
    for path in sorted(active):
        print(f"Retain active runtime: {path}", flush=True)
    for path in unused_paths(cache, active):
        print(f"Reclaim unused hosted cache: {path}", flush=True)
        if args.apply:
            subprocess.run(["sudo", "rm", "-rf", "--", str(path)], check=True)


if __name__ == "__main__":
    main()
