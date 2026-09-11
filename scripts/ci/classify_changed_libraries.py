#!/usr/bin/env python3
"""Classify a CI change by the libraries that own its changed paths."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from libgraph import library_owner_for_path, load_libraries, topological_order


REPO_ROOT = Path(__file__).resolve().parents[2]
SHARED_PREFIXES = ("Hex/", "scripts/ci/", ".github/")
SHARED_PATHS = {
    "scripts/oracle/common.py",
    "lakefile.lean",
    "lake-manifest.json",
    "lean-toolchain",
}
OWNED_TEST_ROOTS = {"bench", "conformance", "conformance-fixtures"}
IGNORED_PATHS = {"libraries.yml", "AGENTS.md", "LICENSE", ".gitignore"}
IGNORED_PREFIXES = ("SPEC/", "PLAN/", "docs/", "reports/", ".claude/")
ORACLE_ALIASES = {
    "bz": "HexBerlekampZassenhaus",
    "graphiso": "HexGraphIso",
    "matrixcarriers": "HexDeterminant",
}


@dataclass(frozen=True)
class Classification:
    libraries: tuple[str, ...]
    all_libraries: bool
    reason: str

    @property
    def library_filter(self) -> str:
        # The verification scripts define an empty filter as the full suite.
        return "" if self.all_libraries else " ".join(self.libraries)


def _normalise(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "", name.lower())


def _closest_library(name: str, library_names: set[str]) -> str | None:
    """Return the longest library name that prefixes an auxiliary path name."""
    normalised = _normalise(name)
    matches = [
        library
        for library in library_names
        if normalised.startswith(_normalise(library))
    ]
    return max(matches, key=len, default=None)


def _is_documentation(path: str) -> bool:
    return (
        path.endswith(".md")
        or path in IGNORED_PATHS
        or path.startswith(IGNORED_PREFIXES)
    )


def load_oracle_owners(repo_root: Path = REPO_ROOT) -> dict[str, set[str]]:
    """Read the oracle runner's public tuple listing, keyed by script path."""
    result = subprocess.run(
        ["bash", "scripts/ci/run_oracles.sh", "--list"],
        cwd=repo_root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    owners: dict[str, set[str]] = {}
    for line in result.stdout.splitlines():
        owner, _emit, oracle, _fixture = line.split("|", 3)
        owners.setdefault(oracle, set()).add(owner)
    return owners


def classify_paths(
    paths: list[str],
    *,
    oracle_owners: dict[str, set[str]],
) -> Classification:
    libraries = load_libraries()
    library_names = set(libraries)
    selected: set[str] = set()
    reasons: list[str] = []

    for raw_path in paths:
        path = raw_path.removeprefix("./")
        if path in SHARED_PATHS or path.startswith(SHARED_PREFIXES):
            return Classification((), True, f"shared infrastructure changed: {path}")

        owner = library_owner_for_path(Path(path), libraries)
        if owner == "Hex":
            return Classification((), True, f"shared library infrastructure changed: {path}")
        if owner == "HexGraph":
            selected.add("HexGraphIso")
            reasons.append(f"{path} -> HexGraphIso")
            continue
        if owner in library_names:
            selected.add(owner)
            reasons.append(f"{path} -> {owner}")
            continue

        parts = Path(path).parts
        if len(parts) >= 2 and parts[0] in OWNED_TEST_ROOTS:
            owner = _closest_library(parts[1], library_names)
            if owner is None:
                return Classification((), True, f"unowned test path changed: {path}")
            selected.add(owner)
            reasons.append(f"{path} -> {owner}")
            continue

        if len(parts) == 3 and parts[:2] == ("scripts", "oracle"):
            if path in oracle_owners:
                owners = oracle_owners[path]
            else:
                stem = Path(path).stem.removeprefix("test_")
                normalised_stem = _normalise(stem)
                alias = next(
                    (
                        library
                        for prefix, library in ORACLE_ALIASES.items()
                        if normalised_stem.startswith(prefix)
                    ),
                    None,
                )
                inferred = alias or _closest_library(f"Hex{stem}", library_names)
                if inferred is None:
                    return Classification((), True, f"shared or unowned oracle changed: {path}")
                owners = {inferred}
            selected.update(owners)
            reasons.append(f"{path} -> {','.join(sorted(owners))}")
            continue

        if _is_documentation(path):
            continue

        return Classification((), True, f"unclassified path changed: {path}")

    if not selected:
        return Classification((), True, "no changed path mapped to a library")

    ordered = tuple(name for name in topological_order(libraries) if name in selected)
    detail = "; ".join(reasons)
    return Classification(ordered, False, detail)


def changed_paths(base_sha: str, head: str = "HEAD") -> list[str]:
    merge_base = subprocess.run(
        ["git", "merge-base", base_sha, head],
        cwd=REPO_ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()
    output = subprocess.run(
        ["git", "diff", "--no-renames", "--name-only", "-z", merge_base, head],
        cwd=REPO_ROOT,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
    return [part.decode("utf-8", "surrogateescape") for part in output.split(b"\0") if part]


def write_github_output(path: Path, classification: Classification) -> None:
    with path.open("a", encoding="utf-8") as output:
        output.write(f"library_filter={classification.library_filter}\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--event", required=True)
    parser.add_argument("--base")
    parser.add_argument("--github-output", type=Path, required=True)
    args = parser.parse_args()

    if args.event != "pull_request":
        classification = Classification((), True, f"{args.event} event runs the full suite")
    elif not args.base:
        classification = Classification((), True, "pull request base SHA is unavailable")
    else:
        try:
            paths = changed_paths(args.base)
            classification = classify_paths(paths, oracle_owners=load_oracle_owners())
        except (OSError, subprocess.CalledProcessError, ValueError) as error:
            classification = Classification((), True, f"classification failed: {error}")

    write_github_output(args.github_output, classification)
    scope = "all libraries" if classification.all_libraries else " ".join(classification.libraries)
    print(f"CI verification library scope: {scope}")
    print(f"Reason: {classification.reason}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
