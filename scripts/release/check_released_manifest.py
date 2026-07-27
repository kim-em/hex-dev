#!/usr/bin/env python3
"""Validate the publish-out manifest without cloning released repositories."""

from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from libgraph import load_libraries, reachable_dependencies  # noqa: E402
from release.sync_released import MANIFEST, managed_paths  # noqa: E402


def fail(message: str) -> None:
    raise ValueError(message)


def release_test_modules() -> set[str]:
    """Read the explicit module set from the monorepo's test-only Lake target."""
    lakefile = (REPO_ROOT / "lakefile.lean").read_text(encoding="utf-8")
    match = re.search(
        r"(?ms)^lean_lib HexReleaseTests where\n(?P<body>.*?)(?=^lean_(?:lib|exe) |\Z)",
        lakefile,
    )
    if match is None:
        fail("lakefile.lean has no HexReleaseTests target")
    return set(re.findall(r"`([A-Z][A-Za-z0-9_.]+)", match.group("body")))


def main() -> int:
    document = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    entries = document.get("repos") if isinstance(document, dict) else None
    if not isinstance(entries, list) or not entries:
        fail("released.yml must contain a non-empty repos list")

    repo_names: set[str] = set()
    library_names: set[str] = set()
    seen_repos: set[str] = set()
    owner_by_repo: dict[str, str] = {}
    aggregate_entries: list[dict] = []

    for index, entry in enumerate(entries, start=1):
        if not isinstance(entry, dict):
            fail(f"entry {index} is not a mapping")
        repo = entry.get("repo")
        if not isinstance(repo, str) or repo.count("/") != 1:
            fail(f"entry {index} has malformed repo {repo!r}")
        owner, short = repo.split("/", 1)
        if owner != "leanprover":
            fail(f"{repo}: released repositories must live under leanprover")
        if repo in repo_names or short in owner_by_repo:
            fail(f"duplicate released repository {repo}")
        repo_names.add(repo)
        owner_by_repo[short] = owner

        pins = entry.get("pins")
        if not isinstance(pins, list) or not all(isinstance(pin, str) for pin in pins):
            fail(f"{repo}: pins must be a list of repository short names")
        if len(pins) != len(set(pins)):
            fail(f"{repo}: pins contains a duplicate")
        unknown = set(pins) - seen_repos
        if unknown:
            fail(f"{repo}: pins must name earlier repositories; not yet seen: {sorted(unknown)}")

        if entry.get("pins_only"):
            aggregate_entries.append(entry)
            if index != len(entries):
                fail(f"{repo}: pins_only aggregate must be the final entry")
            if entry.get("lib"):
                fail(f"{repo}: pins_only aggregate must not declare lib")
        else:
            lib = entry.get("lib")
            if not isinstance(lib, str) or not lib:
                fail(f"{repo}: non-aggregate entry must declare lib")
            if lib in library_names:
                fail(f"duplicate released library {lib}")
            library_names.add(lib)
            test_modules = entry.get("test_modules", [])
            if (
                not isinstance(test_modules, list)
                or not all(isinstance(module, str) for module in test_modules)
                or len(test_modules) != len(set(test_modules))
            ):
                fail(f"{repo}: test_modules must be a duplicate-free string list")
            for module in test_modules:
                if not module.startswith(lib + "."):
                    fail(f"{repo}: test module {module} is outside {lib}")
                module_path = REPO_ROOT / Path(*module.split(".")).with_suffix(".lean")
                if not module_path.is_file():
                    fail(
                        f"{repo}: test module does not exist: "
                        f"{module_path.relative_to(REPO_ROOT)}"
                    )
            mappings = managed_paths(entry)
            if not mappings:
                fail(f"{repo}: entry manages no source paths")
            destinations: set[Path] = set()
            for source, destination, _is_dir in mappings:
                if not source.exists():
                    fail(f"{repo}: managed source does not exist: {source.relative_to(REPO_ROOT)}")
                if destination in destinations:
                    fail(f"{repo}: duplicate managed destination {destination}")
                destinations.add(destination)
            if entry.get("readme", True):
                readme = REPO_ROOT / lib / "README.md"
                text = readme.read_text(encoding="utf-8")
                title = f"# {short}"
                if not text.startswith(title + "\n"):
                    fail(f"{repo}: README must start with {title!r}")
                required = (
                    "# Quickstart",
                    "# Functionality",
                    "# Verification",
                    "# Contributing",
                )
                positions = [text.find(heading + "\n") for heading in required]
                if any(position < 0 for position in positions):
                    missing = [
                        heading for heading, position in zip(required, positions)
                        if position < 0
                    ]
                    fail(f"{repo}: README is missing required headings {missing}")
                if "```toml\n[[require]]" not in text:
                    fail(f"{repo}: README Quickstart must contain a Lake TOML require")
                if f"https://github.com/{repo}.git" not in text:
                    fail(f"{repo}: README Quickstart does not name its released repository")
                if "https://github.com/kim-em/hex-dev" not in text:
                    fail(f"{repo}: README Contributing section does not link to hex-dev")

        if entry.get("lakefile") not in {"lean", "toml"}:
            fail(f"{repo}: lakefile must be 'lean' or 'toml'")

        seen_repos.add(short)

    if len(aggregate_entries) != 1:
        fail(f"released.yml must contain exactly one pins_only aggregate; found {len(aggregate_entries)}")
    aggregate = aggregate_entries[0]
    if aggregate["repo"] != "leanprover/hex":
        fail("the pins_only aggregate must be leanprover/hex")
    split_repos = {
        entry["repo"].split("/", 1)[1]
        for entry in entries
        if not entry.get("pins_only") and entry.get("aggregate", True)
    }
    aggregate_pins = set(aggregate["pins"])
    if aggregate_pins != split_repos:
        fail(
            "leanprover/hex pins differ from the complete split-repository set; "
            f"missing={sorted(split_repos - aggregate_pins)}, "
            f"extra={sorted(aggregate_pins - split_repos)}"
        )

    manifest_tests = {
        module
        for entry in entries
        for module in entry.get("test_modules", [])
    }
    lake_tests = release_test_modules()
    if manifest_tests != lake_tests:
        fail(
            "manifest test_modules differ from the HexReleaseTests Lake target; "
            f"missing={sorted(lake_tests - manifest_tests)}, "
            f"extra={sorted(manifest_tests - lake_tests)}"
        )

    libraries = load_libraries()
    closure = reachable_dependencies(libraries)
    repo_by_library = {
        entry["lib"]: entry["repo"].split("/", 1)[1]
        for entry in entries
        if entry.get("lib") in libraries
    }
    for entry in entries:
        lib = entry.get("lib")
        if lib not in libraries:
            continue
        expected = {
            repo_by_library[dependency]
            for dependency in closure[lib]
            if dependency in repo_by_library
        }
        actual = set(entry["pins"])
        if actual != expected:
            fail(
                f"{entry['repo']}: pins differ from the published dependency closure; "
                f"missing={sorted(expected - actual)}, extra={sorted(actual - expected)}"
            )

    print(
        f"release manifest: {len(entries) - 1} split repositories + "
        f"1 aggregate; paths, pins, test targets, and topological constraints valid"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, yaml.YAMLError) as exc:
        print(f"release manifest: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
