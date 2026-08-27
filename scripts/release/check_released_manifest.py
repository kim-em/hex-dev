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
from release import aggregate_readme  # noqa: E402


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


def release_build_modules() -> set[str]:
    """Read complete development umbrellas from their monorepo Lake target."""
    lakefile = (REPO_ROOT / "lakefile.lean").read_text(encoding="utf-8")
    match = re.search(
        r"(?ms)^lean_lib HexFactorizationModules where\n"
        r"(?P<body>.*?)(?=^lean_(?:lib|exe) |\Z)",
        lakefile,
    )
    if match is None:
        fail("lakefile.lean has no HexFactorizationModules target")
    return set(re.findall(r"`([A-Z][A-Za-z0-9_.]+)", match.group("body")))


def aggregate_umbrella_imports() -> list[str]:
    """Read the umbrellas imported by the monorepo's aggregate mirror."""
    source = (REPO_ROOT / "HexAggregateCheck.lean").read_text(encoding="utf-8")
    if not re.search(r"(?m)^module$", source):
        fail("HexAggregateCheck.lean must be a module, like the released aggregate")
    return re.findall(r"(?m)^public import ([A-Z][A-Za-z0-9_.]+)$", source)


def release_executables() -> dict[str, str]:
    """Read monorepo executable names and root modules."""
    lakefile = (REPO_ROOT / "lakefile.lean").read_text(encoding="utf-8")
    matches = re.finditer(
        r"(?ms)^lean_exe\s+(?P<name>[A-Za-z0-9_]+)\s+where\n"
        r"(?P<body>.*?)(?=^lean_(?:lib|exe) |\Z)",
        lakefile,
    )
    out: dict[str, str] = {}
    for match in matches:
        root = re.search(r"(?m)^\s*root\s*:=\s*`([A-Z][A-Za-z0-9_.]+)", match.group("body"))
        if root is not None:
            out[match.group("name")] = root.group(1)
    return out


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
            if not isinstance(entry.get("precompile_modules", False), bool):
                fail(f"{repo}: precompile_modules must be a Boolean")
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
            build_modules = entry.get("build_modules", [])
            if (
                not isinstance(build_modules, list)
                or not all(isinstance(module, str) for module in build_modules)
                or len(build_modules) != len(set(build_modules))
            ):
                fail(f"{repo}: build_modules must be a duplicate-free string list")
            for module in build_modules:
                if not module.startswith(lib + "."):
                    fail(f"{repo}: development module {module} is outside {lib}")
                module_path = REPO_ROOT / Path(*module.split(".")).with_suffix(".lean")
                if not module_path.is_file():
                    fail(
                        f"{repo}: development module does not exist: "
                        f"{module_path.relative_to(REPO_ROOT)}"
                    )
            executables = entry.get("executables", {})
            if (
                not isinstance(executables, dict)
                or not all(
                    isinstance(name, str) and isinstance(module, str)
                    for name, module in executables.items()
                )
            ):
                fail(f"{repo}: executables must map names to root modules")
            for name, module in executables.items():
                module_path = REPO_ROOT / Path(*module.split(".")).with_suffix(".lean")
                if not module_path.is_file():
                    fail(
                        f"{repo}: executable {name} root does not exist: "
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

    # `leanprover/hex`'s umbrella is a module and so may only import modules.
    # `HexAggregateCheck` reproduces that constraint inside this monorepo, which
    # only works while it imports the same umbrellas in the same order.
    lib_by_repo = {
        entry["repo"].split("/", 1)[1]: entry["lib"]
        for entry in entries
        if entry.get("lib")
    }
    expected_imports = [lib_by_repo[pin] for pin in aggregate["pins"]]
    actual_imports = aggregate_umbrella_imports()
    if actual_imports != expected_imports:
        fail(
            "HexAggregateCheck.lean does not mirror the leanprover/hex pins; "
            f"expected {expected_imports}, found {actual_imports}"
        )

    # The aggregate's README is generated, so a released library reaches it
    # without a hand edit. That only holds if every row's label is present and
    # no entry off the table carries one.
    template = aggregate.get("readme_template")
    if not isinstance(template, str) or not (REPO_ROOT / template).is_file():
        fail("leanprover/hex must declare a readme_template that exists")
    labelled = {entry["repo"] for entry in aggregate_readme.table_entries(document)}
    for entry in entries:
        repo = entry["repo"]
        component = entry.get("component")
        if repo in labelled:
            if not isinstance(component, str) or not component.strip():
                fail(f"{repo}: aggregated library must declare a component label")
        elif component is not None:
            fail(f"{repo}: component labels belong only on aggregated libraries")
    venues = {key for key, _label in aggregate_readme.VENUES}
    for entry in entries:
        announcements = entry.get("announcements")
        if announcements is None:
            continue
        repo = entry["repo"]
        if repo not in labelled:
            fail(f"{repo}: announcements belong only on aggregated libraries")
        if not isinstance(announcements, dict) or not announcements:
            fail(f"{repo}: announcements must be a non-empty venue map")
        unknown = sorted(set(announcements) - venues)
        if unknown:
            fail(f"{repo}: unknown announcement venues {unknown}; "
                 f"known are {sorted(venues)}")
        for venue, url in announcements.items():
            if not isinstance(url, str) or not url.startswith("https://"):
                fail(f"{repo}: {venue} announcement must be an https URL")
    try:
        aggregate_readme.render(document, REPO_ROOT / template)
    except ValueError as exc:
        fail(f"leanprover/hex README does not render: {exc}")

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

    manifest_builds = {
        module
        for entry in entries
        for module in entry.get("build_modules", [])
    }
    lake_builds = release_build_modules()
    if manifest_builds != lake_builds:
        fail(
            "manifest build_modules differ from the HexFactorizationModules "
            f"Lake target; missing={sorted(lake_builds - manifest_builds)}, "
            f"extra={sorted(manifest_builds - lake_builds)}"
        )

    lake_executables = release_executables()
    for entry in entries:
        for name, module in entry.get("executables", {}).items():
            if lake_executables.get(name) != module:
                fail(
                    f"{entry['repo']}: executable {name} must root at {module} "
                    "in lakefile.lean"
                )

    libraries = load_libraries()
    # A manifest entry is a publication commitment, and three entries in one
    # week arrived with their implementation merges while the library's phase
    # pipeline was still at 0 — each one broke every full sync on its empty
    # repository until it was withdrawn by hand. A new entry may only exist
    # once the library has completed the whole pipeline. The libraries below
    # were already published before this rule existed and are grandfathered at
    # the phase they had then: each may only move up (a regression fails), no
    # library may join this list, and an entry leaves it by reaching Phase 7.
    prepublished_floor = {
        "HexRowReduceMathlib": 5,
        "HexDeterminantMathlib": 5,
        "HexBareissMathlib": 5,
    }
    graduated = sorted(
        lib for lib in prepublished_floor
        if lib in libraries and libraries[lib].done_through >= 7
    )
    if graduated:
        fail(
            "Phase-7 libraries must leave prepublished_floor: "
            + ", ".join(graduated)
        )
    for entry in entries:
        lib = entry.get("lib")
        if lib not in libraries:
            continue
        recorded = libraries[lib].done_through
        required = prepublished_floor.get(lib, 7)
        if recorded < required:
            fail(
                f"{entry['repo']}: {lib} is recorded at done_through "
                f"{recorded}; a released.yml entry requires done_through "
                f"{required} ({'its grandfathered floor' if lib in prepublished_floor else 'the completed phase pipeline'}) "
                "— finish the phases first, or withdraw the entry until then"
            )
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
        # A repo's conformance or bench sidecar may import libraries its
        # published library does not (declared per entry as
        # `conformance_pins` / `bench_pins`); the SPEC of the owning library
        # records why. These are sanctioned additions to the closure, never
        # replacements.
        for field in ("conformance_pins", "bench_pins"):
            extra = set(entry.get(field, []))
            undeclared = extra & expected
            if undeclared:
                fail(
                    f"{entry['repo']}: {field} {sorted(undeclared)} are "
                    "already in the library dependency closure; list only "
                    "the sidecar-only additions"
                )
            expected |= extra
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
