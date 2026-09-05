#!/usr/bin/env python3
"""Validate the publish-out manifest without cloning released repositories."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import NoReturn

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from libgraph import load_libraries, reachable_dependencies  # noqa: E402
from release.sync_released import (  # noqa: E402
    MANIFEST,
    SKELETON,
    keep_paths,
    managed_paths,
    released_ci_workflows,
    source_build_settings,
)
from release import aggregate_readme  # noqa: E402


# Fields an earlier shape used to publish benchmarks, conformance drivers,
# fixtures and oracles into the mirrors. A released repo ships only its library,
# so an entry carrying one of these is publishing development instruments.
RETIRED_FIELDS = (
    "bench",
    "bench_dir",
    "bench_files",
    "bench_pins",
    "conformance",
    "conformance_files",
    "conformance_pins",
    "fixtures",
    "oracles",
)

# Top-level names a mirror never carries: the development instruments, the
# bench-result and performance-report ledgers, and mirror-local agent notes.
# `keep_paths` exists for a file the mirror owns, not as a way back to
# publishing what the sweep is there to remove. A published figure under
# `reports/figures/` arrives as a managed destination from the entry's
# `figures:` list, never through this hatch.
UNPUBLISHED_TREES = (
    ".claude",
    ".github",
    "bench",
    "conformance",
    "conformance-fixtures",
    "reports",
    "scripts",
    "vendor",
)


def fail(message: str) -> NoReturn:
    raise ValueError(message)


def check_library_only(entry: dict) -> None:
    """Reject an entry that would publish more than its library to a mirror."""
    retired = [field for field in RETIRED_FIELDS if field in entry]
    if retired:
        fail(
            f"{entry['repo']}: {retired} would publish development instruments "
            "to the mirror; benchmarks, conformance drivers, fixtures and "
            "oracles stay in hex-dev"
        )
    if "remove_paths" in entry:
        fail(
            f"{entry['repo']}: remove_paths is retired; the sync now deletes "
            "everything outside the entry's managed paths and the unmanaged "
            "skeleton, so nothing needs enumerating per entry"
        )


def check_keep_paths(entry: dict) -> None:
    """Reject an escape hatch that widens a mirror past its library."""
    for path in keep_paths(entry):
        if path.parts[0] in UNPUBLISHED_TREES:
            fail(
                f"{entry['repo']}: keep_paths entry {path} names a tree no "
                "mirror publishes; benchmarks, conformance drivers, fixtures, "
                "oracles, bench results and performance reports stay in hex-dev"
            )
        if path.parts[0] in SKELETON:
            fail(
                f"{entry['repo']}: keep_paths entry {path} is already kept as "
                "part of every mirror's unmanaged skeleton"
            )


def check_build_settings(entry: dict) -> None:
    """Keep the mirror's build settings derivable from hex-dev's lakefile.

    The sync reads the `lean_lib <lib>` block here and carries its settings into
    the mirror. Two things have to hold for that to be more than a no-op, and
    neither is visible at sync time until a repository is already being
    published: the manifest must not carry a competing hand-written copy of a
    build decision, and the library must still be a `lean_lib` in this
    monorepo's lakefile. A renamed or globbed-away target would otherwise leave
    the sync deriving an empty settings map and publishing a mirror that quietly
    stops precompiling.
    """
    repo = entry["repo"]
    if "precompile_modules" in entry:
        fail(
            f"{repo}: precompile_modules is derived from lakefile.lean, not "
            "declared here; drop the key"
        )
    try:
        source_build_settings(entry["lib"])
    except RuntimeError as error:
        fail(f"{repo}: {error}")


def parse_sync_baseline(text: str, source: str) -> set[str]:
    """Return repository names from a validated release-sync baseline."""
    try:
        document = json.loads(text)
    except json.JSONDecodeError as error:
        fail(f"{source}: invalid JSON: {error}")
    if not isinstance(document, dict):
        fail(f"{source}: sync baseline must be a JSON object")
    published: set[str] = set()
    for repo, revision in document.items():
        if repo == "_comment":
            continue
        if (
            not isinstance(repo, str)
            or not isinstance(revision, str)
            or re.fullmatch(r"[0-9a-f]{40}", revision) is None
        ):
            fail(f"{source}: malformed baseline entry {repo!r}: {revision!r}")
        published.add(repo)
    return published


def published_repositories(repo_root: Path = REPO_ROOT) -> set[str]:
    """Read the live publication ledger, falling back to its bootstrap seed."""
    live_ref = "refs/remotes/origin/release-sync-baseline"
    probe = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "--verify", "--quiet", live_ref],
        check=False,
        capture_output=True,
        text=True,
    )
    if probe.returncode == 0:
        result = subprocess.run(
            ["git", "-C", str(repo_root), "show", f"{live_ref}:synced.json"],
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            fail(
                f"cannot read synced.json from {live_ref}: "
                f"{result.stderr.strip()}"
            )
        return parse_sync_baseline(result.stdout, live_ref)

    bootstrap = repo_root / "scripts" / "release" / "synced.json"
    if not bootstrap.is_file():
        fail(
            "release-sync-baseline is unavailable and the bootstrap "
            "scripts/release/synced.json does not exist"
        )
    return parse_sync_baseline(
        bootstrap.read_text(encoding="utf-8"), str(bootstrap.relative_to(repo_root))
    )


def check_phase_admission(entries: list[dict], libraries: dict, published: set[str]) -> None:
    """Require Phase 7 for entries that have never completed a real sync."""
    for entry in entries:
        lib = entry.get("lib")
        if lib not in libraries:
            continue
        recorded = libraries[lib].done_through
        repo = entry["repo"]
        short = repo.split("/", 1)[1]
        if recorded < 7 and short not in published:
            fail(
                f"{repo}: {lib} is recorded at done_through {recorded}; a new "
                "released.yml entry requires the completed phase pipeline. "
                "Finish Phase 7 or withdraw the entry until then"
            )


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


PUBLISHED_IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)\s*$"
)


def published_import_closure_violations(
    entries: list[dict], repo_root: Path = REPO_ROOT
) -> list[str]:
    """Imports that would leave a released mirror unbuildable.

    A mirror ships its library and pins only published repositories, so every
    module reachable from a released umbrella (or from its `test_modules`,
    `build_modules` and `extra_paths` roots) may import only published
    libraries, the roots its own entry carries through `extra_paths`, and the
    shared `Hex` test kit. `libraries.yml` cannot see this drift: its `deps`
    already name the unpublished library, and the pin rule keeps only the
    published subset. Returns one message per offending import.
    """
    published = {entry["lib"] for entry in entries if entry.get("lib")}
    extra_roots: dict[str, set[str]] = {}
    for entry in entries:
        roots: set[str] = set()
        for extra in entry.get("extra_paths") or []:
            source = extra.get("src", "") if isinstance(extra, dict) else ""
            roots.add(Path(source).name.removesuffix(".lean"))
        extra_roots[entry.get("repo", "")] = roots
    short_by_repo = {entry.get("repo", ""): entry.get("repo", "").split("/", 1)[-1] for entry in entries}
    extra_roots_by_short = {short_by_repo[repo]: roots for repo, roots in extra_roots.items()}
    violations: list[str] = []
    for entry in entries:
        lib = entry.get("lib")
        if not lib:
            continue
        # A pinned upstream's extra roots are published with that upstream.
        pinned_roots: set[str] = set()
        for pin in entry.get("pins") or []:
            pinned_roots |= extra_roots_by_short.get(pin, set())
        allowed = published | extra_roots.get(entry["repo"], set()) | pinned_roots | {"Hex"}
        stack = [lib] + list(entry.get("test_modules") or []) + list(
            entry.get("build_modules") or []
        )
        for root in extra_roots.get(entry["repo"], set()):
            stack.append(root)
        seen: set[str] = set()
        while stack:
            module = stack.pop()
            if module in seen:
                continue
            seen.add(module)
            path = repo_root / Path(*module.split(".")).with_suffix(".lean")
            if not path.is_file():
                continue
            for line in path.read_text(encoding="utf-8").splitlines():
                match = PUBLISHED_IMPORT_RE.match(line.split("--", 1)[0].rstrip())
                if not match:
                    continue
                imported = match.group(1)
                top = imported.split(".", 1)[0]
                if not top.startswith("Hex"):
                    continue
                if top not in allowed:
                    violations.append(
                        f"{entry['repo']}: {module} imports {imported}, "
                        f"whose library {top} is not in released.yml"
                    )
                    continue
                stack.append(imported)
    return sorted(set(violations))


def check_ci_workflows(entries: list[dict]) -> None:
    """Require one complete, cache-safe managed workflow per released repo."""
    workflows = released_ci_workflows()
    expected = {entry["repo"].split("/", 1)[1] for entry in entries}
    actual = set(workflows)
    if actual != expected:
        fail(
            "released-ci.yml differs from the release manifest; "
            f"missing={sorted(expected - actual)}, extra={sorted(actual - expected)}"
        )
    for entry in entries:
        short = entry["repo"].split("/", 1)[1]
        workflow = workflows[short]
        try:
            parsed = yaml.load(workflow, Loader=yaml.BaseLoader)
        except yaml.YAMLError as exc:
            fail(f"{entry['repo']}: managed CI is invalid YAML: {exc}")
        triggers = parsed.get("on") if isinstance(parsed, dict) else None
        push = triggers.get("push") if isinstance(triggers, dict) else None
        if (
            not isinstance(push, dict)
            or push.get("branches") != ["main"]
            or "pull_request" not in triggers
        ):
            fail(
                f"{entry['repo']}: managed CI must run on main pushes and "
                "pull requests"
            )
        concurrency = parsed.get("concurrency") if isinstance(parsed, dict) else None
        if (
            not isinstance(concurrency, dict)
            or concurrency.get("group") != "${{ github.workflow }}-${{ github.ref }}"
            or concurrency.get("cancel-in-progress")
            != "${{ github.ref != 'refs/heads/main' }}"
        ):
            fail(
                f"{entry['repo']}: managed CI must preserve main runs so their "
                "terminal cache save can finish"
            )
        jobs = parsed.get("jobs") if isinstance(parsed, dict) else None
        if not isinstance(jobs, dict) or not jobs:
            fail(f"{entry['repo']}: managed CI must define jobs")
        for job_name, job in jobs.items():
            if not isinstance(job, dict) or "strategy" in job:
                fail(f"{entry['repo']}: CI job {job_name} must not use a matrix")
            steps = job.get("steps") if isinstance(job, dict) else None
            if not isinstance(steps, list):
                fail(f"{entry['repo']}: CI job {job_name} has no steps")
            indexed = {
                action: [
                    index for index, step in enumerate(steps)
                    if isinstance(step, dict) and step.get("uses") == action
                ]
                for action in (
                    "leanprover/lean-action@v1",
                    "actions/cache/restore@v4",
                    "actions/cache/save@v4",
                )
            }
            if any(len(indices) != 1 for indices in indexed.values()):
                fail(
                    f"{entry['repo']}: CI job {job_name} must contain one "
                    "lean-action, cache restore, and cache save"
                )
            lean_index = indexed["leanprover/lean-action@v1"][0]
            restore_index = indexed["actions/cache/restore@v4"][0]
            save_index = indexed["actions/cache/save@v4"][0]
            if not (lean_index < restore_index < save_index == len(steps) - 1):
                fail(
                    f"{entry['repo']}: CI job {job_name} must restore after "
                    "setup and save only after every verification step"
                )
            lean_inputs = steps[lean_index].get("with", {})
            if lean_inputs.get("use-github-cache") != "false":
                fail(f"{entry['repo']}: lean-action GitHub cache must be disabled")
            if lean_inputs.get("use-mathlib-cache") != "false":
                fail(f"{entry['repo']}: lean-action Mathlib cache must be disabled")
            restore_inputs = steps[restore_index].get("with", {})
            save_inputs = steps[save_index].get("with", {})
            required_paths = {
                ".lake/build",
                ".lake/packages/Hex*/.lake/build",
            }
            cached_paths = {
                path.strip()
                for path in restore_inputs.get("path", "").splitlines()
                if path.strip()
            }
            saved_paths = {
                path.strip()
                for path in save_inputs.get("path", "").splitlines()
                if path.strip()
            }
            if cached_paths != required_paths:
                fail(
                    f"{entry['repo']}: CI job {job_name} cache paths differ; "
                    f"missing={sorted(required_paths - cached_paths)}, "
                    f"extra={sorted(cached_paths - required_paths)}"
                )
            key = restore_inputs.get("key", "")
            restore_prefixes = [
                prefix.strip()
                for prefix in restore_inputs.get("restore-keys", "").splitlines()
                if prefix.strip()
            ]
            if (
                key != save_inputs.get("key")
                or saved_paths != cached_paths
                or len(restore_prefixes) != 1
                or key
                != restore_prefixes[0]
                + "${{ github.run_id }}-${{ github.run_attempt }}"
                or "${{ runner.os }}-${{ runner.arch }}" not in key
                or "${{ hashFiles(" not in key
            ):
                fail(
                    f"{entry['repo']}: CI job {job_name} cache must use a "
                    "run-unique save key and stable restore prefix"
                )
            save_condition = steps[save_index].get("if", "")
            if (
                "github.event_name == 'push'" not in save_condition
                or "github.ref == 'refs/heads/main'" not in save_condition
            ):
                fail(
                    f"{entry['repo']}: CI job {job_name} must save only from main"
                )

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

        check_library_only(entry)

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
            check_build_settings(entry)
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
            check_keep_paths(entry)
            for kept in keep_paths(entry):
                if any(
                    kept == destination
                    or kept in destination.parents
                    or destination in kept.parents
                    for destination in destinations
                ):
                    fail(
                        f"{repo}: keep_paths entry {kept} overlaps a managed destination"
                    )
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

    check_ci_workflows(entries)

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
    # Three entries once landed at phase 0 and broke every full sync against
    # their empty split repositories. Phase 7 is therefore required for a new
    # entry. Once the sync's live baseline proves that a repository has really
    # been published, normal done_through rollback no longer removes it from
    # the source-of-truth publication graph.
    check_phase_admission(entries, libraries, published_repositories())
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
        # A released repo publishes only its library, so its pins are exactly
        # that library's dependency closure.
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

    drift = published_import_closure_violations(entries)
    if drift:
        fail(
            "released umbrellas import unpublished libraries, so the next sync "
            "would publish unbuildable mirrors:\n  " + "\n  ".join(drift)
        )

    print(
        f"release manifest: {len(entries) - 1} split repositories + "
        f"1 aggregate; paths, CI, pins, import closure, test targets, and "
        f"topological constraints valid"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, yaml.YAMLError) as exc:
        print(f"release manifest: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
