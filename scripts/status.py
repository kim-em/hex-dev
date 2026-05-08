#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import subprocess
import sys

from libgraph import RELEASE_LIBRARIES, check_lakefile_alignment, load_lakefile_libs, load_libraries, pascal_to_spec_path


PHASE_NAMES = {
    1: "library scaffolding",
    2: "scaffolding review",
    3: "conformance testing",
    4: "performance & benchmarking",
    5: "implementation work loop",
    6: "proof polishing",
    7: "user-facing documentation",
}
DEPENDENCY_PHASES = {1, 3, 4}


def blockers_for(libraries, name: str, phase: int) -> list[str]:
    if phase not in DEPENDENCY_PHASES:
        return []
    blockers = []
    for dep in libraries[name].deps:
        if libraries[dep].done_through < phase:
            blockers.append(f"{dep}.done_through >= {phase}")
    return blockers


def entry_lines(libraries, name: str) -> list[str]:
    info = libraries[name]
    if not info.is_active:
        return [
            f"{name} is {info.status} (not dispatched)",
            f"spec: {pascal_to_spec_path(name)}",
            f"to activate: bump status to active in libraries.yml "
            f"(plus Lake entry + root file; see PLAN/Conventions.md "
            f"§'Library status')",
        ]
    if info.done_through >= 7:
        return [f"{name} is fully done (done_through = {info.done_through})"]
    phase = info.done_through + 1
    lines = [f"{name} -> Phase {phase} ({PHASE_NAMES[phase]})"]
    blockers = blockers_for(libraries, name, phase)
    lines.append(f"done_through: {info.done_through}")
    if blockers:
        lines.append(f"blocked by: {', '.join(blockers)}")
    else:
        lines.append("ready: yes")
    lines.append(f"spec: {pascal_to_spec_path(name)}")
    lines.append(f"plan: PLAN/Phase{phase}.md")
    lines.append(f"on complete: libraries.yml {name}.done_through: {phase}")
    return lines


def print_scoped_library(libraries, name: str) -> int:
    if name not in libraries:
        print(f"unknown library: {name}", file=sys.stderr)
        return 1
    for line in entry_lines(libraries, name):
        print(line)
    return 0


def check_release(root: Path, release: int, libraries) -> int:
    if release not in RELEASE_LIBRARIES:
        print(f"unknown release: {release}", file=sys.stderr)
        return 1
    required = RELEASE_LIBRARIES[release]
    missing = [name for name in required if not libraries[name].is_active or libraries[name].done_through < 7]
    example = root / "Examples" / f"Release{release}.lean"
    print(f"Release {release}")
    if missing:
        print("missing libraries:")
        for name in missing:
            info = libraries[name]
            if not info.is_active:
                print(f"  {name}: status: {info.status} (must be active for release)")
            else:
                print(f"  {name}: needs done_through >= 7 (currently {info.done_through})")
    else:
        print("missing libraries: none")
    print(f"integration example: {example.relative_to(root)}")
    print(f"exists: {'yes' if example.exists() else 'no'}")
    if example.exists():
        result = subprocess.run(
            ["lake", "build", f"+Examples.Release{release}"],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        print(f"builds: {'yes' if result.returncode == 0 else 'no'}")
        if result.returncode != 0:
            print(result.stdout.rstrip())
    else:
        print("builds: no")
    ready = not missing and example.exists()
    print(f"ready: {'yes' if ready else 'no'}")
    return 0


def print_full_status(libraries) -> None:
    ready = []
    blocked = []
    done = []
    skipped = []  # non-active libraries (planned/draft)
    for name, info in libraries.items():
        if not info.is_active:
            skipped.append((name, info.status))
            continue
        if info.done_through >= 7:
            done.append(name)
            continue
        phase = info.done_through + 1
        blockers = blockers_for(libraries, name, phase)
        if blockers:
            blocked.append((name, phase, blockers))
        else:
            ready.append((name, phase))

    print("Ready (dispatch issues in parallel):")
    if ready:
        for name, phase in ready:
            print()
            print(f"  {name} -> Phase {phase} ({PHASE_NAMES[phase]})")
            print(f"    spec: {pascal_to_spec_path(name)}")
            print(f"    plan: PLAN/Phase{phase}.md")
            print(f"    on complete: libraries.yml {name}.done_through: {phase}")
    else:
        print()
        print("  (none)")

    print()
    print("Blocked:")
    if blocked:
        for name, phase, blockers in blocked:
            print()
            print(f"  {name} -> Phase {phase}")
            print(f"    waiting on: {', '.join(blockers)}")
    else:
        print()
        print("  (none)")

    print()
    print("Fully done:")
    if done:
        print("  " + ", ".join(done))
    else:
        print("  (none yet)")

    # Mandatory non-active footer (PLAN/Conventions.md §"Library status").
    # Silent omission would recreate the invisibility problem the status
    # field was introduced to fix.
    print()
    print("Planned (skipped — SPEC ready, implementation deferred):")
    planned = [name for name, status in skipped if status == "planned"]
    if planned:
        print("  " + ", ".join(planned))
    else:
        print("  (none)")
    print()
    print("Draft (skipped — SPEC in progress):")
    drafts = [name for name, status in skipped if status == "draft"]
    if drafts:
        print("  " + ", ".join(drafts))
    else:
        print("  (none)")


def main(argv: list[str]) -> int:
    root = Path(__file__).resolve().parent.parent
    try:
        libraries = load_libraries(root / "libraries.yml")
        alignment_errors = check_lakefile_alignment(libraries, load_lakefile_libs(root / "lakefile.toml"))
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1
    if alignment_errors:
        for error in alignment_errors:
            print(error, file=sys.stderr)
        return 1

    if len(argv) == 1:
        print_full_status(libraries)
        return 0
    if len(argv) == 2:
        return print_scoped_library(libraries, argv[1])
    if len(argv) == 3 and argv[1] == "release":
        try:
            release = int(argv[2])
        except ValueError:
            print(f"invalid release number: {argv[2]}", file=sys.stderr)
            return 1
        return check_release(root, release, libraries)
    print("usage: status.py [<Library> | release <N>]", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
