#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re
import sys

from libgraph import (
    RELEASE_LIBRARIES,
    check_lakefile_alignment,
    load_lakefile_libs,
    load_libraries,
    pascal_to_spec_path,
    reachable_dependencies,
    topological_order,
)


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


EXAMPLES_LIB = "HexReleaseExamples"
CI_WORKFLOW = Path(".github") / "workflows" / "ci.yml"


def lean_lib_modules(lakefile_text: str, lib: str) -> list[str]:
    """Return the backticked module names in `lean_lib <lib>`'s declaration.

    The block runs from its `lean_lib` line to the next top-level line; `--`
    comments are ignored. Raises ValueError unless exactly one block exists.
    """
    lines = lakefile_text.splitlines()
    starts = [i for i, line in enumerate(lines) if re.fullmatch(rf"lean_lib {lib} where\s*", line)]
    if len(starts) != 1:
        raise ValueError(f"expected one `lean_lib {lib}` declaration, found {len(starts)}")
    body = []
    for line in lines[starts[0] + 1:]:
        if line and not line[0].isspace():
            break
        body.append(line.split("--", 1)[0])
    modules = re.findall(r"`([A-Za-z0-9_.]+)", "\n".join(body))
    if not modules:
        raise ValueError(f"`lean_lib {lib}` lists no modules")
    return modules


def ci_builds_lib(workflow_text: str, lib: str) -> bool:
    """Whether the CI workflow's `HEX_LIB_TARGETS` list contains `lib`."""
    for match in re.finditer(r"HEX_LIB_TARGETS=([^\"\n]*)", workflow_text):
        if lib in match.group(1).split():
            return True
    return False


def check_release(root: Path, release: int, libraries) -> int:
    """Report release readiness without building anything.

    CI builds the integration example through the `HexReleaseExamples` target,
    so this checks that the example is covered by that target; whether it
    builds is the CI result for the commit being released.
    """
    if release not in RELEASE_LIBRARIES:
        print(f"unknown release: {release}", file=sys.stderr)
        return 1
    roots = RELEASE_LIBRARIES[release]
    closure = reachable_dependencies(libraries)
    required_names = set(roots)
    for name in roots:
        required_names.update(closure[name])
    required = [name for name in topological_order(libraries) if name in required_names]
    missing = [name for name in required if not libraries[name].is_active or libraries[name].done_through < 7]
    module = f"Examples.Release{release}"
    example = root / "Examples" / f"Release{release}.lean"
    try:
        registered = module in lean_lib_modules((root / "lakefile.lean").read_text(), EXAMPLES_LIB)
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    ci_covered = registered and ci_builds_lib((root / CI_WORKFLOW).read_text(), EXAMPLES_LIB)
    print(f"Release {release}")
    print(f"libraries (including transitive dependencies): {len(required)}")
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
    print(f"CI-covered ({EXAMPLES_LIB} in {CI_WORKFLOW}): {'yes' if ci_covered else 'no'}")
    ready = not missing and example.exists() and ci_covered
    print(f"ready: {'yes, subject to green CI on the release commit' if ready else 'no'}")
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
