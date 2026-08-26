#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

from libgraph import load_libraries


SETUP_RE = re.compile(r"^\s*setup_benchmark\s+([A-Za-z0-9_'.]+)\s+([A-Za-z0-9_']+)\s*=>\s*(.+?)\s*$")
DERIVATION_RE = re.compile(
    r"(?i)\b(cost[- ]model|deriv(?:e|ation)|complexity|declared (?:model|complexity)|"
    r"theta|big[- ]?o|worst[- ]case|amorti[sz]ed|linear|quadratic|cubic|log(?:arithmic)?|"
    r"schoolbook|dominates|bound)\b|O\(",
)
COMMENT_START_RE = re.compile(r"^\s*/-")
COMMENT_END_RE = re.compile(r"-/\s*$")


def fallback_report_slug(library_name: str) -> str:
    parts: list[str] = []
    for index, char in enumerate(library_name):
        previous = library_name[index - 1] if index else ""
        if index and char.isupper() and not previous.isupper():
            parts.append("-")
        parts.append(char.lower())
    return "".join(parts)


def report_slug(root: Path, library_name: str) -> str:
    normalized_name = library_name.lower()
    # Per-library SPEC lives at `<Lib>/SPEC/<slug>.md`; source-less planned
    # libraries keep theirs under `SPEC/Libraries/<slug>.md`.
    specs = list((root / "SPEC" / "Libraries").glob("*.md")) + list(root.glob("Hex*/SPEC/*.md"))
    for spec in sorted(specs):
        slug = spec.stem
        if slug.replace("-", "") == normalized_name:
            return slug
    return fallback_report_slug(library_name)


def check_headline_reports(root: Path) -> tuple[int, str | None]:
    libraries = load_libraries(root / "libraries.yml")
    checked = 0
    for name, info in libraries.items():
        if info.done_through < 4:
            continue
        # External libraries carry their Phase-4 headline reports in their
        # own released repo, not locally; skip the local-report check.
        if info.is_external:
            continue
        checked += 1
        report = root / "reports" / f"{report_slug(root, name)}-performance.md"
        if info.mathlib and info.phase4 is None and not report.exists():
            continue
        if not report.exists():
            return checked, f"{name}: missing Phase-4 headline report {report.relative_to(root)}"

        text = report.read_text(encoding="utf-8")
        if info.phase4 is None:
            continue
        for comparator in info.phase4.comparators:
            if comparator.tool not in text:
                return (
                    checked,
                    f"{name}: Phase-4 headline report {report.relative_to(root)} "
                    f"does not mention comparator {comparator.tool!r}",
                )
        for family in info.phase4.input_families:
            if family.name not in text:
                return (
                    checked,
                    f"{name}: Phase-4 headline report {report.relative_to(root)} "
                    f"does not mention input family {family.name!r}",
                )
    return checked, None


def run_git(args: list[str], root: Path, *, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if check and result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def default_base(root: Path) -> str | None:
    candidates: list[str] = []
    github_base = os.environ.get("GITHUB_BASE_REF")
    if github_base:
        candidates.extend([f"origin/{github_base}", github_base])
    candidates.extend(["origin/main", "origin/master", "main", "master"])
    for candidate in candidates:
        if subprocess.run(["git", "rev-parse", "--verify", candidate], cwd=root,
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0:
            merge_base = run_git(["merge-base", candidate, "HEAD"], root, check=False).strip()
            if merge_base:
                return merge_base
    return None


def changed_setup_lines(root: Path, base: str) -> list[tuple[Path, int, str]]:
    diff = run_git(
        ["diff", "--unified=0", "--no-ext-diff", f"{base}...HEAD", "--", "*.lean"],
        root,
    )
    changed: list[tuple[Path, int, str]] = []
    current_file: Path | None = None
    new_line = 0
    for line in diff.splitlines():
        if line.startswith("+++ b/"):
            current_file = Path(line[len("+++ b/"):])
            continue
        if line.startswith("@@ "):
            match = re.search(r"\+(\d+)(?:,\d+)?", line)
            if not match:
                continue
            new_line = int(match.group(1))
            continue
        if current_file is None:
            continue
        if line.startswith("+") and not line.startswith("+++"):
            text = line[1:]
            if SETUP_RE.match(text):
                changed.append((current_file, new_line, text))
            new_line += 1
        elif line.startswith("-"):
            # A deleted line: never advances the new-file cursor. The guard is
            # unconditional on `-` because a deleted `--`-comment line renders as
            # `--- …` in the diff and must not be mistaken for the `--- a/<file>`
            # header (that header precedes `+++ b/<file>`, so it is already
            # skipped by the `current_file is None` check and reset at the next
            # `@@`). Counting a deleted `--` comment as context inflated the
            # new-file line number of the following `setup_benchmark`.
            continue
        else:
            new_line += 1
    return changed


def all_setup_lines(root: Path) -> list[tuple[Path, int, str]]:
    found: list[tuple[Path, int, str]] = []
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        rel = path.relative_to(root)
        for idx, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if SETUP_RE.match(line):
                found.append((rel, idx, line))
    return found


def adjacent_comment(lines: list[str], line_no: int) -> str:
    idx = line_no - 2
    while idx >= 0 and not lines[idx].strip():
        idx -= 1
    if idx < 0:
        return ""

    if lines[idx].lstrip().startswith("--"):
        block: list[str] = []
        while idx >= 0 and lines[idx].lstrip().startswith("--"):
            block.append(lines[idx])
            idx -= 1
        return "\n".join(reversed(block))

    if COMMENT_END_RE.search(lines[idx]):
        block = [lines[idx]]
        idx -= 1
        while idx >= 0:
            block.append(lines[idx])
            if COMMENT_START_RE.match(lines[idx]):
                return "\n".join(reversed(block))
            idx -= 1

    return ""


def commits_for_line(root: Path, base: str, rel_path: Path, line_no: int) -> list[str]:
    output = run_git(
        [
            "log",
            "--format=%H%x00%B%x00ENDCOMMIT",
            "--reverse",
            "-L",
            f"{line_no},{line_no}:{rel_path.as_posix()}",
            f"{base}..HEAD",
        ],
        root,
        check=False,
    )
    if not output.strip():
        output = run_git(
            [
                "log",
                "--format=%H%x00%B%x00ENDCOMMIT",
                "--reverse",
                "-G",
                r"setup_benchmark.*=>",
                f"{base}..HEAD",
                "--",
                rel_path.as_posix(),
            ],
            root,
            check=False,
        )
    commits: list[str] = []
    for chunk in output.split("ENDCOMMIT"):
        chunk = chunk.strip("\n\0")
        if chunk:
            commits.append(chunk)
    return commits


def check_registrations(root: Path, registrations: list[tuple[Path, int, str]], base: str | None) -> list[str]:
    errors: list[str] = []
    cache: dict[Path, list[str]] = {}
    for rel_path, line_no, line in registrations:
        path = root / rel_path
        cache.setdefault(rel_path, path.read_text(encoding="utf-8").splitlines())
        comment = adjacent_comment(cache[rel_path], line_no)
        match = SETUP_RE.match(line)
        name = match.group(1) if match else "<unknown>"
        if not comment:
            errors.append(f"{rel_path}:{line_no}: {name} lacks an adjacent cost-model derivation comment")
        elif not DERIVATION_RE.search(comment):
            errors.append(
                f"{rel_path}:{line_no}: adjacent comment for {name} does not look like a cost-model derivation"
            )

        if base is not None:
            commits = commits_for_line(root, base, rel_path, line_no)
            if commits and not any(DERIVATION_RE.search(message) for message in commits):
                errors.append(
                    f"{rel_path}:{line_no}: commits changing {name} lack a cost-model derivation in the message"
                )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check Phase-4 headline reports and benchmark registration derivation requirements."
    )
    parser.add_argument("--base", help="base revision for changed-registration checks")
    parser.add_argument(
        "--all",
        action="store_true",
        help="check every setup_benchmark registration instead of only registrations changed on this branch",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parent.parent
    try:
        report_count, report_error = check_headline_reports(root)
        if report_error is not None:
            print(report_error, file=sys.stderr)
            return 1

        base = None if args.all else (args.base or default_base(root))
        if not args.all and base is None:
            print(
                "could not determine a git merge base; pass --base or fetch branch history",
                file=sys.stderr,
            )
            return 1
        registrations = all_setup_lines(root) if args.all else changed_setup_lines(root, base)
        errors = check_registrations(root, registrations, None if args.all else base)
    except RuntimeError as exc:
        print(exc, file=sys.stderr)
        return 1

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    scope = "all registrations" if args.all else "changed registrations"
    print(
        f"Phase 4 checks passed "
        f"(headline reports: {report_count}; {scope}: {len(registrations)})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
