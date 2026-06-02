#!/usr/bin/env python3
"""Scrub inverted ``depends-on:`` edges from open issues.

Implements the maintenance sweep specified in
PLAN/Conventions.md §"Inverted dependencies are rejected" and
PLAN/Phase0.md step 4: a ``depends-on:`` edge must point *down*
the import DAG (the carrying issue's library may import the dep's
library, per ``scripts/libgraph.may_import``). An edge pointing the
other way is **inverted** — never a real blocker, only a mis-scoped
issue. The pre-creation guard refuses to write inverted edges; this
sweep scrubs any that predate the guard or slip through.

For each open issue:
  - Parse the ``library:`` line and every ``depends-on: #N`` line
    from the body.
  - Resolve each dependency's ``library:`` line (cached).
  - Flag edges where ``not may_import(L_A, L_B)``.
  - For a flagged edge: drop the ``depends-on:`` line from the body,
    post a comment recording the dropped edge and why, clear the
    ``blocked`` label if no other open real dependency remains, and
    apply ``replan``.

Issues missing a ``library:`` line (carrier or dep) are reported and
left untouched — the predicate has nothing to check against. The
script defaults to a dry run; pass ``--apply`` to perform mutations.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import OrderedDict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from libgraph import (  # noqa: E402
    LibraryInfo,
    load_libraries,
    may_import,
    reachable_dependencies,
    repo_root,
)


LIBRARY_LINE_RE = re.compile(r"^library:\s*(\S+)\s*$", re.MULTILINE)
DEPENDS_LINE_RE = re.compile(r"^depends-on:\s*#(\d+)\s*$", re.MULTILINE)


@dataclass(frozen=True)
class InvertedEdge:
    carrier: int
    carrier_library: str
    dep: int
    dep_library: str

    def reason(self) -> str:
        return (
            f"#{self.carrier} (library: {self.carrier_library}) cannot import "
            f"#{self.dep} (library: {self.dep_library}); the edge points up the "
            f"import DAG, so it is never a real blocker "
            f"(PLAN/Conventions.md §\"Inverted dependencies are rejected\")."
        )


def run_gh(args: list[str], *, input_text: str | None = None) -> str:
    proc = subprocess.run(
        ["gh", *args],
        check=True,
        text=True,
        input=input_text,
        capture_output=True,
    )
    return proc.stdout


def list_open_issues() -> list[dict]:
    out = run_gh([
        "issue",
        "list",
        "--state",
        "open",
        "--limit",
        "500",
        "--json",
        "number,body,labels",
    ])
    return json.loads(out)


def fetch_issue(number: int) -> dict:
    out = run_gh([
        "issue",
        "view",
        str(number),
        "--json",
        "number,state,body,labels",
    ])
    return json.loads(out)


def parse_library(body: str) -> str | None:
    match = LIBRARY_LINE_RE.search(body or "")
    return match.group(1) if match else None


def parse_depends(body: str) -> list[int]:
    return [int(n) for n in DEPENDS_LINE_RE.findall(body or "")]


def drop_depends_line(body: str, dep: int) -> str:
    """Remove every ``depends-on: #<dep>`` line from ``body``.

    Preserves surrounding line breaks but collapses a trailing blank
    line so we do not leave an isolated empty line where the edge was.
    """
    pattern = re.compile(rf"^depends-on:\s*#{dep}\s*\r?\n?", re.MULTILINE)
    return pattern.sub("", body or "")


def remaining_open_deps(
    body: str,
    issue_cache: dict[int, dict],
    fetcher,
) -> list[int]:
    open_deps: list[int] = []
    for dep in parse_depends(body):
        info = issue_cache.get(dep)
        if info is None:
            info = fetcher(dep)
            issue_cache[dep] = info
        if info.get("state", "").upper() == "OPEN":
            open_deps.append(dep)
    return open_deps


def classify_edges(
    issues: list[dict],
    libraries: OrderedDict[str, LibraryInfo],
    closure: dict[str, set[str]],
    issue_cache: dict[int, dict],
    fetcher,
) -> tuple[list[InvertedEdge], list[str]]:
    """Return (inverted edges, unscrubbable-report lines)."""
    inverted: list[InvertedEdge] = []
    reports: list[str] = []
    for issue in issues:
        body = issue.get("body") or ""
        number = issue["number"]
        deps = parse_depends(body)
        if not deps:
            continue
        carrier_lib = parse_library(body)
        if carrier_lib is None:
            reports.append(
                f"#{number}: missing `library:` line; cannot classify "
                f"{len(deps)} depends-on edge(s)"
            )
            continue
        if carrier_lib not in libraries:
            reports.append(
                f"#{number}: `library: {carrier_lib}` is not in libraries.yml; "
                f"cannot classify {len(deps)} depends-on edge(s)"
            )
            continue
        for dep in deps:
            dep_info = issue_cache.get(dep)
            if dep_info is None:
                try:
                    dep_info = fetcher(dep)
                except subprocess.CalledProcessError as exc:
                    reports.append(
                        f"#{number}: depends-on #{dep} could not be fetched ({exc})"
                    )
                    continue
                issue_cache[dep] = dep_info
            dep_lib = parse_library(dep_info.get("body") or "")
            if dep_lib is None:
                reports.append(
                    f"#{number}: depends-on #{dep} has no `library:` line; "
                    f"cannot classify this edge"
                )
                continue
            if dep_lib not in libraries:
                reports.append(
                    f"#{number}: depends-on #{dep} has `library: {dep_lib}` "
                    f"not in libraries.yml; cannot classify this edge"
                )
                continue
            if not may_import(carrier_lib, dep_lib, libraries, closure):
                inverted.append(
                    InvertedEdge(
                        carrier=number,
                        carrier_library=carrier_lib,
                        dep=dep,
                        dep_library=dep_lib,
                    )
                )
    return inverted, reports


def apply_edge(
    edge: InvertedEdge,
    issue_cache: dict[int, dict],
    fetcher,
) -> None:
    """Drop the edge from the carrier, comment, relabel, mark replan."""
    carrier = issue_cache.get(edge.carrier) or fetcher(edge.carrier)
    body = carrier.get("body") or ""
    new_body = drop_depends_line(body, edge.dep)
    if new_body == body:
        # Nothing to do; the line was already gone (concurrent edit).
        return
    run_gh(
        ["issue", "edit", str(edge.carrier), "--body-file", "-"],
        input_text=new_body,
    )
    # Refresh the cached body so later edges on the same carrier see it.
    carrier["body"] = new_body
    issue_cache[edge.carrier] = carrier

    comment = (
        f"Inverted-dependency scrub: removed `depends-on: #{edge.dep}`. "
        f"{edge.reason()}"
    )
    run_gh(
        ["issue", "comment", str(edge.carrier), "--body-file", "-"],
        input_text=comment,
    )

    # If no open real dependency remains, drop the `blocked` label.
    if not remaining_open_deps(new_body, issue_cache, fetcher):
        labels = {label["name"] for label in carrier.get("labels") or []}
        if "blocked" in labels:
            run_gh(["issue", "edit", str(edge.carrier), "--remove-label", "blocked"])
            labels.discard("blocked")
            carrier["labels"] = [{"name": name} for name in sorted(labels)]
            issue_cache[edge.carrier] = carrier

    # Route to replan for re-derivation from the SPEC.
    labels = {label["name"] for label in carrier.get("labels") or []}
    if "replan" not in labels:
        run_gh(["issue", "edit", str(edge.carrier), "--add-label", "replan"])
        labels.add("replan")
        carrier["labels"] = [{"name": name} for name in sorted(labels)]
        issue_cache[edge.carrier] = carrier


def format_summary(
    inverted: Iterable[InvertedEdge], reports: Iterable[str], applied: bool
) -> str:
    inverted = list(inverted)
    reports = list(reports)
    lines = []
    verb = "Scrubbed" if applied else "Would scrub"
    if inverted:
        lines.append(f"{verb} {len(inverted)} inverted edge(s):")
        for edge in inverted:
            lines.append(
                f"  #{edge.carrier} ({edge.carrier_library}) "
                f"→ #{edge.dep} ({edge.dep_library})"
            )
    else:
        lines.append("No inverted edges found.")
    if reports:
        lines.append("")
        lines.append(f"Unscrubbable ({len(reports)}):")
        for line in reports:
            lines.append(f"  {line}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--apply",
        action="store_true",
        help="Perform the mutations (default: dry-run; print findings only).",
    )
    args = parser.parse_args()

    libraries = load_libraries(repo_root() / "libraries.yml")
    closure = reachable_dependencies(libraries)

    issues = list_open_issues()
    issue_cache: dict[int, dict] = {issue["number"]: issue for issue in issues}
    inverted, reports = classify_edges(
        issues, libraries, closure, issue_cache, fetch_issue
    )

    if args.apply:
        for edge in inverted:
            apply_edge(edge, issue_cache, fetch_issue)

    print(format_summary(inverted, reports, applied=args.apply))
    return 0


if __name__ == "__main__":
    sys.exit(main())
