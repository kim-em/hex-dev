#!/usr/bin/env python3
"""Require fixed users of persistent comparator drivers to warm each child.

The shared ``Hex.BenchOracle.Flint`` process is lazy and cached only within one
LeanBench child.  A fixed registration that reaches ``runOp`` (possibly through
local adapter definitions or an imported bench helper) must therefore use a
configuration with ``warmupFirstIter := true``.  The same requirement applies
to the HexGF2 NTL driver. Otherwise every outer child charges external-driver
startup to its first timed batch.

This is deliberately a small source lint rather than a target-name allowlist:
it follows Lean definition references from the driver call to registered fixed
targets, so adding a new adapter does not silently evade the timing contract.
"""

from __future__ import annotations

import bisect
import re
import sys
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]

_DECL_PREFIX = (
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
)
_DEF_RE = re.compile(
    rf"(?m)^{_DECL_PREFIX}(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
_COMMAND_RE = re.compile(
    rf"(?m)^(?:{_DECL_PREFIX}"
    r"(?:def|abbrev|theorem|lemma|instance|structure|inductive|opaque)\b"
    r"|initialize\b|setup_(?:fixed_)?benchmark\b|namespace\b|section\b"
    r"|end\b|open\b|export\b|#(?:guard|check|eval)\b)"
)
_REGISTRATION_RE = re.compile(
    r"(?m)^setup_fixed_benchmark\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
    r"(?P<where>\s+where\b)?"
)
_IDENT_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
_DRIVER_CALL_RE = re.compile(
    r"(?:\bHex\.BenchOracle\.Flint\."
    r"(?:runOp|runLine|sendRequest|sendRequestLine)\b"
    r"|\brequestNtlLineWithRetry\b)"
)
_WARM_TRUE_RE = re.compile(r"\bwarmupFirstIter\s*:=\s*true\b")
_WARM_FALSE_RE = re.compile(r"\bwarmupFirstIter\s*:=\s*false\b")
_CONDITIONAL_RE = re.compile(r"\b(?:if|match)\b")


@dataclass(frozen=True)
class Definition:
    path: Path
    name: str
    body: str


@dataclass(frozen=True)
class Registration:
    path: Path
    line: int
    target: str
    config: str


def _without_comments(text: str) -> str:
    """Remove nested Lean comments while retaining newlines and string text."""
    out: list[str] = []
    depth = 0
    in_string = False
    escaped = False
    i = 0
    while i < len(text):
        if depth == 0 and in_string:
            char = text[i]
            out.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            i += 1
        elif depth == 0 and text[i] == '"':
            in_string = True
            out.append(text[i])
            i += 1
        elif depth == 0 and text.startswith("--", i):
            newline = text.find("\n", i)
            if newline < 0:
                break
            out.append("\n")
            i = newline + 1
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def _command_chunks(text: str) -> list[tuple[int, int]]:
    starts = [match.start() for match in _COMMAND_RE.finditer(text)]
    return [
        (start, starts[index + 1] if index + 1 < len(starts) else len(text))
        for index, start in enumerate(starts)
    ]


def _parse_source(path: Path) -> tuple[list[Definition], list[Registration]]:
    text = _without_comments(path.read_text(encoding="utf-8"))
    chunks = _command_chunks(text)
    starts = [start for start, _ in chunks]
    definitions: list[Definition] = []
    registrations: list[Registration] = []

    for match in _DEF_RE.finditer(text):
        index = bisect.bisect_right(starts, match.start()) - 1
        end = chunks[index][1] if index >= 0 else len(text)
        definitions.append(Definition(path, match.group(1), text[match.start():end]))

    for match in _REGISTRATION_RE.finditer(text):
        index = bisect.bisect_right(starts, match.start()) - 1
        end = chunks[index][1] if index >= 0 else len(text)
        registrations.append(
            Registration(
                path=path,
                line=text.count("\n", 0, match.start()) + 1,
                target=match.group(1),
                config=text[match.end():end] if match.group("where") else "",
            )
        )
    return definitions, registrations


def _terminal(identifier: str) -> str:
    return identifier.rsplit(".", 1)[-1]


def _persistent_definition_names(definitions: list[Definition]) -> set[str]:
    persistent = {
        definition.name
        for definition in definitions
        if _DRIVER_CALL_RE.search(definition.body)
    }
    changed = True
    while changed:
        changed = False
        for definition in definitions:
            if definition.name in persistent:
                continue
            references = {_terminal(token) for token in _IDENT_RE.findall(definition.body)}
            if references & persistent:
                persistent.add(definition.name)
                changed = True
    return persistent


def _config_is_warm(
    config: str,
    path: Path,
    definitions_by_name: dict[str, list[Definition]],
    seen: set[str] | None = None,
) -> bool:
    if _WARM_FALSE_RE.search(config):
        return False
    if _WARM_TRUE_RE.search(config):
        return not _CONDITIONAL_RE.search(config)
    seen = set() if seen is None else seen
    for token in _IDENT_RE.findall(config):
        name = _terminal(token)
        if name in seen:
            continue
        candidates = definitions_by_name.get(name, [])
        local_candidates = [definition for definition in candidates if definition.path == path]
        if local_candidates:
            candidates = local_candidates
        if candidates and all(
            _config_is_warm(
                definition.body, definition.path, definitions_by_name, seen | {name}
            )
            for definition in candidates
        ):
            return True
    return False


def check(repo_root: Path) -> tuple[list[Registration], list[Registration]]:
    definitions: list[Definition] = []
    registrations: list[Registration] = []
    for path in sorted((repo_root / "bench").rglob("*.lean")):
        parsed_definitions, parsed_registrations = _parse_source(path)
        definitions.extend(parsed_definitions)
        registrations.extend(parsed_registrations)

    persistent_names = _persistent_definition_names(definitions)
    definitions_by_name: dict[str, list[Definition]] = {}
    for definition in definitions:
        definitions_by_name.setdefault(definition.name, []).append(definition)

    persistent_registrations = [
        registration
        for registration in registrations
        if _terminal(registration.target) in persistent_names
    ]
    failures = [
        registration
        for registration in persistent_registrations
        if not _config_is_warm(
            registration.config, registration.path, definitions_by_name
        )
    ]
    return persistent_registrations, failures


def main() -> int:
    registrations, failures = check(REPO_ROOT)
    if not registrations:
        print(
            "Persistent-comparator warmup lint found no registrations; "
            "check the driver-call and registration parsers.",
            file=sys.stderr,
        )
        return 1
    if failures:
        print("Persistent-comparator warmup lint failed:", file=sys.stderr)
        for registration in failures:
            relative = registration.path.relative_to(REPO_ROOT)
            print(
                f"  {relative}:{registration.line}: `{registration.target}` "
                "does not resolve to a config with `warmupFirstIter := true`",
                file=sys.stderr,
            )
        print(
            "Each outer LeanBench child must discard one driver call before its "
            "timed inner batch; see SPEC/benchmarking.md §External comparators.",
            file=sys.stderr,
        )
        return 1

    print(
        "check_persistent_flint_warmup: OK "
        f"({len(registrations)} fixed persistent-comparator registration(s) checked)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
