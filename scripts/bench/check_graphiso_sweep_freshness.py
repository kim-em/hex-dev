#!/usr/bin/env python3
"""Fail when the hex-graph-iso cactus figures no longer cover their source.

The committed cactus sweep data under ``reports/bench-results/`` records
in its filename a content fingerprint of the source it measured
(``hexgraphiso-cactus-<fp12>-<host>.jsonl`` plus the matching
``hexgraphiso-pairs-...``), and commits the listing that fingerprint
hashes as ``hexgraphiso-cactus-<fp12>.manifest``. The published figures
in ``reports/figures/`` are rendered from that data. Whenever the current
relevant source has no matching sweep, and the paths it differs in are
not covered by runtime-neutral exemptions, the figures are stale:
regenerate everything with ``scripts/bench/graphiso_cactus_sweep.sh`` and
commit the new data and figures together with the code change.

The relevant-source set covers the hex-graph-iso implementation and its
umbrella, graph substrate, sweep driver, plot script, nauty comparator,
build configuration and Lean toolchain. Vendor prose is excluded; C
sources and headers are tracked. The set and the shared mechanism are
declared in ``scripts/bench/sweep_freshness.py``.

The family declares no exemption channel, so any difference has to be
re-measured, with checked exceptions: a ``.lean`` path whose two blobs are equal once
comments are removed, and additions of plain literal Lake targets in existing
Hex library namespaces outside the measured import closure. Target additions
cannot change existing declarations, build options, defaults, or module
ownership within that closure. Prose under the library tree is edited often
enough, and cannot move a curve, that making every docstring cost a sweep
would either stop the prose being written or make regeneration routine
enough to stop meaning anything.
"""

from __future__ import annotations

import difflib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.bench import sweep_freshness as freshness  # noqa: E402

FAMILY = freshness.GRAPHISO
RESULTS = freshness.RESULTS

SWEEP_RE = re.compile(r"^hexgraphiso-cactus-([0-9a-f]{12})-[^.]+\.jsonl$")


NAME = r"[A-Za-z_][A-Za-z0-9_]*"
MODULE = NAME + r"(?:\." + NAME + r")*"
TARGET = re.compile(
    rf"lean_(exe|lib) ({NAME}) where\n"
    r'  srcDir := "(bench|conformance)"\n'
    rf"  (root|roots|globs) := (`{MODULE}|#\[\s*`{MODULE}(?:\s*,\s*`{MODULE})*\s*,?\s*\])\n")
IMPORT = re.compile(
    rf"[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?"
    rf"({MODULE}(?:[ \t]+{MODULE})*)[ \t]*")
IMPORT_START = re.compile(r"[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b")


def graph_import_prefixes() -> set[str] | None:
    """Over-approximate the graph driver's and tactic's imported namespaces.

    Inspect every local source location for an import, so ambiguity only
    rejects an allowance. Nonlocal imports still contribute their namespace.
    Unsupported import syntax fails closed.
    """
    prefixes = {"HexGraphIso", "Init", "Lean", "Std", "Lake"}
    stack = [freshness.ROOT / "HexGraphIso.lean",
             freshness.ROOT / "bench/HexGraphIso/Cactus.lean"]
    seen = set()
    while stack:
        path = stack.pop()
        if path in seen:
            continue
        seen.add(path)
        if not path.is_file():
            return None
        for line in freshness.strip_lean_comments(path.read_text()).splitlines():
            if not IMPORT_START.match(line):
                continue
            match = IMPORT.fullmatch(line)
            if match is None:
                return None
            for module in match[1].split():
                prefixes.add(module.split(".")[0])
                relative = Path(*module.split(".")).with_suffix(".lean")
                for directory in (freshness.ROOT, freshness.ROOT / "bench",
                                  freshness.ROOT / "conformance"):
                    source = directory / relative
                    if source.is_file():
                        stack.append(source)
    return prefixes


def independent_target_additions(before: str, after: str, prefixes: set[str],
                                 imported: set[str]) -> bool:
    """Recognize only insertions of literal, non-default independent targets.

    Insertions must follow an existing executable's final `root` field and
    precede another target or EOF. This prevents moving an attribute/scoped
    option onto a new target or stealing fields from an existing declaration.
    The rest of the file must remain byte-for-byte equal after comment removal.
    """
    before = freshness.strip_lean_comments(before)
    after = freshness.strip_lean_comments(after)
    old, new = before.splitlines(keepends=True), after.splitlines(keepends=True)
    names = set()
    for kind, start, end, left, right in difflib.SequenceMatcher(
            None, old, new, autojunk=False).get_opcodes():
        if kind == "equal":
            continue
        if kind != "insert":
            return False
        previous = next((line.rstrip("\n") for line in reversed(old[:start]) if line.strip()), "")
        following = next((line.rstrip("\n") for line in old[end:] if line.strip()), "")
        if not re.fullmatch(rf"  root := `{MODULE}", previous):
            return False
        if following and not re.fullmatch(rf"lean_(?:lib|exe) {NAME} where", following):
            return False
        addition = "".join(new[left:right])
        cursor, count = 0, 0
        while cursor < len(addition):
            blank = re.match(r"[ \t]*\n", addition[cursor:])
            if blank:
                cursor += blank.end()
                continue
            match = TARGET.match(addition, cursor)
            if match is None:
                return False
            target_kind, name, _directory, field, value = match.groups()
            if (name in names or re.search(rf"\b{re.escape(name)}\b", before)
                    or (target_kind == "exe") != (field == "root")
                    or (field == "root") != value.startswith("`")):
                return False
            modules = re.findall(rf"`({MODULE})", value)
            # With explicit globs, Lake still defaults roots to #[name].
            if field == "globs" and name in imported:
                return False
            if any(module.split(".")[0] not in prefixes for module in modules):
                return False
            names.add(name)
            count += 1
            cursor = match.end()
        if not count:
            return False
    return bool(names)


def independent_lake_targets(difference: freshness.Difference) -> bool:
    """A checked allowance for new targets outside graph import namespaces."""
    if (difference.path != "lakefile.lean" or difference.baseline is None
            or difference.current is None or difference.baseline_mode != difference.current_mode):
        return False
    imported = graph_import_prefixes()
    if imported is None:
        return False
    # Existing Hex library namespaces cannot be supplied by Lean's external
    # packages. Excluding every imported namespace also rules out ownership
    # changes for modules used by either measured artifact.
    independent = {path.stem for path in freshness.ROOT.glob("Hex*.lean")
                   if path.stem not in imported}
    return independent_target_additions(freshness.blob_text(difference.baseline),
                                        freshness.blob_text(difference.current), independent,
                                        imported)


def observations() -> tuple[list[freshness.Observation], list[str]]:
    """The committed sweeps, newest first, and any that are incomplete.

    A sweep counts only when its pairs leg is committed too: the figures
    need both, so a half-committed regeneration is not a measurement.
    """
    found: list[freshness.Observation] = []
    errors: list[str] = []
    for path in sorted(RESULTS.glob("hexgraphiso-cactus-*.jsonl")):
        match = SWEEP_RE.match(path.name)
        if not match:
            continue
        pairs = path.with_name(path.name.replace("-cactus-", "-pairs-"))
        if not pairs.exists():
            errors.append(f"{pairs.name}: pairs data missing for {path.name}")
            continue
        meta = path.with_name(path.name[:-len(".jsonl")] + ".meta.json")
        recorded = ""
        if meta.exists():
            recorded = json.loads(meta.read_text()).get("date") or ""
        found.append(freshness.Observation(
            fingerprint=match.group(1), label=path.name, timestamp=recorded))
    return found, errors


def runtime_neutral(difference: freshness.Difference) -> bool:
    """The checked allowances shared by freshness and sweep selection."""
    return freshness.lean_comment_only(difference) or independent_lake_targets(difference)


def main() -> int:
    found, errors = observations()
    verdict = freshness.assess(FAMILY, found,
                               allow=runtime_neutral)
    errors.extend(verdict.errors)
    errors.extend(freshness.missing_figures(FAMILY))

    if errors:
        print("hex-graph-iso cactus freshness check failed:")
        for error in errors:
            print(f"  - {error}")
        print(f"regenerate with {FAMILY.regenerate} and commit the data, "
              "manifest and figures with the code change")
        return 1
    print(f"hex-graph-iso cactus figures cover the current source "
          f"({verdict.summary()})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
