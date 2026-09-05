#!/usr/bin/env python3
"""Fail when factorization measurements no longer cover their source code.

The newest committed observation for every published curve must use the
current corpus, come from a clean tree, and contain one result for every
corpus instance. Whether it still describes today's source is decided by
content, not by the commit it was taken at: each observation records a
fingerprint of the listing of its system's relevant source, and commits
that listing as a manifest. A measurement therefore survives the squash
merge and any rebase that rewrites the commit but not the content.

The relevant set here is honestly broad -- the Hex factor service call
graph spans HexBasic through HexPolyZ -- and re-measuring needs a
dedicated-hardware session, so runtime-neutral edits are absorbed instead
of re-measured: when the fingerprint has moved, every path whose blob
differs from the manifest must carry a blob-transition exemption under
``scripts/bench/proof_only_runtime_exemptions/``. The relevant sets, the
fingerprinting and the exemption machinery are shared with the other
figure families in ``scripts/bench/sweep_freshness.py``.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.bench import sweep_freshness as freshness  # noqa: E402

ROOT = freshness.ROOT
CORPUS = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
RESULTS = freshness.RESULTS
SYSTEMS = freshness.FACTOR_SYSTEMS

LAKEFILE = "lakefile.lean"

# Lines that begin a top-level Lake declaration. Anything before one of these
# (comments, docstrings, `@[default_target]`) belongs to the declaration that
# follows it.
LAKE_DECL = re.compile(
    r"^(package|require|lean_lib|lean_exe|extern_lib|target|script"
    r"|input_file|module_facet|library_facet|package_facet)\s+(\S+)")


def lakefile_blocks(text: str) -> dict[str, str]:
    """Split a lakefile into top-level declaration blocks, keyed by decl name."""
    blocks: dict[str, str] = {}
    key: str | None = None
    pending: list[str] = []
    current: list[str] = []
    for line in text.splitlines():
        match = LAKE_DECL.match(line)
        if match:
            if key is not None:
                blocks[key] = "\n".join(current).rstrip()
            key = f"{match.group(1)} {match.group(2)}"
            current = pending + [line]
            pending = []
        elif key is None:
            pending.append(line)
        elif line.strip() == "" or line.startswith((" ", "\t")):
            current.append(line)
        else:
            # A bare top-level line (comment, attribute, `open ...`) starts a
            # run that attaches to whatever declaration comes next.
            pending.append(line)
    if key is not None:
        blocks[key] = "\n".join(current).rstrip()
    return blocks


FACTOR_SERVICE_EXE = "hexbz_factor_service"


def factorization_blocks(text: str) -> dict[str, str]:
    """The lakefile declarations that can affect the factorization binary.

    That is the package options, the dependencies, the factorization service
    executable, and the libraries it is built from -- the same set of libraries
    the hex-factor relevant paths already name as factorization source. Every
    other declaration builds a different target and cannot reach this one.
    """
    libs = set(freshness.FACTOR_LIBRARIES)
    relevant = {}
    for name, body in lakefile_blocks(text).items():
        kind, _, decl = name.partition(" ")
        if kind in ("package", "require"):
            relevant[name] = body
        elif kind == "lean_exe" and decl == FACTOR_SERVICE_EXE:
            relevant[name] = body
        elif kind == "lean_lib" and decl in libs:
            relevant[name] = body
    return relevant


def lakefile_texts_differ(before: str, after: str) -> bool:
    """Did this lakefile edit change how the factorization binary is built?

    Nearly every change here registers a *new* library or executable, which
    cannot alter that binary: Lake builds each target from its own declaration.
    Comparing whole-file blobs therefore flagged every such pull request, and
    each one needed its own proof-only exemption keyed to a blob that the next
    merge invalidated.

    So compare only the declarations the factorization binary is built from.
    """
    old_blocks = factorization_blocks(before)
    new_blocks = factorization_blocks(after)
    if set(old_blocks) != set(new_blocks):
        return True
    return any(new_blocks[name] != body for name, body in old_blocks.items())


def build_only_lakefile_edit(difference: freshness.Difference) -> bool:
    """A lakefile transition that cannot reach the factorization binary."""
    if difference.path != LAKEFILE:
        return False
    if difference.baseline is None or difference.current is None:
        return False
    return not lakefile_texts_differ(
        freshness.git("cat-file", "blob", difference.baseline),
        freshness.git("cat-file", "blob", difference.current))


def load_current_reports(corpus_sha: str):
    newest = {}
    for path in sorted(RESULTS.glob("hexbz-factor-sweep-*.json")):
        report = json.loads(path.read_text())
        if report.get("config", {}).get("corpus_sha256") != corpus_sha:
            continue
        timestamp = report.get("env", {}).get("timestamp_unix_ms") or 0
        for system in report.get("config", {}).get("systems", []):
            if system in SYSTEMS and (
                    system not in newest or timestamp > newest[system][0]):
                newest[system] = (timestamp, path, report)
    return newest


def observation(system: str, timestamp, path: Path, report) -> (
        freshness.Observation | None):
    """The fingerprint this report recorded for one system, if it has one."""
    digest = report.get("env", {}).get("source_fingerprints", {}).get(system)
    if not digest:
        return None
    return freshness.Observation(
        fingerprint=digest, label=path.name, timestamp=timestamp)


def record(report_path: Path, ref: str | None) -> int:
    """Stamp a freshly measured sweep with the source it measured.

    The sweep driver deliberately does not do this itself: it is a shared
    relevant path for all six systems, so editing it would mark every
    comparator record stale, and the comparators have no exemption
    channel. Run this straight after a sweep instead.

    The listing is read from the commit the sweep recorded, which is the
    source it actually measured, and falls back to the index when the
    report has no resolvable commit.
    """
    report = json.loads(report_path.read_text())
    systems = [system for system in report.get("config", {}).get("systems", [])
               if system in SYSTEMS]
    if not systems:
        print(f"{report_path.name}: no measured system to fingerprint",
              file=sys.stderr)
        return 1
    if ref is None:
        commit = report.get("env", {}).get("git_commit")
        if commit and subprocess.run(
                ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
                cwd=ROOT, capture_output=True).returncode == 0:
            ref = commit
    fingerprints = {}
    for system in systems:
        family = freshness.factor_family(system)
        listing = (freshness.tree_listing(family, ref) if ref
                   else freshness.index_listing(family))
        fingerprints[system] = freshness.record(family, listing)
    env = report.setdefault("env", {})
    env["source_fingerprints"] = dict(sorted(
        ((env.get("source_fingerprints") or {}) | fingerprints).items()))
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    source = f"commit {ref[:12]}" if ref else "the index"
    print(f"{report_path.name}: recorded {len(fingerprints)} fingerprint(s) "
          f"from {source}")
    for system, digest in sorted(fingerprints.items()):
        print(f"  {system} {digest} "
              f"({freshness.factor_family(system).name}-{digest}.manifest)")
    return 0


def main() -> int:
    corpus_sha = hashlib.sha256(CORPUS.read_bytes()).hexdigest()
    corpus_names = {
        json.loads(line)["name"] for line in CORPUS.read_text().splitlines()
        if line.strip()
    }
    newest = load_current_reports(corpus_sha)
    errors = []
    current_rows = {}

    for system in SYSTEMS:
        if system not in newest:
            errors.append(f"{system}: no measurement for the current corpus")
            continue
        timestamp, path, report = newest[system]
        env = report.get("env", {})
        if env.get("git_dirty") is not False:
            errors.append(f"{system}: {path.name} was measured from a dirty tree")
        rows = [row for row in report.get("results", []) if row.get("system") == system]
        current_rows[system] = rows
        names = {row.get("name") for row in rows}
        if names != corpus_names:
            missing = sorted(corpus_names - names)
            extra = sorted(names - corpus_names)
            details = []
            if missing:
                details.append(f"missing {len(missing)}: " + ", ".join(missing))
            if extra:
                details.append(f"extra {len(extra)}: " + ", ".join(str(n) for n in extra))
            errors.append(f"{system}: {path.name} corpus mismatch; " + "; ".join(details))
        duplicates = sorted(str(name) for name, count in Counter(
            row.get("name") for row in rows).items() if count != 1)
        if duplicates:
            errors.append(
                f"{system}: {path.name} has duplicate rows: " + ", ".join(duplicates))
        if not report.get("cross_check", {}).get("ok"):
            errors.append(f"{system}: {path.name} failed its differential cross-check")

        family = freshness.factor_family(system)
        recorded = observation(system, timestamp, path, report)
        if recorded is None:
            errors.append(
                f"{system}: {path.name} records no source fingerprint; "
                f"re-measure, or record one from the measuring commit with "
                f"scripts/bench/sweep_freshness.py --record {family.name} "
                f"--ref <commit>")
            continue
        verdict = freshness.assess(
            family, [recorded], allow=build_only_lakefile_edit)
        errors.extend(f"{system}: {error}" for error in verdict.errors)

    # Newest-per-system plots may combine records made at different times.
    # Recheck those selected answers together rather than relying only on each
    # source record's internal cross-check.
    for name in sorted(corpus_names):
        answers = {}
        for system, rows in current_rows.items():
            row = next((row for row in rows if row.get("name") == name), None)
            if row is not None and row.get("status") == "ok":
                degrees = row.get("factor_degrees")
                if degrees is None:
                    errors.append(f"{system}: {name} answered without factor_degrees")
                else:
                    answers[system] = tuple(degrees)
        if len(set(answers.values())) > 1:
            rendered = ", ".join(
                f"{system}={list(degrees)}" for system, degrees in sorted(answers.items()))
            errors.append(f"{name}: current-system factor degrees disagree: {rendered}")

    if errors:
        print("factorization performance data is stale:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        print("re-measure the affected systems on the benchmarking host, or, "
              "for an edit that cannot change what was measured, add one JSON "
              "file naming the exact blob transition under "
              "scripts/bench/proof_only_runtime_exemptions/", file=sys.stderr)
        return 1
    print("factorization performance data covers the current corpus and source")
    return 0


def cli(argv: list[str]) -> int:
    if argv and argv[0] == "--record":
        if len(argv) not in (2, 4) or (len(argv) == 4 and argv[2] != "--ref"):
            print("usage: check_factor_sweep_freshness.py "
                  "--record <sweep.json> [--ref REF]", file=sys.stderr)
            return 2
        return record(Path(argv[1]), argv[3] if len(argv) == 4 else None)
    if argv:
        print("usage: check_factor_sweep_freshness.py "
              "[--record <sweep.json> [--ref REF]]", file=sys.stderr)
        return 2
    return main()


if __name__ == "__main__":
    raise SystemExit(cli(sys.argv[1:]))
