#!/usr/bin/env python3
"""Fail when factorization measurements no longer cover their source code.

The newest committed observation for every published curve must use the current
corpus, come from a clean recorded commit, and contain one result for every
corpus instance. A measurement remains valid across a squash merge when the
relevant source tree is unchanged. It becomes stale when its system adapter,
the shared sweep protocol, the corpus, or (for Hex) executable factorization
code differs from that recorded commit.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
RESULTS = ROOT / "reports" / "bench-results"
PROOF_ONLY_EXEMPTIONS = (
    ROOT / "scripts" / "bench" / "proof_only_runtime_exemptions")
SYSTEMS = ("hex-factor", "flint", "ntl", "pari", "isabelle-bz", "isabelle-lll")

COMMON_PATHS = {
    "bench/corpus/hexbz-factor-corpus.jsonl",
    "scripts/bench/factor_sweep.py",
}

SYSTEM_PATHS = {
    "flint": {"scripts/oracle/bz_flint_service.py"},
    "ntl": {
        "scripts/oracle/bz_ntl_service.cc",
        "scripts/oracle/setup_bz_ntl_driver.sh",
    },
    "pari": {"scripts/oracle/bz_pari_service.py"},
    "isabelle-bz": {
        "scripts/oracle/setup_bz_isabelle.sh",
        "scripts/oracle/bz-isabelle/",
    },
    "isabelle-lll": {
        "scripts/oracle/setup_bz_lll_isabelle.sh",
        "scripts/oracle/bz-lll-isabelle/",
    },
}

HEX_PREFIXES = (
    "Hex/",
    "HexArith/",
    "HexBareiss/",
    "HexBerlekamp/",
    "HexBerlekampZassenhaus/",
    "HexHensel/",
    "HexLLL/",
    "HexMatrix/",
    "HexModArith/",
    "HexPoly/",
    "HexPolyFp/",
    "HexPolyZ/",
    "HexBasic/",
)

HEX_PATHS = {
    "bench/HexBench/FactorService.lean",
    "lakefile.lean",
    "lake-manifest.json",
    "lean-toolchain",
}


def git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=ROOT, text=True, capture_output=True, check=False)
    if result.returncode:
        raise SystemExit(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


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
    `HEX_PREFIXES` already names as factorization source. Every other
    declaration builds a different target and cannot reach this one.
    """
    libs = {prefix.rstrip("/") for prefix in HEX_PREFIXES}
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


def lakefile_affects_runtime(baseline: str) -> bool:
    """Did this lakefile edit change how the factorization binary is built?

    Nearly every change here registers a *new* library or executable, which
    cannot alter that binary: Lake builds each target from its own declaration.
    Comparing whole-file blobs therefore flagged every such pull request, and
    each one needed its own proof-only exemption keyed to a blob that the next
    merge invalidated.

    So compare only the declarations the factorization binary is built from.
    """
    before = git_blob(baseline, LAKEFILE)
    after = git_blob("HEAD", LAKEFILE)
    if before is None or after is None:
        return True
    return lakefile_texts_differ(
        git("cat-file", "blob", before), git("cat-file", "blob", after))


def lakefile_texts_differ(before: str, after: str) -> bool:
    """The block comparison behind `lakefile_affects_runtime`, without git."""
    old_blocks = factorization_blocks(before)
    new_blocks = factorization_blocks(after)
    if set(old_blocks) != set(new_blocks):
        return True
    return any(new_blocks[name] != body for name, body in old_blocks.items())


def source_path(system: str, path: str) -> bool:
    if path in COMMON_PATHS:
        return True
    if system == "hex-factor":
        return path in HEX_PATHS or (
            path.endswith(".lean") and path.startswith(HEX_PREFIXES))
    return any(path == source or path.startswith(source)
               for source in SYSTEM_PATHS[system])


def git_blob(ref: str, path: str) -> str | None:
    result = subprocess.run(
        ["git", "rev-parse", f"{ref}:{path}"], cwd=ROOT,
        text=True, capture_output=True, check=False)
    return result.stdout.strip() if result.returncode == 0 else None


def load_proof_only_exemptions() -> set[tuple[str, str, str]]:
    """Load exact, reviewer-auditable source transitions with no runtime effect.

    Both blob IDs are required so an exemption expires automatically as soon
    as the file changes again. This is intentionally narrower than exempting a
    path or trusting a commit-message marker.

    One file per exemption. A single shared list cannot be merged: entries are
    appended by whichever branches happen to be open, so concurrent pull
    requests collide on it textually even when their exemptions are unrelated.
    """
    exemptions = set()
    for entry_path in sorted(PROOF_ONLY_EXEMPTIONS.glob("*.json")):
        entry = json.loads(entry_path.read_text())
        required = {"path", "baseline_blob", "current_blob", "reason"}
        missing = required - entry.keys()
        if missing:
            raise SystemExit(
                f"{entry_path}: missing {', '.join(sorted(missing))}")
        exemptions.add((
            entry["path"], entry["baseline_blob"], entry["current_blob"]))
    return exemptions


def proof_only_transition(
        path: str, baseline: str,
        exemptions: set[tuple[str, str, str]]) -> bool:
    baseline_blob = git_blob(baseline, path)
    current_blob = git_blob("HEAD", path)
    return (path, baseline_blob, current_blob) in exemptions


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


def main() -> int:
    corpus_sha = hashlib.sha256(CORPUS.read_bytes()).hexdigest()
    corpus_names = {
        json.loads(line)["name"] for line in CORPUS.read_text().splitlines()
        if line.strip()
    }
    newest = load_current_reports(corpus_sha)
    proof_only_exemptions = load_proof_only_exemptions()
    errors = []
    current_rows = {}

    for system in SYSTEMS:
        if system not in newest:
            errors.append(f"{system}: no measurement for the current corpus")
            continue
        _, path, report = newest[system]
        env = report.get("env", {})
        commit = env.get("git_commit")
        if env.get("git_dirty") is not False:
            errors.append(f"{system}: {path.name} was measured from a dirty tree")
        if not commit:
            errors.append(f"{system}: {path.name} has no source commit")
            continue
        commit_exists = subprocess.run(
            ["git", "cat-file", "-e", f"{commit}^{{commit}}"],
            cwd=ROOT, capture_output=True).returncode == 0
        if not commit_exists:
            errors.append(f"{system}: measured commit {commit[:12]} is unavailable")
            continue
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
        changed = git("diff", "--name-only", f"{commit}..HEAD").splitlines()
        stale = sorted(
            name for name in changed
            if source_path(system, name) and not (
                system == "hex-factor" and (
                    proof_only_transition(name, commit, proof_only_exemptions)
                    or (name == LAKEFILE
                        and not lakefile_affects_runtime(commit)))))
        if stale:
            errors.append(
                f"{system}: source differs from {commit[:12]}: " + ", ".join(stale))

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
        return 1
    print("factorization performance data covers the current corpus and source")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
