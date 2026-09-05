#!/usr/bin/env python3
"""Content-fingerprint freshness checking for published performance figures.

Every published figure is rendered from committed sweep data, and that
data has to keep describing the source it measured. This module is the
one mechanism all such checks are built from.

A **family** declares the source whose content the figures depend on: a
set of include paths (exact files, directory prefixes, or a prefix with a
single ``*`` suffix glob such as ``HexArith/*.lean``) minus a set of
exclusions. Its **listing** is the ``mode blob stage\tpath`` lines for
exactly those files, in path order, and its **fingerprint** is the first
twelve hex digits of the sha256 of that listing.

Keying on content rather than on the measuring commit is deliberate. A
recorded commit has to stay resolvable forever, which fails for data
regenerated inside the pull request that changes the code: a squash merge
rewrites the measuring commit, and so does any rebase. A fingerprint
depends only on what was measured, and history rewrites preserve content.

Content keying alone cannot absorb runtime-neutral edits, though: a
docstring change moves the fingerprint just as a hot-loop rewrite does.
That is why each observation also commits its listing verbatim as a
**manifest** next to the data. When no committed observation matches the
current fingerprint, the check diffs the current listing against the
newest manifest path by path, and accepts the difference only when every
differing path is covered by a blob-transition exemption. Exemptions name
both the baseline and the current blob, so they expire automatically when
the file changes again, and they live one-per-file so that concurrent
pull requests never collide on a shared list.

The pay-off is that a broad relevant set (factorization spans HexBasic
through HexPolyZ, and re-measuring needs a dedicated-hardware session)
stays enforceable, while a tight one (hex-graph-iso, minutes to
regenerate) simply re-measures and rarely writes an exemption at all.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "reports" / "bench-results"
FIGURES = ROOT / "reports" / "figures"

MANIFEST_SUFFIX = ".manifest"
FINGERPRINT_DIGITS = 12


def git(*args: str) -> str:
    # `core.quotePath=false` so a non-ASCII path is listed under the name
    # the family declarations match against, rather than as an escape.
    result = subprocess.run(
        ["git", "-c", "core.quotePath=false", *args],
        cwd=ROOT, text=True, capture_output=True, check=False)
    if result.returncode:
        raise SystemExit(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


@dataclass(frozen=True)
class Family:
    """The source a plot family's measurements depend on, and where they live.

    ``include`` and ``exclude`` entries are exact paths, directory
    prefixes ending in ``/``, or a prefix with one ``*`` standing for the
    file name, as in ``HexArith/*.lean``. Keep both sets as tight as
    honesty allows: everything listed here forces a re-measurement (or an
    exemption) when it changes, and everything omitted is a claim that it
    cannot move the curves.
    """

    name: str
    include: tuple[str, ...]
    exclude: tuple[str, ...] = ()
    exemptions: Path | None = None
    figures: tuple[str, ...] = ()
    regenerate: str = ""

    def matches(self, path: str) -> bool:
        return (any(_entry_matches(entry, path) for entry in self.include)
                and not any(_entry_matches(entry, path)
                            for entry in self.exclude))

    def pathspec(self) -> list[str]:
        """A git pathspec covering the include set, before Python filtering.

        Deliberately coarse: `git ls-tree` rejects exclude magic, so both
        the index and the tree listing filter with `matches` instead, and
        the pathspec only has to avoid walking the whole repository.
        """
        return sorted(
            {entry.partition("*")[0] for entry in self.include} - {""})

    def staging_pathspec(self) -> list[str]:
        """The exact pathspec, for staging the relevant source before a sweep.

        Unlike `pathspec` this carries the exclusions, so regenerating a
        family never stages documentation the author had not staged.
        """
        return list(self.include) + [f":!{entry}" for entry in self.exclude]


def _entry_matches(entry: str, path: str) -> bool:
    if entry.endswith("/"):
        return path.startswith(entry)
    prefix, star, suffix = entry.partition("*")
    if star:
        return path.startswith(prefix) and path.endswith(suffix)
    return path == entry or path.startswith(entry + "/")


def index_listing(family: Family) -> str:
    """The family's listing as the index has it, i.e. what a sweep measures."""
    raw = git("ls-files", "-s", "--", *family.pathspec())
    kept = []
    for line in raw.splitlines():
        meta, _, path = line.partition("\t")
        _mode, _blob, stage = meta.split()
        if stage != "0":
            raise SystemExit(
                f"{path} is unmerged in the index; resolve the conflict "
                f"before fingerprinting {family.name}")
        if family.matches(path):
            kept.append(line + "\n")
    return "".join(kept)


def tree_listing(family: Family, ref: str) -> str:
    """The family's listing at a commit, in the same format as the index one.

    Gitlinks count as entries just as `git ls-files -s` reports them, so
    that a submodule under a family path cannot make the two listings of
    the same content disagree.
    """
    raw = git("ls-tree", "-r", ref, "--", *family.pathspec())
    rows = []
    for line in raw.splitlines():
        meta, _, path = line.partition("\t")
        mode, kind, blob = meta.split()
        if kind in ("blob", "commit") and family.matches(path):
            rows.append((path, mode, blob))
    rows.sort(key=lambda row: row[0].encode())
    return "".join(f"{mode} {blob} 0\t{path}\n" for path, mode, blob in rows)


def fingerprint(listing: str) -> str:
    return hashlib.sha256(
        listing.encode()).hexdigest()[:FINGERPRINT_DIGITS]


def parse_listing(listing: str) -> dict[str, str]:
    """Map each listed path to its blob id."""
    blobs = {}
    for line in listing.splitlines():
        meta, _, path = line.partition("\t")
        _mode, blob, _stage = meta.split()
        blobs[path] = blob
    return blobs


def manifest_path(family: Family, digest: str) -> Path:
    return RESULTS / f"{family.name}-{digest}{MANIFEST_SUFFIX}"


def record(family: Family, listing: str | None = None) -> str:
    """Commit the current listing as a manifest; return its fingerprint."""
    listing = index_listing(family) if listing is None else listing
    digest = fingerprint(listing)
    path = manifest_path(family, digest)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(listing)
    return digest


@dataclass(frozen=True)
class Observation:
    """A committed measurement, and the source fingerprint it was taken at.

    ``timestamp`` only has to order one family's observations against each
    other, so a family may use whatever it records: epoch milliseconds,
    an ISO date string, anything sortable and consistent within the family.
    """

    fingerprint: str
    label: str
    timestamp: float | str = 0.0


@dataclass(frozen=True)
class Difference:
    path: str
    baseline: str | None
    current: str | None

    def render(self) -> str:
        return (f"{self.path} ({(self.baseline or 'absent')[:12]}"
                f" -> {(self.current or 'absent')[:12]})")


def differences(baseline: str, current: str) -> list[Difference]:
    before, after = parse_listing(baseline), parse_listing(current)
    return [Difference(path, before.get(path), after.get(path))
            for path in sorted(set(before) | set(after))
            if before.get(path) != after.get(path)]


def load_exemptions(directory: Path | None) -> set[tuple[str, str, str]]:
    """Load exact, reviewer-auditable source transitions with no runtime effect.

    Both blob ids are required so an exemption expires automatically as
    soon as the file changes again. This is intentionally narrower than
    exempting a path or trusting a commit-message marker.

    One file per exemption. A single shared list cannot be merged:
    entries are appended by whichever branches happen to be open, so
    concurrent pull requests collide on it textually even when their
    exemptions are unrelated.
    """
    exemptions: set[tuple[str, str, str]] = set()
    if directory is None or not directory.is_dir():
        return exemptions
    for entry_path in sorted(directory.glob("*.json")):
        entry = json.loads(entry_path.read_text())
        required = {"path", "baseline_blob", "current_blob", "reason"}
        missing = required - entry.keys()
        if missing:
            raise SystemExit(
                f"{entry_path}: missing {', '.join(sorted(missing))}")
        exemptions.add((
            entry["path"], entry["baseline_blob"], entry["current_blob"]))
    return exemptions


@dataclass
class Verdict:
    """Why a family's figures are current, or how they went stale."""

    fingerprint: str
    matched: Observation | None = None
    baseline: Observation | None = None
    exempted: list[Difference] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)

    @property
    def fresh(self) -> bool:
        return not self.errors

    def summary(self) -> str:
        if self.matched is not None:
            return f"{self.fingerprint} measured by {self.matched.label}"
        if self.baseline is not None:
            return (f"{self.fingerprint} differs from {self.baseline.label}"
                    f" only in {len(self.exempted)} exempted path(s): "
                    + ", ".join(diff.path for diff in self.exempted))
        return self.fingerprint


def assess(family: Family, observations: list[Observation],
           allow=None, listing: str | None = None) -> Verdict:
    """Decide whether committed measurements still cover the current source.

    Fresh when some observation was taken at the current fingerprint.
    Otherwise the newest observation that committed a manifest becomes the
    baseline, and every path whose blob differs must be covered by an
    exemption or by ``allow(difference)``, a family-specific rule for
    paths whose content changes without changing what was measured.
    """
    listing = index_listing(family) if listing is None else listing
    digest = fingerprint(listing)
    verdict = Verdict(fingerprint=digest)

    for observation in observations:
        if observation.fingerprint == digest:
            verdict.matched = observation
            return verdict

    with_manifest = [
        observation for observation in sorted(
            observations, key=lambda o: o.timestamp, reverse=True)
        if manifest_path(family, observation.fingerprint).exists()]
    if not with_manifest:
        verdict.errors.append(
            f"no measurement covers the current source (fingerprint "
            f"{digest}), and none of the {len(observations)} committed "
            f"measurement(s) carries a manifest to compare against")
        return verdict

    verdict.baseline = with_manifest[0]
    baseline = manifest_path(
        family, verdict.baseline.fingerprint).read_text()
    if fingerprint(baseline) != verdict.baseline.fingerprint:
        # The manifest is the whole evidence that the baseline listing is
        # the one that was measured. A manifest that does not hash to the
        # fingerprint it is filed under proves nothing.
        verdict.errors.append(
            f"manifest for {verdict.baseline.fingerprint} does not hash to "
            f"its own fingerprint; it no longer records what "
            f"{verdict.baseline.label} measured")
        return verdict
    exemptions = load_exemptions(family.exemptions)
    unexplained = []
    for difference in differences(baseline, listing):
        key = (difference.path, difference.baseline, difference.current)
        if key in exemptions or (allow is not None and allow(difference)):
            verdict.exempted.append(difference)
        else:
            unexplained.append(difference)
    if unexplained:
        verdict.errors.append(
            f"source differs from {verdict.baseline.label} (fingerprint "
            f"{verdict.baseline.fingerprint}) in paths with no runtime-neutral "
            f"exemption: " + ", ".join(
                difference.render() for difference in unexplained))
    return verdict


def missing_figures(family: Family) -> list[str]:
    return [f"reports/figures/{name} is missing"
            for name in family.figures
            if not (FIGURES / name).exists()]


# --- Families -------------------------------------------------------------

# Documentation under a library tree cannot affect measured performance, so
# SPECs and READMEs are excluded: a doc-only change must not force a sweep.
GRAPHISO = Family(
    name="hexgraphiso-cactus",
    include=(
        "HexGraphIso/",
        "HexGraph/",
        "bench/HexGraphIso/Cactus.lean",
        "scripts/plots/hexgraphiso-cactus.py",
    ),
    exclude=("HexGraphIso/SPEC", "HexGraphIso/README.md"),
    exemptions=ROOT / "scripts" / "bench" / "graphiso_runtime_exemptions",
    figures=(
        "hexgraphiso-canon-cactus.svg",
        "hexgraphiso-pairs-cactus.svg",
        "hexgraphiso-tactic-times.json",
    ),
    regenerate="scripts/bench/graphiso_cactus_sweep.sh",
)

FACTOR_EXEMPTIONS = ROOT / "scripts" / "bench" / "proof_only_runtime_exemptions"

# Everything every factorization system's measurement depends on: the corpus
# it runs and the sweep protocol that drives it.
FACTOR_COMMON = (
    "bench/corpus/hexbz-factor-corpus.jsonl",
    "scripts/bench/factor_sweep.py",
)

# The Hex factorization service call graph, as Lean libraries. Only their
# `.lean` sources count; the C sources under `<library>/ffi/` do reach the
# binary but are not listed, because `Hex/BenchOracle/ffi/` sits in the same
# trees and belongs to the oracles rather than to factorization. Splitting
# those apart is worth doing, and independent of how the data is keyed.
FACTOR_LIBRARIES = (
    "Hex", "HexArith", "HexBareiss", "HexBerlekamp", "HexBerlekampZassenhaus",
    "HexHensel", "HexLLL", "HexMatrix", "HexModArith", "HexPoly", "HexPolyFp",
    "HexPolyZ", "HexBasic",
)

FACTOR_SYSTEM_PATHS = {
    "hex-factor": tuple(
        f"{library}/*.lean" for library in FACTOR_LIBRARIES) + (
        "bench/HexBench/FactorService.lean",
        "HexPrimality/Table.lean",
        "lakefile.lean",
        "lake-manifest.json",
        "lean-toolchain",
    ),
    "flint": ("scripts/oracle/bz_flint_service.py",),
    "ntl": (
        "scripts/oracle/bz_ntl_service.cc",
        "scripts/oracle/setup_bz_ntl_driver.sh",
    ),
    "pari": ("scripts/oracle/bz_pari_service.py",),
    "isabelle-bz": (
        "scripts/oracle/setup_bz_isabelle.sh",
        "scripts/oracle/bz-isabelle/",
    ),
    "isabelle-lll": (
        "scripts/oracle/setup_bz_lll_isabelle.sh",
        "scripts/oracle/bz-lll-isabelle/",
    ),
}

FACTOR_SYSTEMS = (
    "hex-factor", "flint", "ntl", "pari", "isabelle-bz", "isabelle-lll")


def factor_family(system: str) -> Family:
    """The source one comparator system's factorization curve depends on."""
    return Family(
        name=f"hexbz-factor-{system}",
        include=FACTOR_COMMON + FACTOR_SYSTEM_PATHS[system],
        exemptions=FACTOR_EXEMPTIONS,
        regenerate=(
            "scripts/bench/factor_sweep.py on the benchmarking host"),
    )


FAMILIES = {GRAPHISO.name: GRAPHISO} | {
    factor_family(system).name: factor_family(system)
    for system in FACTOR_SYSTEMS}


def main(argv: list[str]) -> int:
    """Print or record a family's fingerprint; regeneration scripts use this."""
    usage = ("usage: sweep_freshness.py (--fingerprint | --record | --paths)"
             " <family> [--ref REF]")
    if len(argv) < 2 or argv[0] not in ("--fingerprint", "--record", "--paths"):
        print(usage, file=sys.stderr)
        return 2
    mode, name, *rest = argv
    family = FAMILIES.get(name)
    if family is None:
        print(f"unknown family {name}; known: {', '.join(sorted(FAMILIES))}",
              file=sys.stderr)
        return 2
    if mode == "--paths":
        print(" ".join(family.staging_pathspec()))
        return 0
    ref = rest[1] if len(rest) == 2 and rest[0] == "--ref" else None
    listing = tree_listing(family, ref) if ref else index_listing(family)
    if mode == "--record":
        print(record(family, listing))
    else:
        print(fingerprint(listing))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
