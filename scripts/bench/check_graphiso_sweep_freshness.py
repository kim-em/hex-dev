#!/usr/bin/env python3
"""Fail when the hex-graph-iso cactus figures no longer cover their source.

The committed cactus sweep data under ``reports/bench-results/`` records
in its filename a content fingerprint of the source it measured
(``hexgraphiso-cactus-<hash12>-<host>.jsonl`` plus the matching
``hexgraphiso-pairs-...``): the hash of ``git ls-files -s`` over the
relevant paths, so it survives squash merges and rebases, which rewrite
commits but not content. The published figures in ``reports/figures/``
are rendered from that data. Whenever the current relevant source has no
matching sweep, the figures are stale: regenerate everything with
``scripts/bench/graphiso_cactus_sweep.sh`` and commit the new data and
figures together with the code change.

The relevant-source set is deliberately tight (the hex-graph-iso
implementation, its graph substrate, the sweep driver, and the plot
script) so unrelated pull requests never trip this check; a change to a
shared helper that measurably shifts these curves shows up in the
per-library benchmarks first.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "reports" / "bench-results"
FIGURES = ROOT / "reports" / "figures"

# Documentation under the library tree cannot affect measured performance,
# so the SPEC and README are excluded: a doc-only change must not force a
# multi-hour sweep. Keep this list identical to the pathspec in
# scripts/bench/graphiso_cactus_sweep.sh, or the recorded and checked
# fingerprints diverge.
RELEVANT = (
    "HexGraphIso/",
    "HexGraph/",
    "bench/HexGraphIso/Cactus.lean",
    "scripts/plots/hexgraphiso-cactus.py",
    ":!HexGraphIso/SPEC",
    ":!HexGraphIso/README.md",
)

SWEEP_RE = re.compile(r"^hexgraphiso-cactus-([0-9a-f]{12})-[^.]+\.jsonl$")

REQUIRED_FIGURES = (
    "hexgraphiso-canon-cactus.svg",
    "hexgraphiso-pairs-cactus.svg",
    "hexgraphiso-tactic-times.json",
)


def relevant_hash() -> str:
    """A content fingerprint of the relevant source, commit-independent."""
    listing = subprocess.run(
        ["git", "ls-files", "-s", "--", *RELEVANT],
        cwd=ROOT, text=True, capture_output=True, check=True).stdout
    return hashlib.sha256(listing.encode()).hexdigest()[:12]


def main() -> int:
    errors: list[str] = []
    current = relevant_hash()

    fresh = None
    for path in sorted(RESULTS.glob("hexgraphiso-cactus-*.jsonl")):
        match = SWEEP_RE.match(path.name)
        if match and match.group(1) == current:
            pairs = path.with_name(path.name.replace("-cactus-", "-pairs-"))
            if pairs.exists():
                fresh = path
            else:
                errors.append(
                    f"{pairs.name}: pairs data missing for {path.name}")

    if fresh is None and not errors:
        errors.append(
            f"no sweep data matches the current relevant source "
            f"(fingerprint {current}); the cactus figures are stale")

    for name in REQUIRED_FIGURES:
        if not (FIGURES / name).exists():
            errors.append(f"reports/figures/{name} is missing")

    if errors:
        print("hex-graph-iso cactus freshness check failed:")
        for error in errors:
            print(f"  - {error}")
        print("regenerate with scripts/bench/graphiso_cactus_sweep.sh and "
              "commit the data and figures with the code change")
        return 1
    print(f"hex-graph-iso cactus figures cover the current source "
          f"({fresh.name})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
