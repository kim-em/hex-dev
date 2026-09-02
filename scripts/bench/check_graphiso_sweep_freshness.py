#!/usr/bin/env python3
"""Fail when the hex-graph-iso cactus figures no longer cover their source.

The committed cactus sweep data under ``reports/bench-results/`` records
in its filename the commit it was measured at
(``hexgraphiso-cactus-<sha8>-<host>.jsonl`` plus the matching
``hexgraphiso-pairs-...``). The published figures in ``reports/figures/``
are rendered from that data. Whenever any source that changes what the
sweep measures differs from the recorded commit, the figures are stale:
regenerate everything with ``scripts/bench/graphiso_cactus_sweep.sh``
and commit the new data and figures together with the code change.

The relevant-source set is deliberately tight (the hex-graph-iso
implementation, its graph substrate, the sweep driver, and the plot
script) so unrelated pull requests never trip this check; a change to a
shared helper that measurably shifts these curves shows up in the
per-library benchmarks first.
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "reports" / "bench-results"
FIGURES = ROOT / "reports" / "figures"

RELEVANT = (
    "HexGraphIso/",
    "HexGraph/",
    "bench/HexGraphIso/Cactus.lean",
    "scripts/plots/hexgraphiso-cactus.py",
)

SWEEP_RE = re.compile(r"^hexgraphiso-cactus-([0-9a-f]{8,40})-[^.]+\.jsonl$")

REQUIRED_FIGURES = (
    "hexgraphiso-canon-cactus.svg",
    "hexgraphiso-pairs-cactus.svg",
    "hexgraphiso-tactic-times.json",
)


def git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=ROOT, text=True, capture_output=True, check=False)
    if result.returncode:
        raise SystemExit(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def main() -> int:
    errors: list[str] = []

    sweeps: list[tuple[int, str, Path]] = []
    for path in sorted(RESULTS.glob("hexgraphiso-cactus-*.jsonl")):
        match = SWEEP_RE.match(path.name)
        if not match:
            continue
        sha = match.group(1)
        probe = subprocess.run(
            ["git", "rev-parse", "--verify", f"{sha}^{{commit}}"],
            cwd=ROOT, text=True, capture_output=True, check=False)
        if probe.returncode:
            errors.append(f"{path.name}: recorded commit {sha} is unknown")
            continue
        commit = probe.stdout.strip()
        stamp = int(git("log", "-1", "--format=%ct", commit).strip())
        sweeps.append((stamp, commit, path))

    if not sweeps:
        errors.append(
            "no hexgraphiso-cactus-<sha8>-<host>.jsonl sweep data under "
            "reports/bench-results/")
    else:
        stamp, commit, path = max(sweeps)
        pairs = path.with_name(path.name.replace("-cactus-", "-pairs-"))
        if not pairs.exists():
            errors.append(f"{pairs.name}: pairs data missing for {path.name}")
        diff = git("diff", "--name-only", f"{commit}..HEAD", "--", *RELEVANT)
        if diff.strip():
            changed = ", ".join(diff.split())
            errors.append(
                f"cactus figures are stale: source differs from recorded "
                f"commit {commit[:12]}: {changed}")

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
    print("hex-graph-iso cactus figures cover the current source")
    return 0


if __name__ == "__main__":
    sys.exit(main())
