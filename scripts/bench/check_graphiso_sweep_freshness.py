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

The relevant-source set is deliberately tight (the hex-graph-iso
implementation, its graph substrate, the sweep driver, and the plot
script), so unrelated pull requests never trip this check and
re-measuring is the cheap answer rather than writing an exemption; a
change to a shared helper that measurably shifts these curves shows up in
the per-library benchmarks first. It is declared, with the shared
mechanism, in ``scripts/bench/sweep_freshness.py``.

The family declares no exemption channel, so any difference has to be
re-measured, with one exception the check verifies for itself: a ``.lean``
path whose two blobs are equal once their comments are removed
(``lean_comment_only``). Prose under the library tree is edited often
enough, and cannot move a curve, that making every docstring cost a sweep
would either stop the prose being written or make regeneration routine
enough to stop meaning anything.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.bench import sweep_freshness as freshness  # noqa: E402

FAMILY = freshness.GRAPHISO
RESULTS = freshness.RESULTS

SWEEP_RE = re.compile(r"^hexgraphiso-cactus-([0-9a-f]{12})-[^.]+\.jsonl$")


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


def main() -> int:
    found, errors = observations()
    verdict = freshness.assess(FAMILY, found,
                               allow=freshness.lean_comment_only)
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
