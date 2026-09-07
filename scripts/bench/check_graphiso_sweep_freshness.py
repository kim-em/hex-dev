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

The family declares no exemption channel, so any runtime-relevant difference
has to be re-measured. The check itself verifies two exceptions: a ``.lean``
path whose two blobs are equal once their comments are removed, and a lakefile
edit outside the declarations that build the cactus executable. Neither relies
on a persistent assertion that can go stale.
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
LAKEFILE = "lakefile.lean"

GRAPHISO_LIBRARIES = {"Hex", "HexBasic", "HexGraph", "HexGraphIso"}
GRAPHISO_EXECUTABLE = "hexgraphiso_cactus"
GRAPHISO_EXTERN_LIBRARY = "hexnautyffi"
GRAPHISO_BUILD_DEFS = {"nautyVendorOTarget", "nautyCanonOTarget"}


def graphiso_blocks(text: str) -> dict[str, str]:
    """The lakefile declarations that can affect the cactus executable."""
    relevant = {}
    for name, body in freshness.lakefile_blocks(text).items():
        kind, _, declaration = name.partition(" ")
        if kind in ("package", "require"):
            relevant[name] = body
        elif kind == "lean_lib" and declaration in GRAPHISO_LIBRARIES:
            relevant[name] = body
        elif kind == "lean_exe" and declaration == GRAPHISO_EXECUTABLE:
            relevant[name] = body
        elif kind == "extern_lib" and declaration == GRAPHISO_EXTERN_LIBRARY:
            relevant[name] = body
        elif kind == "def" and declaration in GRAPHISO_BUILD_DEFS:
            relevant[name] = body
    return relevant


def lakefile_texts_differ(before: str, after: str) -> bool:
    """Whether a lakefile edit changes the cactus executable's build."""
    old_blocks = graphiso_blocks(before)
    new_blocks = graphiso_blocks(after)
    if set(old_blocks) != set(new_blocks):
        return True
    return any(new_blocks[name] != body for name, body in old_blocks.items())


def build_only_lakefile_edit(difference: freshness.Difference) -> bool:
    """A lakefile transition outside the cactus executable's build graph."""
    if difference.path != LAKEFILE:
        return False
    if difference.baseline is None or difference.current is None:
        return False
    return not lakefile_texts_differ(
        freshness.blob_text(difference.baseline),
        freshness.blob_text(difference.current))


def runtime_neutral_edit(difference: freshness.Difference) -> bool:
    """A source edit mechanically known not to change either cactus curve."""
    return (freshness.lean_comment_only(difference)
            or build_only_lakefile_edit(difference))


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
    verdict = freshness.assess(FAMILY, found, allow=runtime_neutral_edit)
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
