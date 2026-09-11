#!/usr/bin/env python3
"""Measure the `rank` tactic against Mathlib's `eval_rank` on shared literals.

Each family is one closed integer matrix literal proved twice in fresh
modules: by `eval_rank` (reference arm, importing only
`Mathlib.Tactic.NormRank`) and by `rank` (candidate arm, importing
`HexRankMathlib`). Both arms are paired against their own import-only
baseline, so a pair's delta is the cost of the proof itself: elaboration,
certificate construction and the kernel check. The comparator ratio of a
family is the Mathlib delta over the Hex delta.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule,
    ProbePair,
    SweepSpec,
    run_cli,
)

PREFIX = "HexRankMathlib.ProofProbe"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def probe(name: str, axioms: bool = False) -> ProbeModule:
    return ProbeModule(f"{PREFIX}.{name}", AXIOMS if axioms else None)


BASELINE = probe("Baseline")
MATHLIB_BASELINE = probe("MathlibBaseline")

FAMILIES = (
    ("dense-8", "Dense8", 8, 8),
    ("dense-16", "Dense16", 16, 16),
    ("deficient-16", "Deficient16", 16, 14),
    ("dense-32", "Dense32", 32, 32),
    ("low-rank-32", "LowRank32", 32, 2),
)


def pairs() -> tuple[ProbePair, ...]:
    out = [
        ProbePair("import-null", BASELINE, BASELINE,
                  {"component": "fresh-build-noise", "n": 0, "rank": 0}, null_control=True),
        ProbePair("mathlib-import-null", MATHLIB_BASELINE, MATHLIB_BASELINE,
                  {"component": "fresh-build-noise", "n": 0, "rank": 0}, null_control=True),
    ]
    for family, module, n, rank in FAMILIES:
        out.append(ProbePair(
            f"{family}-eval-rank", MATHLIB_BASELINE, probe(f"{module}Mathlib", True),
            {"component": "full-tactic", "family": family, "n": n, "rank": rank,
             "route": "eval_rank", "fresh_module_budget_ms": 60_000}))
        out.append(ProbePair(
            f"{family}-rank", BASELINE, probe(f"{module}Hex", True),
            {"component": "full-tactic", "family": family, "n": n, "rank": rank,
             "route": "rank", "fresh_module_budget_ms": 60_000}))
    return tuple(out)


SPEC = SweepSpec(
    description=__doc__ or "HexRankMathlib rank tactic sweep",
    pairs=pairs(),
    probe_target="HexRankMathlibProofProbe",
    schema="hex-rank-mathlib-tactic-probes-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-rank-mathlib-tactic-probes",
    extra_sources=(
        Path("HexRank/Kernel.lean"),
        Path("HexRankMathlib/Kernel.lean"),
        Path("HexRankMathlib/Tactic.lean"),
    ),
    required_samples=6,
    absolute_only=True,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
