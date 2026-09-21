#!/usr/bin/env python3
"""Measure literal Tarski replay and domain interpretation in fresh kernel builds.

Each candidate is paired with its import-only baseline in adjacent alternating
AB/BA order. This measures checker/domain proofs, not missing root-sum semantics
or nested extension certificates. No performance budget or phase completion is
asserted by these probes.
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
BASELINE = ProbeModule("HexSturmMathlib.ProofProbe.Baseline")
SPEC = SweepSpec(
    description=__doc__ or "Tarski literal replay proof sweep",
    pairs=tuple(
        ProbePair(name.lower(), BASELINE,
                  ProbeModule("HexSturmMathlib.ProofProbe." + name, AXIOMS),
                  {"family": "literal-rational-query", "degree": 2,
                   "scope": "checker and domain; no root-sum theorem"})
        for name in ("Accepted", "Rejected")
    ),
    probe_target="HexSturmMathlibReplayProbe",
    schema="hex-sturm-mathlib-literal-probes-v1",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-sturm-mathlib",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    sys.exit(run_cli(SPEC, Path(__file__)))
