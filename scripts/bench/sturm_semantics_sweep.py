#!/usr/bin/env python3
"""Measure fresh applications of the proved Sturm–Tarski semantic bridge.

Pair the semantic replay module with its exact import-only baseline in
adjacent alternating AB/BA order. The module includes rational, noncanonical,
and integer/dyadic certificates and audits each result's kernel axioms.
This measures application of the imported foundation, not its initial build.
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_cli,
)

SPEC = SweepSpec(
    description=__doc__ or "Sturm–Tarski semantic replay proof sweep",
    pairs=(ProbePair(
        "semantics",
        ProbeModule("HexSturmMathlib.Replay.SemanticsBaseline"),
        ProbeModule("HexSturmMathlib.Replay.Semantics",
                    ("propext", "Classical.choice", "Quot.sound")),
        {"family": "literal-query-semantics", "degree": 2,
         "scope": "kernel replay and mathematical root-sum interpretation"},
    ),),
    probe_target="HexConformance",
    src_dir=Path("conformance"),
    schema="hex-sturm-mathlib-semantic-probes-v1",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-sturm-semantics",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    sys.exit(run_cli(SPEC, Path(__file__)))
