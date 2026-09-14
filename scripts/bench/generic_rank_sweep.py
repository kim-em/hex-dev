#!/usr/bin/env python3
"""Fresh-module symbolic rank probes, with separate polynomial-identity timings.

Preregistered ceilings: 30 seconds per full proof build; 120 seconds for
cleanup. Each case is paired with its import-only baseline, six retained
AB/BA rounds. There is no symbolic eval_rank comparator surface.
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli

PREFIX = "HexGenericRankMathlib.ProofProbe"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
MODULES = ('VariableGeneric', 'VariableHypothesis', 'VariableSideGoal', 'QuadraticGeneric', 'QuadraticHypothesis', 'QuadraticSideGoal', 'Full2Generic', 'Full2Hypothesis', 'Full2SideGoal', 'Low2Generic', 'Low2Hypothesis', 'Low2SideGoal', 'FiniteHypothesis', 'FiniteSideGoal')
# FiniteGeneric is a documented non-test until #10257 provides the residue list form.
SPEC = SweepSpec(
    description=__doc__ or "symbolic rank proof probes",
    pairs=tuple(ProbePair(name, ProbeModule(f"{PREFIX}.Baseline"),
        ProbeModule(f"{PREFIX}.{name}", AXIOMS),
        {"component": "symbolic-rank", "fresh_module_budget_ms": 30_000,
         "cleanup_timeout_seconds": 120}) for name in MODULES),
    probe_target="HexGenericRankMathlibProofProbe",
    schema="hex-generic-rank-mathlib-probes-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-generic-rank-mathlib-probes",
    extra_sources=tuple(Path(p) for p in (
        "HexGenericRank/Basic.lean", "HexGenericRankMathlib/Transport.lean",
        "HexGenericRankMathlib/Sound.lean", "HexGenericRankMathlib/Kernel.lean",
        "HexGenericRankMathlib/Reify.lean", "HexGenericRankMathlib/Modular.lean",
        "HexGenericRankMathlib/Provider.lean", "HexGenericRankMathlib/Tactic.lean")),
    required_samples=6,
    absolute_only=True,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    if "--timeout" not in sys.argv:
        sys.argv.extend(["--timeout", "120"])
    raise SystemExit(run_cli(SPEC, Path(__file__)))
