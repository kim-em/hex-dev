#!/usr/bin/env python3
"""Fresh-module symbolic rank probes, with separate polynomial-identity timings.

Preregistered ceilings: 30 seconds per full proof build; 120 seconds for
cleanup. Each case is paired with its import-only baseline, six retained
AB/BA rounds. There is no symbolic eval_rank comparator surface.
"""
from __future__ import annotations

import json
import re
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

PHASES = ("batch", "producer", "header kernel", "pivot kernel", "upper kernel")


def compiler_metrics(module, sample):
    """Retain named Lean-profiler phases alongside each external wall sample."""
    if module.endswith(".Baseline"):
        return
    output = sample.get("compiler_output", "")
    metrics = {}
    for phase in PHASES:
        hits = re.findall(r"^\s*generic-rank " + phase + r" ([0-9.e+-]+)(ms|s)$",
                          output, re.MULTILINE)
        if len(hits) != 1:
            raise RuntimeError(f"{module}: expected one profiler total for {phase}")
        value, unit = hits[0]
        metrics[phase] = float(value) * (1 if unit == "ms" else 1000)
    traces = [json.loads(line[line.index("{"):]) for line in output.splitlines()
              if "[Hex.genericRank]" in line]
    if len(traces) != 1:
        raise RuntimeError(f"{module}: expected one provider trace")
    sample["phase_profile_ms"] = metrics
    sample["proof_nodes"] = traces[0]["proofNodes"]


if __name__ == "__main__":
    if "--timeout" not in sys.argv:
        sys.argv.extend(["--timeout", "120"])
    raise SystemExit(run_cli(SPEC, Path(__file__), sample_observer=compiler_metrics))
