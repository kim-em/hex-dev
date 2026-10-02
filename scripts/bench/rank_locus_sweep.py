#!/usr/bin/env python3
"""Fresh-module rank-locus probes on the symbolic family, with r at most three.

Preregistered ceilings: 30 seconds per full proof build; 120 seconds for cleanup.
Each of eight cases has six retained adjacent AB/BA baseline/candidate pairs.
Comparator: no-comparable-surface-in-named-comparator.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli

PREFIX = "HexDeterminantalIdealMathlib.ProofProbe"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
CASES = (
    ("Full2R1", 2, 1, 1, 1, False, 1),
    ("Full2R2", 2, 2, 2, 4, False, 2),
    ("Low2R1", 2, 1, 1, 1, True, 1),
    ("Full4R3", 4, 1, 1, 1, False, 3),
    ("Low4R2", 4, 2, 1, 4, True, 2),
    ("Low4R3", 4, 2, 1, 4, True, 3),
    ("Full8R3", 8, 1, 1, 1, False, 3),
    ("Low8R3", 8, 1, 1, 1, True, 3),
)
SPEC = SweepSpec(
    description=__doc__ or "rank-locus proof probes",
    pairs=tuple(ProbePair(name, ProbeModule(f"{PREFIX}.Baseline"),
        ProbeModule(f"{PREFIX}.{name}", AXIOMS),
        {"family": "symbolic", "n": n, "variables": k, "degree": d,
         "support": s, "low": low, "threshold": r,
         "fresh_module_budget_ms": 30_000, "cleanup_timeout_seconds": 120})
        for name, n, k, d, s, low, r in CASES),
    probe_target="HexDeterminantalIdealMathlibProofProbe",
    schema="hex-determinantal-ideal-mathlib-probes-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-determinantal-ideal-mathlib-probes",
    extra_sources=(Path("bench/HexGenericRank/Bench.lean"),),
    required_samples=6,
    absolute_only=True,
    retain_compiler_output=True,
)

PHASES = ("batch", "enumeration", "enumeration kernel")


def compiler_metrics(module, sample):
    """Record the named Lean-profiler totals and emitted proof node counts."""
    if module.endswith(".Baseline"):
        return
    output = sample.get("compiler_output", "")
    metrics = {}
    for phase in PHASES:
        hits = re.findall(r"^\s*rank-locus " + phase + r" ([0-9.e+-]+)(ms|s)$",
                          output, re.MULTILINE)
        if len(hits) != 1:
            raise RuntimeError(f"{module}: expected one profiler total for {phase}")
        value, unit = hits[0]
        metrics[phase] = float(value) * (1 if unit == "ms" else 1000)
    nodes = re.findall(r"\[Hex.rankLocus\] proofNodes: (\d+)", output)
    if len(nodes) != 2:
        raise RuntimeError(f"{module}: expected iff and record proof-node traces")
    sample["phase_profile_ms"] = metrics
    sample["proof_nodes"] = int(nodes[-1])


if __name__ == "__main__":
    if "--timeout" not in sys.argv:
        sys.argv.extend(["--timeout", "120"])
    raise SystemExit(run_cli(SPEC, Path(__file__), sample_observer=compiler_metrics))
