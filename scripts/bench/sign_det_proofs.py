#!/usr/bin/env python3
"""Matched fresh-module measurements of ordinary-kernel BKR graph replay.

Literal and replay modules are rebuilt adjacently in six rotated rounds.
Timeouts are operational; this suite declares no wall-time performance budget.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli
from scripts.bench.structural_tactic_sweep import acquire_cpu

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
PAIRS = tuple(
    ProbePair(
        name=f"depth-{depth}-{kind.lower()}",
        reference=ProbeModule(f"HexSignDetMathlib.ProofProbe.D{depth}.{literal}"),
        candidate=ProbeModule(f"HexSignDetMathlib.ProofProbe.D{depth}.{kind}", AXIOMS),
        metadata={"family": "same-level-graph", "outcome": kind.lower(),
                  "depth": depth, "query_arity": 2**depth,
                  "graph_nodes": depth + 1, "graph_edges": 2*depth,
                  "measurement_scope": "literal normalization plus ordinary-kernel replay",
                  "semantic_root_soundness": "foundation gate remains open"})
    for depth in (1, 3, 5, 7)
    for kind, literal in (("Accept", "Literal"), ("Reject", "BadLiteral")))

SPEC = SweepSpec(
    description=__doc__ or "BKR graph proof probes", pairs=PAIRS,
    probe_target="HexSignDetMathlibProofProbe",
    schema="hex-sign-det-graph-proofs-v1",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-sign-det-graph-proofs",
    required_samples=6, retain_compiler_output=True,
    extra_sources=(Path("libraries.yml"), Path("SPEC/benchmarking.md"),
                   Path("reports/sign-det-proof-model.md"),
                   Path("scripts/bench/structural_tactic_sweep.py")))


def main():
    cpu, lease = acquire_cpu()
    try:
        return run_cli(SPEC, Path(__file__),
                       [*sys.argv[1:], "--shared-host", "--cpu", str(cpu)])
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
