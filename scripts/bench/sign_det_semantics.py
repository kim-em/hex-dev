#!/usr/bin/env python3
"""Diagnostic fresh-module costs of interpreting checked BKR graphs as root counts.

An import-only baseline and a semantic theorem application use identical warm
imports. Four rotated rounds alternate adjacent AB/BA order. This is neither
the initial foundation build nor reduction of the certificate checker.
"""
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SPEC = SweepSpec(
    description=__doc__ or "BKR semantic proof diagnostics",
    pairs=tuple(ProbePair(
        f"depth-{depth}",
        ProbeModule(f"HexSignDetMathlib.ProofProbe.D{depth}.SemanticBaseline", None,
                    f"Hex.SignDetMathlib.ProofProbe.D{depth}.SemanticBaseline"),
        ProbeModule(f"HexSignDetMathlib.ProofProbe.D{depth}.Semantic", AXIOMS,
                    f"Hex.SignDetMathlib.ProofProbe.D{depth}.Semantic"),
        {"family": "same-level-graph-semantics", "depth": depth,
         "query_arity": 2**depth, "graph_nodes": depth + 1,
         "graph_edges": 2*depth, "degree": 2, "support_size": 1,
         "coefficient_extension_depth": 0,
         "measurement_scope": "application of root-count semantics to a warm accepted graph",
         "excluded_costs": ["literal checker reduction", "initial foundation build",
                            "compiled execution", "nested coefficient arithmetic"]},
    ) for depth in (1, 3, 5, 7)),
    probe_target="HexSignDetMathlibProofProbe",
    schema="hex-sign-det-semantic-probes-v2",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-sign-det-semantics",
    required_samples=4,
    retain_compiler_output=True,
    extra_sources=(Path("libraries.yml"), Path("SPEC/benchmarking.md"),
                   Path("reports/sign-det-semantic-probes.md"),
                   Path("scripts/bench/structural_tactic_sweep.py"),
                   Path("scripts/bench/test_sign_det_semantics.py")),
)


def main() -> int:
    return run_retained_cli(SPEC, Path(__file__))

if __name__ == "__main__":
    raise SystemExit(main())
