#!/usr/bin/env python3
"""Fresh-module ordinary-kernel replay over one to three rational-function fields.

Six trial-major rounds rotate adjacent import-baseline/proof pairs and alternate
AB/BA order. Every completed arm is retained, including failures. These are
finite input observations, not an asymptotic or pure-kernel timing claim.
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


def prefix(depth: int) -> str:
    return (f"HexSignDetMathlib.ProofProbe.Nested.N{depth}" if depth < 3 else
            "HexSignDetMathlib.NestedProofProbe.N3")


PAIRS = tuple(
    ProbePair(
        f"depth-{depth}-{operation}",
        ProbeModule(f"{prefix(depth)}.Baseline"),
        ProbeModule(f"{prefix(depth)}.{operation}", AXIOMS,
                    f"Hex.SignDetMathlib.{prefix(depth).split('.', 1)[1]}.{operation}"),
        {"family": "literal-nested-coefficient-replay", "extension_depth": depth,
         "operation": operation,
         "build_target": ("HexSignDetMathlibProofProbe" if depth < 3 else
                          "HexSignDetMathlibNestedProofProbe"), "degree": 1, "query_arity": 2,
         "graph_nodes": 2, "graph_edges": 2, "distinct_leaf_references": 1,
         "measurement_scope": "fresh-module proof of the actual graph checker result",
         "excluded_costs": ["initial import build", "certificate production",
                            "JSON parsing", "native execution", "semantic theorem application",
                            "cross-level coefficient-sign proof DAG"]},
    ) for depth in (1, 2, 3) for operation in ("Accept", "RejectArithmetic")
) + (ProbePair(
    "depth-1-RejectStale",
    ProbeModule(f"{prefix(1)}.Baseline"),
    ProbeModule(f"{prefix(1)}.RejectStale", AXIOMS,
                "Hex.SignDetMathlib.ProofProbe.Nested.N1.RejectStale"),
    {"family": "literal-nested-coefficient-replay", "extension_depth": 1,
     "operation": "RejectStale", "degree": 1, "query_arity": 2,
     "graph_nodes": 2, "graph_edges": 2, "distinct_leaf_references": 1,
     "build_target": "HexSignDetMathlibProofProbe",
     "measurement_scope": "early literal context rejection",
     "excluded_costs": ["initial import build", "certificate production", "JSON parsing",
                        "native execution", "semantic theorem application",
                        "cross-level coefficient-sign proof DAG"]},
),)
SPEC = SweepSpec(
    description=__doc__ or "Nested coefficient kernel replay costs",
    pairs=PAIRS,
    probe_target="HexSignDetMathlibProofProbe",
    schema="hex-sign-det-nested-kernel-v2",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-sign-det-nested-kernel",
    required_samples=6,
    retain_compiler_output=True,
    extra_sources=(Path("libraries.yml"), Path("SPEC/benchmarking.md"),
                   Path("reports/sign-det-nested-kernel.md"),
                   Path("HexPolyFast/Division.lean"), Path("HexPolyFast/HalfGcd.lean"),
                   Path("HexPolyFast/Karatsuba.lean"), Path("HexRationalFn/Normalize.lean"),
                   Path("scripts/bench/structural_tactic_sweep.py")),
)

def main() -> int:
    return run_retained_cli(SPEC, Path(__file__))

if __name__ == "__main__":
    raise SystemExit(main())
