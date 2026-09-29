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


def pair(depth: int, operation: str) -> ProbePair:
    fraction = operation in ("AcceptFraction", "RejectProduct", "FieldArithmetic", "Certificates")
    scalar = operation in ("FieldArithmetic", "Certificates")
    stem = prefix(depth)
    candidate = f"{stem}.{operation}"
    baseline = f"{stem}.{'FractionBaseline' if fraction else 'Baseline'}"
    scope = ("supplied fraction normalization checker proofs" if operation == "Certificates" else
             "fraction addition and division" if scalar else
             "actual forged chain guards and initial identity" if operation == "ArithmeticCause" else
             "early literal context rejection" if operation == "RejectStale" else
             "fresh-module proof of the actual graph checker result")
    has_graph = not scalar
    return ProbePair(
        f"depth-{depth}-{operation}", ProbeModule(baseline),
        ProbeModule(candidate, AXIOMS, f"Hex.SignDetMathlib.{candidate.split('.', 1)[1]}"),
        {"family": ("literal-fraction-normalization" if operation == "Certificates" else
                    "literal-fraction-field-arithmetic" if scalar else
                    "literal-fraction-replay" if fraction else
                    "literal-nested-coefficient-replay"),
         "extension_depth": depth, "operation": operation,
         "build_target": ("HexSignDetMathlibProofProbe" if depth < 3 else
                          "HexSignDetMathlibNestedProofProbe"),
         "degree": 1 if has_graph else None, "query_arity": 2 if has_graph else 0,
         "graph_nodes": 2 if has_graph else 0, "graph_edges": 2 if has_graph else 0,
         "distinct_leaf_references": 1 if has_graph else 0,
         "measurement_scope": scope,
         "excluded_costs": ["initial import build", "certificate production", "JSON parsing",
                            "native execution", "semantic theorem application",
                            "cross-level coefficient-sign proof DAG"]},
    )


PAIRS = tuple(pair(depth, operation) for depth in (1, 2, 3)
              for operation in ("Accept", "RejectArithmetic", "RejectStale", "ArithmeticCause")) + \
        tuple(pair(depth, operation) for depth in (1, 2)
              for operation in ("AcceptFraction", "RejectProduct", "FieldArithmetic", "Certificates"))
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
                   Path("scripts/bench/test_sign_det_nested_kernel.py"),
                   Path("HexPolyFast/Division.lean"), Path("HexPolyFast/HalfGcd.lean"),
                   Path("HexPolyFast/Karatsuba.lean"), Path("HexRationalFn/Normalize.lean"),
                   Path("scripts/bench/structural_tactic_sweep.py")),
)

def main() -> int:
    return run_retained_cli(SPEC, Path(__file__))

if __name__ == "__main__":
    raise SystemExit(main())
