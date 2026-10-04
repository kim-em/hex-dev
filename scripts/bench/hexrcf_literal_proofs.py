#!/usr/bin/env python3
"""Matched ordinary-kernel proof costs for reduced-coordinate quotation.

Each pair has the same imports and quantified goal. Only the quotation control
changes: PolyQuot.reduce versus a constructor with a checked degree bound.
Both arms retain the same solver, literal replay and soundness theorem. Four
trial-major alternating AB/BA rounds retain every completed build. This measures
fresh-module build cost, including elaboration and replay, not isolated kernel
time or the other optimizations proposed in issues #10633 and #10634.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
NAMESPACE = "Hex.RCF.ProofProbe.Literals"


def pair(case: str) -> ProbePair:
    prefix = "HexRCF.ProofProbe.Literals." + case
    return ProbePair(
        case.lower(),
        ProbeModule(prefix + "Legacy", AXIOMS, NAMESPACE),
        ProbeModule(prefix + "Reduced", AXIOMS, NAMESPACE),
        {"changed_dimension": "literal_quotation",
         "reference_mode": "PolyQuot.reduce",
         "candidate_mode": "PolyQuot.mk with ordinary-kernel degree evidence",
         "same_formula": True, "same_solver_and_checker": True},
    )


SPEC = SweepSpec(
    description=__doc__,
    pairs=tuple(pair(case) for case in ("Further", "Reciprocal", "Cubic")),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-literal-proofs-v1",
    measurement="adjacent-literal-quotation-olean-wall-v1",
    output_stem="hex-rcf-literal-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
