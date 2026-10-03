#!/usr/bin/env python3
"""Matched fixed-field proof costs at eight and sixty-four generator bits.

Question: how does a tighter initial square affect full-query evidence and whole
proof cost for the same positive square root and sentence? Both roots are proved
to equal sqrt(2). The high-precision proof transports back to the exact same goal.
Refinement is disabled; all other quotation/checker modes and imports match.
The shared selected-root identity lemmas are warmed dependencies, not timed setup.
This does not measure automatic common-field reconstruction or nested depth.
Four adjacent alternating AB/BA rounds retain every completed arm.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
NAMESPACE = "Hex.RCF.ProofProbe.Precision"

SPEC = SweepSpec(
    description=__doc__,
    pairs=(ProbePair(
        "generator-precision",
        ProbeModule("HexRCF.ProofProbe.Precision.Bits8", AXIOMS, NAMESPACE),
        ProbeModule("HexRCF.ProofProbe.Precision.Bits64", AXIOMS, NAMESPACE),
        {"changed_dimension": "initial_generator_square_precision",
         "reference_bits": 8, "candidate_bits": 64,
         "same_goal": True, "same_selected_real_root": "positive sqrt(2)",
         "field_degree": 2, "maximum_variable_exponent": 2,
         "source_atoms": 3, "source_coefficients": 1,
         "generator_refinement_steps": 0,
         "candidate_transport": "checked selected-root sentence equivalence",
         "shared_authentication_lemmas_warmed": True},
    ),),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-precision-proofs-v1",
    measurement="adjacent-initial-generator-precision-olean-wall-v1",
    output_stem="hex-rcf-precision-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
