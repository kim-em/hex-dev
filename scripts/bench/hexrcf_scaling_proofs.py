#!/usr/bin/env python3
"""Matched proof costs for three independent fixed-field input changes.

Question: how do polynomial degree, distinct atom count and integer coefficient
width change actual ordinary-kernel quotation cost on the same selected field?
Each pair changes one input dimension. All carriers have no real roots; this
isolates that regime and does not measure root separation or tower depth.
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
NAMESPACE = "Hex.RCF.ProofProbe.Scaling"


def probe(module: str) -> ProbeModule:
    return ProbeModule("HexRCF.ProofProbe.Scaling." + module, AXIOMS, NAMESPACE)


SPEC = SweepSpec(
    description=__doc__,
    pairs=(
        ProbePair("degree", probe("Degree2"), probe("Degree4"), {
            "changed_dimension": "maximum_variable_exponent",
            "reference_value": 2, "candidate_value": 4,
            "atoms": 1, "integer_coefficient_bits": 1,
            "selected_field_degree": 2, "source_coefficients": 1,
            "real_root_sections": 0,
        }),
        ProbePair("atoms", probe("Atoms1"), probe("Atoms4"), {
            "changed_dimension": "distinct_atoms",
            "reference_value": 1, "candidate_value": 4,
            "maximum_variable_exponent": 2, "integer_coefficient_bits": 2,
            "selected_field_degree": 2, "source_coefficients": 1,
            "real_root_sections": 0,
            "extra_atoms": "constant positive scalar multiples; carrier degree remains two",
        }),
        ProbePair("coefficient-width", probe("Bits32"), probe("Bits128"), {
            "changed_dimension": "integer_coefficient_bits",
            "reference_value": 32, "candidate_value": 128,
            "maximum_variable_exponent": 2, "atoms": 1,
            "selected_field_degree": 2, "source_coefficients": 1,
            "real_root_sections": 0,
        }),
    ),
    probe_target="HexRCFProofProbe",
    schema="hex-rcf-scaling-proofs-v1",
    measurement="adjacent-independent-input-olean-wall-v1",
    output_stem="hex-rcf-scaling-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
