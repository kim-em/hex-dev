#!/usr/bin/env python3
"""Source tactic costs for repeated and shared polynomial roots.

The baseline asks x^2 = sqrt(2) with 1 < x < 2. One candidate squares the
principal polynomial; another adds its product with x-1 as a redundant zero
condition. The targets differ and input polynomial degrees/atom counts change,
while the checked normalized carrier has the same four root sections. These
are two input comparisons, not a pure one-parameter complexity model or a
comparison between solvers. Four trial-major rounds rotate the two adjacent
pairs and alternate AB/BA, retaining every completed observation.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def probe(name: str) -> ProbeModule:
    return ProbeModule(f"HexRCF.ProofProbe.CommonRoots.{name}", AXIOMS,
                       f"Hex.RCF.ProofProbe.CommonRoots.{name}")


SPEC = SweepSpec(
    description=__doc__,
    pairs=(
        ProbePair("repeated", probe("Simple"), probe("Repeated"), {
            "changed_input": "square the principal zero polynomial",
            "reference_max_atom_degree": 2, "candidate_max_atom_degree": 4,
            "reference_atoms": 3, "candidate_atoms": 3,
            "reference_product_degree": 4, "candidate_product_degree": 6,
            "same_goal": False, "same_principal_zero_set": True,
            "field_degree": 2, "source_coefficients": 1,
            "checked_carrier_degree": 4, "root_sections": 4, "sectors": 5,
        }),
        ProbePair("shared", probe("Simple"), probe("Shared"), {
            "changed_input": "add a polynomial sharing existing roots",
            "reference_max_atom_degree": 2, "candidate_max_atom_degree": 3,
            "reference_atoms": 3, "candidate_atoms": 4,
            "reference_product_degree": 4, "candidate_product_degree": 7,
            "same_goal": False, "same_principal_zero_set": True,
            "field_degree": 2, "source_coefficients": 1,
            "checked_carrier_degree": 4, "root_sections": 4, "sectors": 5,
        }),
    ),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-common-root-proofs-v1",
    measurement="adjacent-source-common-repeated-root-olean-wall-v1",
    output_stem="hex-rcf-common-root-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
