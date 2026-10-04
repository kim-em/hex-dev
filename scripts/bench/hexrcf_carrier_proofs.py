#!/usr/bin/env python3
"""Matched ordinary-kernel proof costs for monic carrier cores.

Both arms use the same imports, goal, coordinate quotation, interval signs and
split replay. The candidate normalizes the proposed derivative-gcd quotient
with the existing DensePoly.monicize operation. Both check the original
product, quotient and radical identities. Signed Sturm chains retain their
positive-scaling convention. This measures fresh-module Lake build cost,
including production and replay, not isolated gcd or kernel time.
Four trial-major adjacent alternating AB/BA rounds retain every completed arm.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
NAMESPACE = "Hex.RCF.ProofProbe.Carrier"


def pair(case: str) -> ProbePair:
    prefix = "HexRCF.ProofProbe.Carrier." + case
    return ProbePair(
        case.lower(),
        ProbeModule(prefix + "Raw", AXIOMS, NAMESPACE),
        ProbeModule(prefix + "Monic", AXIOMS, NAMESPACE),
        {"changed_dimension": "carrier_normalization",
         "reference_mode": "raw derivative-gcd quotient",
         "candidate_mode": "monic derivative-gcd quotient",
         "same_formula": True, "same_checker": True,
         "same_sign_evidence_and_replay": True},
    )


SPEC = SweepSpec(
    description=__doc__,
    pairs=tuple(pair(case) for case in ("Further", "Reciprocal", "Cubic")),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-carrier-proofs-v1",
    measurement="adjacent-carrier-normalization-olean-wall-v1",
    output_stem="hex-rcf-carrier-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
