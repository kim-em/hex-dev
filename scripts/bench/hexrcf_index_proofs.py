#!/usr/bin/env python3
"""Matched ordinary-kernel proof costs for indexed finite sign retrieval.

Both arms use the same imports, goal, monic carrier, coordinate quotation,
interval evidence and split replay. The candidate freezes a balanced tree of
positions into the original checked sign entries. Bounds and exact keys are
checked at every hit; no independent cache signs are trusted. Checker equivalence
transports accepted indexed replay to the existing soundness theorem.
This measures fresh-module Lake cost, not isolated lookup or asymptotic scaling.
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
NAMESPACE = "Hex.RCF.ProofProbe.Index"


def pair(case: str) -> ProbePair:
    prefix = "HexRCF.ProofProbe.Index." + case
    return ProbePair(
        case.lower(),
        ProbeModule(prefix + "Linear", AXIOMS, NAMESPACE),
        ProbeModule(prefix + "Indexed", AXIOMS, NAMESPACE),
        {"changed_dimension": "finite_sign_retrieval",
         "reference_mode": "linear checked-entry lookup",
         "candidate_mode": "balanced positional checked-entry lookup",
         "same_formula": True, "checked_equivalence": True,
         "same_sign_evidence_and_replay": True},
    )


SPEC = SweepSpec(
    description=__doc__,
    pairs=tuple(pair(case) for case in ("Further", "Reciprocal", "Cubic")),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-index-proofs-v1",
    measurement="adjacent-finite-sign-retrieval-olean-wall-v1",
    output_stem="hex-rcf-index-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
