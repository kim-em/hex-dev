#!/usr/bin/env python3
"""Matched ordinary-kernel proof costs for literal interval sign evidence.

Each pair has the same imports, quantified goal, `PolyQuot.reduce` quotation
control, solver and checker. The reference quotes a full rational Sturm query
for every field sign; the candidate quotes exact Horner signs on the same
certified generator interval, retaining query evidence when inconclusive.
Both paths check the same count-one interval and exact keys/values. Production
uses the same interval-preferring builder; the reference reconstructs checked
Sturm entries during quotation. End-to-end fresh-module build times include
that assembly, elaboration and replay; they do not isolate kernel time.
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
NAMESPACE = "Hex.RCF.ProofProbe.Intervals"


def pair(case: str) -> ProbePair:
    prefix = "HexRCF.ProofProbe.Intervals." + case
    return ProbePair(
        case.lower(),
        ProbeModule(prefix + "Query", AXIOMS, NAMESPACE),
        ProbeModule(prefix + "Horner", AXIOMS, NAMESPACE),
        {"changed_dimension": "sign_evidence",
         "reference_mode": "full rational Sturm entries",
         "candidate_mode": "exact Horner signs with Sturm fallback",
         "same_formula": True, "same_solver_and_checker": True},
    )


SPEC = SweepSpec(
    description=__doc__,
    pairs=tuple(pair(case) for case in ("Further", "Reciprocal", "Cubic")),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-interval-proofs-v1",
    measurement="adjacent-interval-sign-olean-wall-v1",
    output_stem="hex-rcf-interval-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
