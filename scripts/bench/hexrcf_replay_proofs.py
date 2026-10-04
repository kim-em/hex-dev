#!/usr/bin/env python3
"""Matched ordinary-kernel proof costs for combined certificate replay.

Both arms use the same imports, goal, solver, interval signs, coordinate
quotation, checker and soundness theorem. The reference splits the checker
conjunction; the candidate checks one Boolean replay goal. Source authentication
and the final handler proof check remain separate in both arms. This measures
fresh-module Lake build cost, not isolated kernel time or physical sharing.
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
NAMESPACE = "Hex.RCF.ProofProbe.Replay"


def pair(case: str) -> ProbePair:
    prefix = "HexRCF.ProofProbe.Replay." + case
    return ProbePair(
        case.lower(),
        ProbeModule(prefix + "Split", AXIOMS, NAMESPACE),
        ProbeModule(prefix + "Single", AXIOMS, NAMESPACE),
        {"changed_dimension": "certificate_replay",
         "reference_mode": "separately checked conjuncts",
         "candidate_mode": "one Boolean replay decision goal",
         "same_formula": True, "same_solver_and_checker": True},
    )


SPEC = SweepSpec(
    description=__doc__,
    pairs=tuple(pair(case) for case in ("Further", "Reciprocal", "Cubic")),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-replay-proofs-v1",
    measurement="adjacent-certificate-replay-olean-wall-v1",
    output_stem="hex-rcf-replay-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
