#!/usr/bin/env python3
"""Matched ordinary-kernel proof costs for checked generator-window refinement.

The arms differ only in a zero versus four-step producer refinement budget.
Both preserve original root bindings and freeze contained count-one windows;
replay checks the same selected root without performing root refinement.
The fixed-field case starts at eight bits and needs full queries before
refinement. The three source examples test whether their existing windows
already suffice. These are whole fresh-module costs, not isolated sign timings.
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
NAMESPACE = "Hex.RCF.ProofProbe.Windows"


def pair(case: str) -> ProbePair:
    prefix = "HexRCF.ProofProbe.Windows." + case
    return ProbePair(
        case.lower(),
        ProbeModule(prefix + "Original", AXIOMS, NAMESPACE),
        ProbeModule(prefix + "Refined", AXIOMS, NAMESPACE),
        {"changed_dimension": "generator_window_budget",
         "reference_mode": "zero refinement steps",
         "candidate_mode": "four checked refinement steps",
         "same_formula": True, "original_root_binding_preserved": True,
         "same_checker_and_lookup": True},
    )


SPEC = SweepSpec(
    description=__doc__,
    pairs=tuple(pair(case) for case in ("Fixed", "Further", "Reciprocal", "Cubic")),
    probe_target="HexRCFProofProfile",
    schema="hex-rcf-window-proofs-v1",
    measurement="adjacent-generator-window-olean-wall-v1",
    output_stem="hex-rcf-window-proofs",
    required_samples=4,
    retain_compiler_output=True,
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
