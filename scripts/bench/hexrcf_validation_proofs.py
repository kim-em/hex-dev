#!/usr/bin/env python3
"""Matched fresh-module costs of redundant fresh-input validation.

Both arms prove identical goals with matching imports and solver options.
The reference revalidates the just-built environment using the public boundary.
The candidate uses private factory assembly and the mandatory dispatcher kernel
check. Editable public inputs always retain full validation. Four trial-major
rounds alternate adjacent AB/BA arms; all completed samples are retained.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
NAMESPACE = "Hex.RCF.ProofProbe.Validation"

def pair(case: str) -> ProbePair:
    prefix = "HexRCF.ProofProbe.Validation." + case
    return ProbePair(case.lower(),
        ProbeModule(prefix + "Checked", AXIOMS, NAMESPACE),
        ProbeModule(prefix + "Fresh", AXIOMS, NAMESPACE),
        {"changed_dimension": "fresh_input_validation",
         "reference_mode": "repeat full prepared environment validation",
         "candidate_mode": "private factory assembly and dispatcher checking",
         "same_formula": True, "same_imports_solver_and_replay": True,
         "required_route": "CommonPresentation.checkPolynomials_sound in quoted proof"})

SPEC = SweepSpec(description=__doc__, pairs=tuple(pair(x) for x in ("Scalar", "Several")),
    probe_target="HexRCFProofProfile", schema="hex-rcf-validation-proofs-v2",
    measurement="adjacent-fresh-input-validation-olean-wall-v1",
    output_stem="hex-rcf-validation-proofs", required_samples=4,
    retain_compiler_output=True)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
