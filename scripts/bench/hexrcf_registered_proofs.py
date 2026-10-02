#!/usr/bin/env python3
"""Fresh-module cost of four rcf proofs from caller-supplied coarse bounds.

Four adjacent AB/BA rounds compare matched imports with actual tactic proofs.
This answers the fixed integration cost question, not a complexity claim or
evidence of convergence of the constant providers.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

SPEC = SweepSpec(
    description=__doc__,
    pairs=(ProbePair(
        "registered-constants",
        ProbeModule("HexRCF.ProofProbe.Registered.Baseline"),
        ProbeModule("HexRCF.ProofProbe.Registered.Tactic",
                    ("propext", "Classical.choice", "Quot.sound"),
                    axiom_namespace="Hex.RCF.ProofProbe.Registered"),
        {"component": "four-ordinary-kernel-proofs",
         "request": "1/16", "pi_bounds": "[3,63/20]",
         "exp_bounds": "[27/10,14/5]"},
    ),),
    probe_target="HexRCFProofProbe",
    schema="hex-rcf-registered-proofs-v1",
    measurement="adjacent-matched-import-olean-wall-v1",
    output_stem="hex-rcf-registered-proofs",
    required_samples=4,
    retain_compiler_output=True,
    extra_sources=(Path("adapters/HexRCF/RealCoefficients/Finite.lean"),
                   Path("adapters/HexRCF/RealCoefficients/Registration.lean"),
                   Path("adapters/HexRCF/RealCoefficients/Reify.lean")),
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
