#!/usr/bin/env python3
"""Fresh proof cost for close sections and a further algebraic root.

Question: how much ordinary-kernel proof construction does each observed
production case require? Both fresh modules use identical imports and the
complete fixed-field producer. Four adjacent alternating AB/BA rounds retain
all completed arms. These different formulas do not isolate a root-count or
precision scaling law, and this build-only probe is not a numerical benchmark.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
NAMESPACE = "Hex.RCF.ProofProbe.Production"

SPEC = SweepSpec(
    description=__doc__,
    pairs=(ProbePair(
        "ordinary-real-sections",
        ProbeModule("HexRCF.ProofProbe.Production.Close", AXIOMS, NAMESPACE),
        ProbeModule("HexRCF.ProofProbe.Production.Further", AXIOMS, NAMESPACE),
        {"component": "ordinary-kernel-fixed-field-production",
         "field_degree": 2, "source_coefficients": 1,
         "left_root_gap": "2^-132", "left_sections": 2,
         "right_sections": 4, "right_condition": "x^2=sqrt(2), 1<x<2",
         "comparison_kind": "different-formulas-not-causal-scaling"},
    ),),
    probe_target="HexRCFProofProbe",
    schema="hex-rcf-production-proofs-v1",
    measurement="adjacent-ordinary-real-production-olean-wall-v1",
    output_stem="hex-rcf-production-proofs",
    required_samples=4,
    retain_compiler_output=True,
    extra_sources=(Path("adapters/HexRCF/RealCoefficients/FieldSignProgress.lean"),
                   Path("adapters/HexRCF/RealCoefficients/FieldBuildProgress.lean"),
                   Path("adapters/HexRCF/RealCoefficients/FieldLiteral.lean")),
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
