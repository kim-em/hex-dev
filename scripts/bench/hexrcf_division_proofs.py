#!/usr/bin/env python3
"""Fresh-module cost of wrapped versus direct fixed-field source conversion.

Question: after sharing the selected generator, does direct QAdjoin conversion
add proof cost over the convenience wrapper for the same cubic reciprocal?
Four adjacent alternating AB/BA rounds quote an ordinary-kernel rcf proof in
each arm with identical imports and source setup. This is a build-only probe,
not a numerical benchmark or a general algebraic-search scaling experiment.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
NAMESPACE = "Hex.RCF.ProofProbe.Division"

SPEC = SweepSpec(
    description=__doc__,
    pairs=(ProbePair(
        "cubic-source-conversion",
        ProbeModule("HexRCF.ProofProbe.Division.Wrapped", AXIOMS, NAMESPACE),
        ProbeModule("HexRCF.ProofProbe.Division.Direct", AXIOMS, NAMESPACE),
        {"component": "ordinary-kernel-cubic-reciprocal",
         "field_degree": 3, "source_coordinates": 2,
         "distinct_generators": 1, "target_degree": 1,
         "degree_kind": "source-syntax", "specialized_atom": "zero"},
    ),),
    probe_target="HexRCFProofProbe",
    schema="hex-rcf-division-proofs-v1",
    measurement="adjacent-source-conversion-olean-wall-v1",
    output_stem="hex-rcf-division-proofs",
    required_samples=4,
    retain_compiler_output=True,
    extra_sources=(Path("adapters/HexRCF/RealCoefficients/CommonTactic.lean"),
                   Path("adapters/HexRCF/RealCoefficients/FieldCompile.lean"),
                   Path("adapters/HexRCF/RealCoefficients/Field.lean")),
)

if __name__ == "__main__":
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
