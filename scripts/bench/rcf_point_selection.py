#!/usr/bin/env python3
"""Compare selected-section and direct parent-point quotation of one root.

Both fresh modules have matched ordinary imports and prove x = sqrt(2) over
its already authenticated native parent. This tests the cost of proposing an
extra selected extension versus restoring a parent-field point. It is a
build-only proof probe, not a Mathlib-importing executable benchmark or a
comparison of general source discovery, nonlinear roots or cell completeness.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_retained_cli,
)

PREFIX = "HexRCF.ProofProbe.Points"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SPEC = SweepSpec(
    description=__doc__ or "RCF parent point quotation cost",
    pairs=(ProbePair(
        "selected-section-parent-point",
        ProbeModule(f"{PREFIX}.Section", AXIOMS,
                    "Hex.RCF.ProofProbe.Points.Section"),
        ProbeModule(f"{PREFIX}.Point", AXIOMS,
                    "Hex.RCF.ProofProbe.Points.Point"),
        {
            "question": "cost of an extra selected extension versus a parent-field point",
            "parent_degree": 2,
            "sentence_degree": 1,
            "atoms": 1,
            "coefficients": 1,
            "goal": "exists x : Real, x = Real.sqrt 2",
            "matched_imports": "same two conformance factories and ProofEvidence",
            "scope": "fixed parent, ordinary non-module fixture closure",
            "heartbeats": 20_000_000,
            "recursion_limit": 32768,
        },
    ),),
    probe_target="HexRCFProofProbeMeasurements",
    schema="hex-rcf-parent-point-proofs-v1",
    measurement="adjacent-alternating-fresh-module-build",
    output_stem="hex-rcf-parent-point-proofs",
    extra_sources=(
        Path("adapters/HexRCF/RealCoefficients/PointBuild.lean"),
        Path("adapters/HexRCF/RealCoefficients/PointReplay.lean"),
        Path("adapters/HexRCF/RealCoefficients/PointQuote.lean"),
        Path("conformance/HexRCF/PointProduceConformance.lean"),
        Path("conformance/HexRCF/SectionProduceConformance.lean"),
        Path("scripts/bench/cpu_lease.py"),
    ),
    required_samples=4,
    retain_compiler_output=True,
)


def check_imports() -> None:
    headers = []
    for arm in ("Section", "Point"):
        source = (ROOT / "bench/HexRCF/ProofProbe/Points" / f"{arm}.lean").read_bytes()
        header, separator, _body = source.partition(b"namespace Hex.RCF.ProofProbe.Points.")
        if not separator:
            raise ValueError(f"{arm}: missing namespace boundary")
        headers.append(header)
    if headers[0] != headers[1]:
        raise ValueError("point quotation probes have different import headers")


if __name__ == "__main__":
    check_imports()
    raise SystemExit(run_retained_cli(SPEC, Path(__file__)))
