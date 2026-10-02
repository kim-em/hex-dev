#!/usr/bin/env python3
"""Measure shared real-closed-field instance and odd-root theorem use."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli

SPEC = SweepSpec(
    description=__doc__,
    pairs=(ProbePair(
        "real-closed",
        ProbeModule("HexRealRootsMathlib.ProofProbe.RealClosedBaseline"),
        ProbeModule("HexRealRootsMathlib.ProofProbe.RealClosed",
                    ("propext", "Classical.choice", "Quot.sound")),
        {"component": "instance-and-odd-root", "interpretation": "ordinary-kernel-checking"},
    ),),
    probe_target="HexRealRootsMathlibReplayProbe",
    schema="hex-real-closed-proof-probe-v1",
    measurement="paired-fresh-module-olean-wall-v1",
    output_stem="hex-real-closed",
    extra_sources=(Path("HexRealRootsMathlib/RealClosed.lean"),
                   Path("HexRealAlgebraicMathlib/RealClosed.lean")),
    required_samples=4,
)

if __name__ == "__main__":
    sys.exit(run_cli(SPEC, Path(__file__)))
