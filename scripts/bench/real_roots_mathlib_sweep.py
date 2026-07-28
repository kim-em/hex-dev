#!/usr/bin/env python3
"""Measure end-to-end ``isolate_roots`` elaboration and certificate replay.

Every case is paired with the same import-only module. The shared harness
rebuilds the two modules adjacently, alternates their order, and retains both
raw measurements and the signed candidate-minus-reference delta.
"""

from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule,
    ProbePair,
    SweepSpec,
    run_cli,
)


EXPECTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
BASELINE = ProbeModule("HexRealRootsMathlib.ProofProbe.Baseline")
NATURAL6 = ProbeModule(
    "HexRealRootsMathlib.ProofProbe.Natural6", EXPECTED_AXIOMS
)
NATURAL10 = ProbeModule(
    "HexRealRootsMathlib.ProofProbe.Natural10", EXPECTED_AXIOMS
)


def probe(
    name: str, module: str, family: str, degree: int, width_bits: int | None
) -> ProbePair:
    return ProbePair(
        name=name,
        reference=BASELINE,
        candidate=ProbeModule(module, EXPECTED_AXIOMS),
        metadata={
            "family": family,
            "degree": degree,
            "width_bits": width_bits,
        },
    )


SPEC = SweepSpec(
    description=__doc__ or "isolate_roots fresh-module sweep",
    pairs=(
        ProbePair(
            "fresh-build-null",
            BASELINE,
            BASELINE,
            {
                "family": "fresh-build-noise",
                "magnitude": "baseline",
                "interpretation": "calibration-only",
            },
            null_control=True,
        ),
        ProbePair(
            "natural-10-null",
            NATURAL10,
            NATURAL10,
            {
                "family": "fresh-build-noise",
                "magnitude": "natural-10",
                "interpretation": "calibration-only",
            },
            null_control=True,
        ),
        probe(
            "natural-6",
            "HexRealRootsMathlib.ProofProbe.Natural6",
            "natural-width",
            6,
            None,
        ),
        probe(
            "natural-8",
            "HexRealRootsMathlib.ProofProbe.Natural8",
            "natural-width",
            8,
            None,
        ),
        probe(
            "natural-10",
            "HexRealRootsMathlib.ProofProbe.Natural10",
            "natural-width",
            10,
            None,
        ),
        probe(
            "refined-2",
            "HexRealRootsMathlib.ProofProbe.Refined2",
            "width-2^-20",
            2,
            20,
        ),
        probe(
            "refined-4",
            "HexRealRootsMathlib.ProofProbe.Refined4",
            "width-2^-20",
            4,
            20,
        ),
        probe(
            "refined-6",
            "HexRealRootsMathlib.ProofProbe.Refined6",
            "width-2^-20",
            6,
            20,
        ),
        ProbePair(
            "refine-6",
            NATURAL6,
            ProbeModule(
                "HexRealRootsMathlib.ProofProbe.Refined6",
                EXPECTED_AXIOMS,
            ),
            {
                "family": "refinement-attribution",
                "degree": 6,
                "width_bits": 20,
            },
        ),
    ),
    probe_target="HexRealRootsMathlibReplayProbe",
    schema="hex-real-roots-mathlib-proof-probe-v2",
    measurement="paired-fresh-module-olean-wall-v1",
    extra_sources=(
        Path("libraries.yml"),
        Path("PLAN/Phase4.md"),
        Path("SPEC/benchmarking.md"),
        Path("HexRealRootsMathlib/SPEC/hex-real-roots-mathlib.md"),
    ),
    output_stem="hex-real-roots-mathlib",
    required_samples=6,
)


if __name__ == "__main__":
    sys.exit(run_cli(SPEC, Path(__file__)))
