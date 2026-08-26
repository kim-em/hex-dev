#!/usr/bin/env python3
"""Measure end-to-end ``factor_poly``/``irreducibility`` elaboration cost
for the integer-polynomial (Berlekamp-Zassenhaus) tactic surface.

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
BASELINE = ProbeModule("HexBerlekampZassenhausMathlib.ProofProbe.Baseline")
FACTOR8 = ProbeModule(
    "HexBerlekampZassenhausMathlib.ProofProbe.Factor8", EXPECTED_AXIOMS
)
IRREDUCIBLE16 = ProbeModule(
    "HexBerlekampZassenhausMathlib.ProofProbe.Irreducible16", EXPECTED_AXIOMS
)


def probe(
    name: str, module: str, family: str, degree: int, factors: int | None
) -> ProbePair:
    return ProbePair(
        name=name,
        reference=BASELINE,
        candidate=ProbeModule(module, EXPECTED_AXIOMS),
        metadata={
            "family": family,
            "degree": degree,
            "factors": factors,
        },
    )


SPEC = SweepSpec(
    description=__doc__ or "factor_poly fresh-module sweep",
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
            "irreducible-16-null",
            IRREDUCIBLE16,
            IRREDUCIBLE16,
            {
                "family": "fresh-build-noise",
                "magnitude": "irreducible-16",
                "interpretation": "calibration-only",
            },
            null_control=True,
        ),
        probe(
            "factor-4",
            "HexBerlekampZassenhausMathlib.ProofProbe.Factor4",
            "factor-distinct",
            4,
            2,
        ),
        probe(
            "factor-8",
            "HexBerlekampZassenhausMathlib.ProofProbe.Factor8",
            "factor-distinct",
            8,
            4,
        ),
        probe(
            "factor-12",
            "HexBerlekampZassenhausMathlib.ProofProbe.Factor12",
            "factor-distinct",
            12,
            6,
        ),
        probe(
            "irreducible-4",
            "HexBerlekampZassenhausMathlib.ProofProbe.Irreducible4",
            "irreducibility",
            4,
            None,
        ),
        probe(
            "irreducible-8",
            "HexBerlekampZassenhausMathlib.ProofProbe.Irreducible8",
            "irreducibility",
            8,
            None,
        ),
        probe(
            "irreducible-16",
            "HexBerlekampZassenhausMathlib.ProofProbe.Irreducible16",
            "irreducibility",
            16,
            None,
        ),
        probe(
            "kernel-4",
            "HexBerlekampZassenhausMathlib.ProofProbe.Kernel4",
            "kernel-fallback",
            4,
            None,
        ),
        probe(
            "kernel-8",
            "HexBerlekampZassenhausMathlib.ProofProbe.Kernel8",
            "kernel-fallback",
            8,
            None,
        ),
        ProbePair(
            "multiplicity-8",
            FACTOR8,
            ProbeModule(
                "HexBerlekampZassenhausMathlib.ProofProbe.Repeated8",
                EXPECTED_AXIOMS,
            ),
            {
                "family": "multiplicity-attribution",
                "degree": 8,
                "factors": 4,
            },
        ),
    ),
    probe_target="HexBerlekampZassenhausMathlibProofProbe",
    schema="hex-berlekamp-zassenhaus-mathlib-proof-probe-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    extra_sources=(
        Path("libraries.yml"),
        Path("PLAN/Phase4.md"),
        Path("SPEC/benchmarking.md"),
        Path(
            "HexBerlekampZassenhausMathlib/SPEC/"
            "hex-berlekamp-zassenhaus-mathlib.md"
        ),
    ),
    output_stem="hex-berlekamp-zassenhaus-mathlib",
    required_samples=6,
)


if __name__ == "__main__":
    sys.exit(run_cli(SPEC, Path(__file__)))
