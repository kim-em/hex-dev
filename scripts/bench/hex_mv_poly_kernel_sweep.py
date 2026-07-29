#!/usr/bin/env python3
"""Measure HexMvPoly kernel reduction against the sorted-list probe adapter."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule,
    ProbePair,
    SweepSpec,
    run_cli,
)


EXPECTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
BASELINE = ProbeModule("HexMvPolyMathlib.ProofProbe.Baseline")


def module(name: str) -> ProbeModule:
    """A kernel-checked workload module with the expected standard axioms."""
    return ProbeModule(
        f"HexMvPolyMathlib.ProofProbe.{name}",
        EXPECTED_AXIOMS,
    )


def comparison(
    name: str, hex_module: str, sorted_module: str, family: str, size: int
) -> ProbePair:
    """One matched production-versus-sorted representation comparison."""
    return ProbePair(
        name=name,
        reference=module(hex_module),
        candidate=module(sorted_module),
        metadata={
            "family": family,
            "size": size,
            "reference_representation": "Hex ExtTreeMap",
            "candidate_representation": "sorted-list adapter",
        },
    )


SPEC = SweepSpec(
    description=__doc__ or "HexMvPoly kernel-reduction sweep",
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
            "cancellation-6-null",
            module("HexCancellation6"),
            module("HexCancellation6"),
            {
                "family": "fresh-build-noise",
                "magnitude": "cancellation-6",
                "interpretation": "calibration-only",
            },
            null_control=True,
        ),
        comparison(
            "cancellation-4",
            "HexCancellation4",
            "SortedCancellation4",
            "kernel-cancellation-identities",
            4,
        ),
        comparison(
            "cancellation-6",
            "HexCancellation6",
            "SortedCancellation6",
            "kernel-cancellation-identities",
            6,
        ),
        comparison(
            "sos-3",
            "HexSos3",
            "SortedSos3",
            "kernel-sos-certificates",
            3,
        ),
        comparison(
            "sos-4",
            "HexSos4",
            "SortedSos4",
            "kernel-sos-certificates",
            4,
        ),
        comparison(
            "structural-8",
            "HexStructural8",
            "SortedStructural8",
            "structural-collisions",
            8,
        ),
    ),
    probe_target="HexMvPolyMathlibProofProbe",
    schema="hex-mv-poly-kernel-proof-probes-v1",
    measurement="paired-fresh-module-olean-wall-v1",
    output_stem="hex-mv-poly-kernel",
    extra_sources=(
        Path("libraries.yml"),
        Path("SPEC/benchmarking.md"),
        Path("SPEC/Libraries/hex-mv-poly.md"),
    ),
    required_samples=6,
    max_pair_retries=32,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
