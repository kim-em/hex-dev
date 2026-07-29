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
    name: str,
    hex_module: str,
    sorted_module: str,
    family: str,
    size: int,
    **axes: object,
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
            **axes,
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
            "addition-inputs-64",
            "HexAdditionInputs64",
            "SortedAdditionInputs64",
            "kernel-sparse-addition-construction",
            64,
            coefficient="Int",
            arity=[4, 8],
            comparator=["lex", "grevlex"],
            support="matched construction-only control",
            interpretation="construction-control",
        ),
        comparison(
            "addition-64",
            "HexAddition64",
            "SortedAddition64",
            "kernel-sparse-addition",
            64,
            coefficient="Int",
            arity=[4, 8],
            comparator=["lex", "grevlex"],
            support="separated, interleaved, and scattered",
            workload_control="addition-inputs-64",
            ratio_threshold=2.0,
        ),
        comparison(
            "multiplication-sparse-6",
            "HexMulSparse6",
            "SortedMulSparse6",
            "kernel-sparse-multiplication",
            6,
            coefficient="Int",
            arity=8,
            comparator="grlex",
            support="low-collision patterned multivariate",
        ),
        comparison(
            "multiplication-collide-inputs-12",
            "HexMulCollideInputs12",
            "SortedMulCollideInputs12",
            "kernel-multiplication-construction",
            12,
            coefficient="Rat",
            arity=8,
            comparator="grevlex",
            support="matched construction-only control",
            interpretation="construction-control",
        ),
        comparison(
            "multiplication-collide-12",
            "HexMulCollide12",
            "SortedMulCollide12",
            "kernel-sparse-multiplication",
            12,
            coefficient="Rat",
            arity=8,
            comparator="grevlex",
            support="high-collision single-axis",
            workload_control="multiplication-collide-inputs-12",
            ratio_threshold=2.0,
        ),
        comparison(
            "cancellation-4",
            "HexCancellation4",
            "SortedCancellation4",
            "kernel-cancellation-identities",
            4,
            coefficient=["Int", "Rat"],
            arity=4,
            comparator="lex",
            support="two-axis cancellation",
        ),
        comparison(
            "cancellation-6",
            "HexCancellation6",
            "SortedCancellation6",
            "kernel-cancellation-identities",
            6,
            coefficient=["Int", "Rat"],
            arity=4,
            comparator="lex",
            support="two-axis cancellation",
        ),
        comparison(
            "cancellation-inputs-10",
            "HexCancellationInputs10",
            "SortedCancellationInputs10",
            "kernel-cancellation-construction",
            10,
            coefficient=["Int", "Rat"],
            arity=4,
            comparator="lex",
            support="matched construction-only control",
            interpretation="construction-control",
        ),
        comparison(
            "cancellation-10",
            "HexCancellation10",
            "SortedCancellation10",
            "kernel-cancellation-identities",
            10,
            coefficient=["Int", "Rat"],
            arity=4,
            comparator="lex",
            support="two-axis cancellation",
            workload_control="cancellation-inputs-10",
            ratio_threshold=2.0,
        ),
        comparison(
            "sos-3",
            "HexSos3",
            "SortedSos3",
            "kernel-sos-certificates",
            3,
            coefficient="Int",
            arity=4,
            comparator="grevlex",
            support="three patterned polynomials",
        ),
        comparison(
            "sos-4",
            "HexSos4",
            "SortedSos4",
            "kernel-sos-certificates",
            4,
            coefficient="Int",
            arity=4,
            comparator="grevlex",
            support="three patterned polynomials",
        ),
        comparison(
            "sos-inputs-8",
            "HexSosInputs8",
            "SortedSosInputs8",
            "kernel-sos-construction",
            8,
            coefficient="Int",
            arity=4,
            comparator="grevlex",
            support="matched construction-only control",
            interpretation="construction-control",
        ),
        comparison(
            "sos-8",
            "HexSos8",
            "SortedSos8",
            "kernel-sos-certificates",
            8,
            coefficient="Int",
            arity=4,
            comparator="grevlex",
            support="three patterned polynomials",
            workload_control="sos-inputs-8",
            ratio_threshold=2.0,
        ),
        comparison(
            "structural-inputs-32",
            "HexStructuralInputs32",
            "SortedStructuralInputs32",
            "kernel-structural-construction",
            32,
            coefficient="Int",
            arity={"source": 4, "target": 2},
            comparator={"source": "grlex", "target": "grevlex"},
            support="matched construction-only control",
            interpretation="construction-control",
        ),
        comparison(
            "structural-32",
            "HexStructural32",
            "SortedStructural32",
            "kernel-structural-collisions",
            32,
            coefficient="Int",
            arity={"source": 4, "target": 2},
            comparator={"source": "grlex", "target": "grevlex"},
            support="rename/substitution collisions",
            workload_control="structural-inputs-32",
            ratio_threshold=2.0,
        ),
    ),
    probe_target="HexMvPolyMathlibProofProbe",
    schema="hex-mv-poly-kernel-proof-probes-v5",
    measurement=(
        "paired-fresh-module-olean-wall-import-construction-"
        "subtracted-ratio-bounded-v5"
    ),
    output_stem="hex-mv-poly-kernel",
    extra_sources=(
        Path("libraries.yml"),
        Path("SPEC/benchmarking.md"),
        Path("SPEC/Libraries/hex-mv-poly.md"),
    ),
    required_samples=6,
    max_pair_retries=32,
    import_baseline_control="fresh-build-null",
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
