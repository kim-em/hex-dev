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
# Expensive null control. Every probe here carries the same ~6.7 s `import all`
# executable closure, so the marginal elaboration cost has to be large before
# a module is a genuinely distinct build magnitude: the degree-16 binomial
# reaches only 1.37x the baseline, under the 2.0x the shared harness requires
# of its two controls. The degree-8 kernel replay is 2.48x, and it is also the
# only control that brackets the most expensive substantive arm (`kernel-8`
# itself), so the robust-null envelopes are interpolated rather than
# extrapolated.
KERNEL8 = ProbeModule(
    "HexBerlekampZassenhausMathlib.ProofProbe.Kernel8", EXPECTED_AXIOMS
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
            "kernel-8-null",
            KERNEL8,
            KERNEL8,
            {
                "family": "fresh-build-noise",
                "magnitude": "kernel-8",
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
    # Preregistered long-arm retry bound (`SPEC/benchmarking.md`: a suite with
    # preregistered long arms may explicitly request at most 32). These arms
    # run 6.65 s to 16.60 s, roughly 3x the sibling `HexBerlekampMathlib`
    # suite's, so each one spends proportionally longer exposed to a stray
    # scheduler tick on the pinned core or its SMT sibling and is rejected
    # correspondingly more often. Raising the retry bound buys more
    # clean-pair opportunities at the unchanged admission threshold; it is
    # the lever for a shared host that stays busy, and deliberately not the
    # interference ratio, which would instead admit dirtier arms.
    max_pair_retries=32,
)


if __name__ == "__main__":
    sys.exit(run_cli(SPEC, Path(__file__)))
