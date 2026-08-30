#!/usr/bin/env python3
"""Measure the supported core and Mathlib ``primality`` policy routes.

Every substantive probe is paired with the matching import-only module. The
accepted probes exercise certificate search, compiled self-check, certificate
reification, and kernel replay at the exact 512-bit ceiling. A non-smooth
512-bit safe probable prime exercises bounded rho exhaustion at that same
ceiling. Rejection immediately above it must occur before search. No failure
route may fall through to a total decision.
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


CORE_BASELINE = ProbeModule("HexPrimality.ProofProbe.CoreBaseline")
PROOF_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
CORE_512 = ProbeModule("HexPrimality.ProofProbe.Core512", PROOF_AXIOMS)
MATHLIB_BASELINE = ProbeModule("HexPrimalityMathlib.ProofProbe.MathlibBaseline")
MATHLIB_512 = ProbeModule("HexPrimalityMathlib.ProofProbe.Mathlib512", PROOF_AXIOMS)


def policy_pair(
    name: str,
    route: str,
    outcome: str,
    reference: ProbeModule,
    candidate: ProbeModule,
    bits: int,
) -> ProbePair:
    return ProbePair(
        name,
        reference,
        candidate,
        {
            "route": route,
            "outcome": outcome,
            "bits": bits,
            "fresh_module_budget_ms": 10_000,
        },
    )


SPEC = SweepSpec(
    description=__doc__ or "primality elaborator policy sweep",
    pairs=(
        ProbePair(
            "core-baseline-null",
            CORE_BASELINE,
            CORE_BASELINE,
            {"route": "core", "outcome": "calibration-only", "bits": 0},
            null_control=True,
        ),
        ProbePair(
            "core-512-null",
            CORE_512,
            CORE_512,
            {"route": "core", "outcome": "calibration-only", "bits": 512},
            null_control=True,
        ),
        ProbePair(
            "mathlib-baseline-null",
            MATHLIB_BASELINE,
            MATHLIB_BASELINE,
            {"route": "mathlib", "outcome": "calibration-only", "bits": 0},
            null_control=True,
        ),
        policy_pair("core-512", "core", "accepted", CORE_BASELINE, CORE_512, 512),
        policy_pair(
            "mathlib-512", "mathlib", "accepted", MATHLIB_BASELINE, MATHLIB_512, 512
        ),
        policy_pair(
            "core-exhausted",
            "core",
            "exhausted",
            CORE_BASELINE,
            ProbeModule("HexPrimality.ProofProbe.CoreExhausted"),
            512,
        ),
        policy_pair(
            "mathlib-exhausted",
            "mathlib",
            "exhausted",
            MATHLIB_BASELINE,
            ProbeModule("HexPrimalityMathlib.ProofProbe.MathlibExhausted"),
            512,
        ),
        policy_pair(
            "core-over-budget",
            "core",
            "over-budget",
            CORE_BASELINE,
            ProbeModule("HexPrimality.ProofProbe.CoreOverBudget"),
            513,
        ),
        policy_pair(
            "mathlib-over-budget",
            "mathlib",
            "over-budget",
            MATHLIB_BASELINE,
            ProbeModule("HexPrimalityMathlib.ProofProbe.MathlibOverBudget"),
            513,
        ),
    ),
    probe_target="HexPrimalityElabProbe",
    schema="hex-primality-elaborator-policy-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-primality-elaborator-policy",
    extra_sources=(
        Path("HexPrimality/SPEC/hex-primality.md"),
        Path("bench/HexBench/PrimalityKernel.lean"),
        Path("bench/HexPrimality/Bench.lean"),
    ),
    required_samples=6,
    max_pair_retries=32,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
