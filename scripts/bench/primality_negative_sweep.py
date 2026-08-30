#!/usr/bin/env python3
"""Measure the opt-in ``Nat.Prime`` negative-result policy.

Each candidate is a fresh importing module paired with the same import-only
baseline.  The factor-found ladder spans the first certificate-tier width,
ordinary machine integers, balanced 41/42-bit factors, and the supported
512-bit ceiling.  The final pair records deterministic one-restart exhaustion
on a balanced 512-bit semiprime and must decline without trial division.
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


BASELINE = ProbeModule("HexPrimalityMathlib.ProofProbe.MathlibBaseline")
NEGATIVE_25 = ProbeModule("HexPrimalityMathlib.ProofProbe.Negative25")
NEGATIVE_64 = ProbeModule("HexPrimalityMathlib.ProofProbe.Negative64")
NEGATIVE_82 = ProbeModule("HexPrimalityMathlib.ProofProbe.Negative82")
NEGATIVE_512 = ProbeModule("HexPrimalityMathlib.ProofProbe.Negative512")
EXHAUSTED_512 = ProbeModule(
    "HexPrimalityMathlib.ProofProbe.NegativeExhausted512"
)


def negative_pair(
    name: str,
    candidate: ProbeModule,
    bits: int,
    outcome: str,
    factor_bits: tuple[int, int],
) -> ProbePair:
    return ProbePair(
        name,
        BASELINE,
        candidate,
        {
            "route": "opt-in-nat-prime-norm-num",
            "outcome": outcome,
            "bits": bits,
            "factor_bits": list(factor_bits),
            "rho_restarts": 1,
            "seed": "numeral",
            "fresh_module_budget_ms": 10_000,
        },
    )


SPEC = SweepSpec(
    description=__doc__ or "Nat.Prime negative-result policy sweep",
    pairs=(
        ProbePair(
            "negative-baseline-null",
            BASELINE,
            BASELINE,
            {"outcome": "calibration-only", "bits": 0},
            null_control=True,
        ),
        ProbePair(
            "negative-82-null",
            NEGATIVE_82,
            NEGATIVE_82,
            {"outcome": "calibration-only", "bits": 82},
            null_control=True,
        ),
        negative_pair("negative-25", NEGATIVE_25, 25, "factor-found", (7, 18)),
        negative_pair("negative-64", NEGATIVE_64, 64, "factor-found", (32, 32)),
        negative_pair("negative-82", NEGATIVE_82, 82, "factor-found", (41, 42)),
        negative_pair(
            "negative-512", NEGATIVE_512, 512, "factor-found", (3, 510)
        ),
        negative_pair(
            "negative-exhausted-512",
            EXHAUSTED_512,
            512,
            "exhausted",
            (256, 256),
        ),
    ),
    probe_target="HexPrimalityElabProbe",
    schema="hex-primality-negative-policy-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-primality-negative-policy",
    extra_sources=(
        Path("HexPrimalityMathlib/NormNum.lean"),
        Path("conformance/HexPrimalityMathlib/OptInConformance.lean"),
    ),
    required_samples=6,
    max_pair_retries=32,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
