#!/usr/bin/env python3
"""Measure the opt-in ``Nat.Prime`` negative-result policy.

Each candidate is a fresh importing module paired with the same import-only
baseline.  The factor-found ladder spans the first certificate-tier width, a
32-bit strong pseudoprime, the balanced 64-bit restart boundary, and the
supported 512-bit ceiling's parity preflight.  The exhaustion rows cover the
first zero-restart width and a balanced 512-bit semiprime; both must decline
without trial division.
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
NEGATIVE_32 = ProbeModule("HexPrimalityMathlib.ProofProbe.Negative32")
NEGATIVE_64 = ProbeModule("HexPrimalityMathlib.ProofProbe.Negative64")
NEGATIVE_64_NULL = ProbeModule("HexPrimalityMathlib.ProofProbe.Negative64Null")
EXHAUSTED_65 = ProbeModule("HexPrimalityMathlib.ProofProbe.NegativeExhausted65")
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
    rho_restarts: int,
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
            "rho_restarts": rho_restarts,
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
            "negative-64-null",
            NEGATIVE_64_NULL,
            NEGATIVE_64_NULL,
            {"outcome": "calibration-only", "bits": 64},
            null_control=True,
        ),
        negative_pair(
            "negative-25", NEGATIVE_25, 25, "factor-found", (7, 18), 1
        ),
        negative_pair(
            "negative-32", NEGATIVE_32, 32, "factor-found", (8, 25), 1
        ),
        negative_pair(
            "negative-64", NEGATIVE_64, 64, "factor-found", (32, 32), 1
        ),
        negative_pair(
            "negative-exhausted-65",
            EXHAUSTED_65,
            65,
            "exhausted",
            (19, 46),
            0,
        ),
        negative_pair(
            "negative-512", NEGATIVE_512, 512, "parity-factor-found", (2, 511), 0
        ),
        negative_pair(
            "negative-exhausted-512",
            EXHAUSTED_512,
            512,
            "exhausted",
            (256, 256),
            0,
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
