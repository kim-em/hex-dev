#!/usr/bin/env python3
"""Measure HexIntFactor checkFactorization kernel replay for k = 1..10."""

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


BASELINE = ProbeModule("HexIntFactor.ProofProbe.Baseline")


def replay(count: int) -> ProbeModule:
    return ProbeModule(f"HexIntFactor.ProofProbe.Replay{count}", ("propext",))


def replay_pair(count: int) -> ProbePair:
    return ProbePair(
        f"replay-{count}",
        BASELINE,
        replay(count),
        {
            "family": "checkFactorization-kernel-replay",
            "factor_count": count,
            "largest_factor_bits": 61 if count == 10 else 5,
            "fresh_module_budget_ms": 5000,
        },
    )


SPEC = SweepSpec(
    description=__doc__ or "HexIntFactor kernel replay sweep",
    pairs=(
        ProbePair(
            "fresh-build-null",
            BASELINE,
            BASELINE,
            {"family": "fresh-build-noise", "magnitude": "baseline"},
            null_control=True,
        ),
        ProbePair(
            "replay-10-null",
            replay(10),
            replay(10),
            {"family": "fresh-build-noise", "magnitude": "replay-10"},
            null_control=True,
        ),
        *(replay_pair(count) for count in range(1, 11)),
    ),
    probe_target="HexIntFactorKernelProbe",
    schema="hex-int-factor-kernel-replay-v1",
    measurement="rotated-paired-fresh-module-olean-wall-absolute-v1",
    output_stem="hex-int-factor-kernel-replay",
    extra_sources=(
        Path("HexIntFactor/SPEC/hex-int-factor.md"),
        Path("SPEC/benchmarking.md"),
    ),
    required_samples=6,
    max_pair_retries=32,
    absolute_only=True,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
