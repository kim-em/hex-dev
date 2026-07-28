#!/usr/bin/env python3
"""Run the matched fresh-module HexRCF tactic proof probes."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (
    ProbeModule,
    ProbePair,
    SweepSpec,
    run_cli,
)


ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
BASELINE = ProbeModule("HexRCF.ProofProbe.Baseline")


def case_pairs(case: str, module_case: str, budget_ms: int) -> tuple[ProbePair, ...]:
    """The five preregistered deltas for one fixed source/reflected case."""
    prefix = f"HexRCF.ProofProbe.{module_case}"
    input_module = ProbeModule(f"{prefix}.Input")
    literal_module = ProbeModule(f"{prefix}.Literal")
    common = {"case": case, "tactic_budget_ms": budget_ms}
    return (
        ProbePair(
            f"{case}-reify",
            BASELINE,
            ProbeModule(f"{prefix}.Reify"),
            {**common, "component": "reification"},
        ),
        ProbePair(
            f"{case}-search",
            input_module,
            ProbeModule(f"{prefix}.Search"),
            {**common, "component": "compiled-search-attribution"},
        ),
        ProbePair(
            f"{case}-literal",
            input_module,
            literal_module,
            {**common, "component": "literal-elaboration"},
        ),
        ProbePair(
            f"{case}-replay",
            literal_module,
            ProbeModule(f"{prefix}.Replay", ALLOWED_AXIOMS),
            {**common, "component": "kernel-replay"},
        ),
        ProbePair(
            f"{case}-tactic",
            BASELINE,
            ProbeModule(f"{prefix}.Tactic", ALLOWED_AXIOMS),
            {**common, "component": "end-to-end-tactic"},
        ),
    )


SPEC = SweepSpec(
    description=__doc__ or "HexRCF fresh-module proof probes",
    pairs=(
        ProbePair(
            "fresh-build-null",
            BASELINE,
            BASELINE,
            {
                "component": "fresh-build-noise",
                "interpretation": "calibration-only",
                "magnitude": "baseline",
            },
            null_control=True,
        ),
        ProbePair(
            "degree50-tactic-null",
            ProbeModule("HexRCF.ProofProbe.Degree50.Tactic", ALLOWED_AXIOMS),
            ProbeModule("HexRCF.ProofProbe.Degree50.Tactic", ALLOWED_AXIOMS),
            {
                "component": "fresh-build-noise",
                "interpretation": "calibration-only",
                "magnitude": "degree50-tactic",
            },
            null_control=True,
        ),
        *case_pairs("quadratic", "Quadratic", 100),
        *case_pairs("degree10", "Degree10", 1_000),
        *case_pairs("degree50", "Degree50", 30_000),
    ),
    probe_target="HexRCFProofProbe",
    schema="hexrcf-proof-probes-v2",
    measurement="paired-fresh-module-olean-wall-v1",
    output_stem="hexrcf-proof-probes",
    extra_sources=(
        Path("libraries.yml"),
        Path("PLAN/Phase4.md"),
        Path("SPEC/benchmarking.md"),
        Path("SPEC/Libraries/hex-rcf.md"),
    ),
    required_samples=6,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
