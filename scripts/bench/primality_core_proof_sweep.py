#!/usr/bin/env python3
"""Run the matched fresh-module HexPrimality core proof probes."""

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
BASELINE = ProbeModule("HexPrimality.ProofProbe.CoreBaseline")
FRESH_MODULE_BUDGET_MS = 10_000


def case_pairs(bits: int) -> tuple[ProbePair, ...]:
    """The five preregistered fresh-module costs for one prime."""
    prefix = f"HexPrimality.ProofProbe.Bit{bits}"
    input_module = ProbeModule(f"{prefix}.Input")
    literal_module = ProbeModule(f"{prefix}.Literal")
    common = {
        "bits": bits,
        "fresh_module_budget_ms": FRESH_MODULE_BUDGET_MS,
        "budget_kind": "absolute-regression-bound",
    }
    return (
        ProbePair(
            f"bit{bits}-input",
            BASELINE,
            input_module,
            {**common, "component": "input-construction"},
        ),
        ProbePair(
            f"bit{bits}-search",
            input_module,
            ProbeModule(f"{prefix}.Search"),
            {**common, "component": "compiled-search-attribution"},
        ),
        ProbePair(
            f"bit{bits}-literal",
            input_module,
            literal_module,
            {**common, "component": "emitted-certificate-literal"},
        ),
        ProbePair(
            f"bit{bits}-replay",
            literal_module,
            ProbeModule(f"{prefix}.Replay", ALLOWED_AXIOMS),
            {**common, "component": "kernel-replay"},
        ),
        ProbePair(
            f"bit{bits}-tactic",
            BASELINE,
            ProbeModule(f"{prefix}.Tactic", ALLOWED_AXIOMS),
            {**common, "component": "full-core-primality"},
        ),
    )


SPEC = SweepSpec(
    description=__doc__ or "HexPrimality core fresh-module proof probes",
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
            "bit123-tactic-null",
            ProbeModule("HexPrimality.ProofProbe.Bit123.Tactic", ALLOWED_AXIOMS),
            ProbeModule("HexPrimality.ProofProbe.Bit123.Tactic", ALLOWED_AXIOMS),
            {
                "component": "fresh-build-noise",
                "interpretation": "calibration-only",
                "magnitude": "bit123-tactic",
            },
            null_control=True,
        ),
        ProbePair(
            "bit512-tactic-null",
            ProbeModule("HexPrimality.ProofProbe.Bit512.Tactic", ALLOWED_AXIOMS),
            ProbeModule("HexPrimality.ProofProbe.Bit512.Tactic", ALLOWED_AXIOMS),
            {
                "component": "fresh-build-noise",
                "interpretation": "calibration-only",
                "magnitude": "bit512-tactic",
            },
            null_control=True,
        ),
        *case_pairs(31),
        *case_pairs(61),
        *case_pairs(123),
        *case_pairs(256),
        *case_pairs(511),
        *case_pairs(512),
    ),
    probe_target="HexPrimalityElabProbe",
    schema="hexprimality-core-proof-probes-v1",
    measurement="paired-fresh-module-olean-wall-absolute-v1",
    output_stem="hexprimality-core-proof-probes",
    extra_sources=(
        Path("libraries.yml"),
        Path("PLAN/Phase4.md"),
        Path("SPEC/benchmarking.md"),
        Path("HexPrimality/SPEC/hex-primality.md"),
    ),
    required_samples=6,
    max_pair_retries=32,
    absolute_only=True,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
