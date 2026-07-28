#!/usr/bin/env python3
"""Measure end-to-end ``isolate_roots`` elaboration and certificate replay.

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
BASELINE = ProbeModule("HexRealRootsMathlib.Baseline")


def probe(
    name: str, module: str, family: str, degree: int, width_bits: int | None
) -> ProbePair:
    return ProbePair(
        name=name,
        reference=BASELINE,
        candidate=ProbeModule(module, EXPECTED_AXIOMS),
        metadata={
            "family": family,
            "degree": degree,
            "width_bits": width_bits,
        },
    )


SPEC = SweepSpec(
    description=__doc__ or "isolate_roots fresh-module sweep",
    pairs=(
        probe(
            "natural-6",
            "HexRealRootsMathlib.Natural6",
            "natural-width",
            6,
            None,
        ),
        probe(
            "natural-8",
            "HexRealRootsMathlib.Natural8",
            "natural-width",
            8,
            None,
        ),
        probe(
            "natural-10",
            "HexRealRootsMathlib.Natural10",
            "natural-width",
            10,
            None,
        ),
        probe(
            "refined-2",
            "HexRealRootsMathlib.Refined2",
            "width-2^-20",
            2,
            20,
        ),
        probe(
            "refined-4",
            "HexRealRootsMathlib.Refined4",
            "width-2^-20",
            4,
            20,
        ),
        probe(
            "refined-6",
            "HexRealRootsMathlib.Refined6",
            "width-2^-20",
            6,
            20,
        ),
    ),
    probe_target="HexRealRootsMathlibReplayProbe",
    schema="hex-real-roots-mathlib-proof-probe-v1",
    measurement=(
        "fresh-module end-to-end elaboration, compiled certificate search, "
        "literal elaboration, and ordinary kernel checking"
    ),
    output_stem="hex-real-roots-mathlib",
)


if __name__ == "__main__":
    sys.exit(run_cli(SPEC, Path(__file__)))
