#!/usr/bin/env python3
"""Measure bridge-owned ``Nat.Prime`` proof construction and tactic costs.

The typical and ceiling cases separate numeral construction, a committed
certificate literal, production certificate reification, bridge theorem plus
kernel replay, and the end-to-end ``primality`` tactic. Certificate search is
deliberately absent: it is the identical core computation and is linked from
the report's core-owned evidence. Threshold rows compare the opted-in trial
and certificate ``norm_num`` routes; the ceiling row covers the large
certificate-backed path.
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


PREFIX = "HexPrimalityMathlib.ProofProbe"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def probe(name: str, axioms: bool = False) -> ProbeModule:
    return ProbeModule(f"{PREFIX}.{name}", AXIOMS if axioms else None)


BASELINE = probe("Baseline")
INPUT31 = probe("Input31")
LITERAL31 = probe("Literal31")
INPUT512 = probe("Input512")
LITERAL512 = probe("Literal512")
REPLAY512 = probe("Replay512", True)


def pair(
    name: str,
    reference: ProbeModule,
    candidate: ProbeModule,
    component: str,
    bits: int,
    route: str,
) -> ProbePair:
    return ProbePair(
        name,
        reference,
        candidate,
        {
            "component": component,
            "bits": bits,
            "route": route,
            "fresh_module_budget_ms": 10_000,
        },
    )


SPEC = SweepSpec(
    description=__doc__ or "HexPrimalityMathlib proof sweep",
    pairs=(
        ProbePair(
            "import-null",
            BASELINE,
            BASELINE,
            {"component": "fresh-build-noise", "bits": 0},
            null_control=True,
        ),
        ProbePair(
            "replay-512-null",
            REPLAY512,
            REPLAY512,
            {"component": "fresh-build-noise", "bits": 512},
            null_control=True,
        ),
        pair("input-31", BASELINE, INPUT31, "input", 31, "shared"),
        pair("literal-31", INPUT31, LITERAL31, "certificate-literal", 31, "shared"),
        pair("reify-31", LITERAL31, probe("Reify31"), "reification", 31, "bridge"),
        pair("replay-31", LITERAL31, probe("Replay31", True), "kernel-replay", 31, "bridge"),
        pair("primality-31", BASELINE, probe("Primality31", True), "full-tactic", 31, "primality"),
        pair("input-512", BASELINE, INPUT512, "input", 512, "shared"),
        pair("literal-512", INPUT512, LITERAL512, "certificate-literal", 512, "shared"),
        pair("reify-512", LITERAL512, probe("Reify512"), "reification", 512, "bridge"),
        pair("replay-512", LITERAL512, REPLAY512, "kernel-replay", 512, "bridge"),
        pair("primality-512", BASELINE, probe("Primality512", True), "full-tactic", 512, "primality"),
        pair("norm-num-trial", BASELINE, probe("NormNumTrial", True), "full-tactic", 24, "norm-num-trial"),
        pair("norm-num-threshold", BASELINE, probe("NormNumThreshold", True), "full-tactic", 25, "norm-num-certificate"),
        pair("norm-num-512", BASELINE, probe("NormNum512", True), "full-tactic", 512, "norm-num-certificate"),
    ),
    probe_target="HexPrimalityMathlibProofProbe",
    schema="hex-primality-mathlib-proof-probes-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-primality-mathlib-proof-probes",
    extra_sources=(
        Path("HexPrimalityMathlib/NormNum.lean"),
        Path("HexPrimalityMathlib/Prime.lean"),
        Path("HexPrimalityMathlib/SPEC/hex-primality-mathlib.md"),
    ),
    required_samples=6,
    max_pair_retries=32,
    absolute_only=True,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
