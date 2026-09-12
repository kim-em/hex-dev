#!/usr/bin/env python3
"""Measure the `det` tactic against Mathlib's `eval_det` on shared literals.

Each family is one closed matrix literal proved twice in fresh modules: by
`eval_det` (reference arm, importing only `Mathlib.Tactic.NormDet`) and by
`det` (candidate arm, importing `HexBareissMathlib`). Both arms are paired
against their own import-only baseline, so a pair's delta is an absolute
estimate of the cost of that proof: literal elaboration, certificate
construction and the kernel check. The two arms of a family are separate
estimates; the ratio of their medians is reported as the family's
comparator ratio, and is only as resolved as the smaller of the two deltas.
The probes are written by `scripts/bench/det_tactic_probes.py`; the
`dense-32` family has no `eval_det` arm, which does not finish within the
budget.
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

PREFIX = "HexBareissMathlib.ProofProbe"
AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def probe(name: str, axioms: bool = False) -> ProbeModule:
    return ProbeModule(f"{PREFIX}.{name}", AXIOMS if axioms else None)


BASELINE = probe("Baseline")
MATHLIB_BASELINE = probe("MathlibBaseline")

# family, module stem, dimension, whether `eval_det` has an arm
FAMILIES = (
    ("dense-8", "Dense8", 8, True),
    ("dense-12", "Dense12", 12, True),
    ("dense-16", "Dense16", 16, True),
    ("dense-32", "Dense32", 32, False),
    ("tridiagonal-16", "Tridiagonal16", 16, True),
    ("vandermonde-8", "Vandermonde8", 8, True),
    ("singular-16", "Singular16", 16, True),
    ("large-8-64", "Large8Bits64", 8, True),
    ("large-4-256", "Large4Bits256", 4, True),
    ("rational-8", "Rational8", 8, True),
)


def pairs() -> tuple[ProbePair, ...]:
    out: list[ProbePair] = []
    for family, module, n, mathlib in FAMILIES:
        if mathlib:
            out.append(ProbePair(
                f"{family}-eval-det", MATHLIB_BASELINE, probe(f"{module}Mathlib", True),
                {"component": "full-tactic", "family": family, "n": n,
                 "route": "eval_det", "fresh_module_budget_ms": 120_000}))
        out.append(ProbePair(
            f"{family}-det", BASELINE, probe(f"{module}Hex", True),
            {"component": "full-tactic", "family": family, "n": n,
             "route": "det", "fresh_module_budget_ms": 120_000}))
    return tuple(out)


SPEC = SweepSpec(
    description=__doc__ or "HexBareissMathlib det tactic sweep",
    pairs=pairs(),
    probe_target="HexBareissMathlibProofProbe",
    schema="hex-bareiss-mathlib-tactic-probes-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-bareiss-mathlib-tactic-probes",
    extra_sources=(
        Path("HexBareiss/Kernel.lean"),
        Path("HexBareissMathlib/Kernel.lean"),
        Path("HexBareissMathlib/Tactic.lean"),
        Path("HexMatrixMathlib/Literal.lean"),
    ),
    required_samples=6,
    absolute_only=True,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
