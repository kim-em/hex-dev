#!/usr/bin/env python3
"""Fresh-module kernel replay of literal rational-function certificates."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (  # noqa: E402
    ProbeModule, ProbePair, SweepSpec, run_cli,
)

BASELINE = ProbeModule("HexRationalFn.ProofProbe.Baseline")
AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def probe(name):
    return ProbeModule(f"HexRationalFn.ProofProbe.{name}", AXIOMS)


SPEC = SweepSpec(
    description=__doc__,
    pairs=(
        ProbePair("import-null", BASELINE, BASELINE,
                  {"family": "fresh-build-noise", "magnitude": "import"},
                  null_control=True),
        ProbePair("replay-null", probe("Replay64"), probe("Replay64"),
                  {"family": "fresh-build-noise", "magnitude": "replay-64"},
                  null_control=True),
        *(ProbePair(f"replay-{n}", BASELINE, probe(f"Replay{n}"),
                    {"family": "certificate-kernel-replay", "witness_degree": n + 1,
                     "fresh_module_budget_ms": 5000}) for n in (4, 16, 64)),
        ProbePair("reject-64", BASELINE, probe("Reject64"),
                  {"family": "certificate-kernel-rejection", "witness_degree": 65,
                   "fresh_module_budget_ms": 5000}),
    ),
    probe_target="HexRationalFnKernelProbe",
    schema="hex-rational-fn-kernel-replay-v1",
    measurement="rotated-paired-fresh-module-olean-wall-absolute-v1",
    output_stem="hex-rational-fn-kernel-replay",
    extra_sources=(Path("HexRationalFn/SPEC/hex-rational-fn.md"),
                   Path("SPEC/benchmarking.md")),
    required_samples=6,
    max_pair_retries=32,
    absolute_only=True,
)


if __name__ == "__main__":
    raise SystemExit(run_cli(SPEC, Path(__file__)))
