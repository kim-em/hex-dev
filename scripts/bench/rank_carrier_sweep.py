#!/usr/bin/env python3
"""Compare rank and eval_rank on rational and quadratic matrix literals."""

from pathlib import Path
import fcntl
import os
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import ProbeModule, ProbePair, SweepSpec, run_cli

PREFIX = "HexRankMathlib.ProofProbe."
AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def pairs() -> tuple[ProbePair, ...]:
    result = []
    for carrier in ("Rational", "Quadratic"):
        for size, n, rank in (("8", 8, 8), ("Deficient16", 16, 14)):
            family = f"{carrier.lower()}-{n}-rank-{rank}"
            for arm, route in (("Mathlib", "eval_rank"), ("Hex", "rank")):
                baseline = "MathlibBaseline" if arm == "Mathlib" else "Baseline"
                if carrier == "Quadratic":
                    baseline = "Quadratic" + baseline
                result.append(ProbePair(
                    f"{family}-{route}", ProbeModule(PREFIX + baseline),
                    ProbeModule(PREFIX + carrier + size + arm, AXIOMS),
                    {"family": family, "carrier": carrier, "n": n, "rank": rank,
                     "route": route, "fresh_module_budget_ms": 60_000},
                ))
    result.append(ProbePair(
        "closed-algebraic-8-rank-8", ProbeModule(PREFIX + "NumberFieldBaseline"),
        ProbeModule(PREFIX + "Algebraic8Hex", AXIOMS),
        {"family": "closed-algebraic", "carrier": "PolyQuot", "n": 8, "rank": 8,
         "route": "rank", "fresh_module_budget_ms": 60_000},
    ))
    return tuple(result)


SPEC = SweepSpec(
    description=__doc__ or "", pairs=pairs(), probe_target="HexRankMathlibProofProbe",
    schema="hex-rank-mathlib-carrier-probes-v1",
    measurement="paired-fresh-module-olean-wall-robust-null-v2",
    output_stem="hex-rank-mathlib-carrier-probes",
    extra_sources=tuple(Path(p) for p in (
        "HexRank/Polynomial.lean", "HexRank/PolyProduce.lean", "HexRank/Kernel.lean",
        "HexMatrixMathlib/Literal.lean", "HexBareiss/Kernel.lean",
        "HexRankMathlib/Rational.lean", "HexRankMathlib/Polynomial.lean",
        "HexRankMathlib/Quotient.lean", "HexRankMathlib/Quadratic.lean",
        "HexRankMathlib/NumberField.lean", "HexRankMathlib/NumberFieldTactic.lean",
        "HexRankMathlib/PolyExpr.lean",
        "HexPolyZ/IntegerPolynomial.lean", "HexNumberField/Basic.lean",
        "HexNumberFieldMathlib/AdjoinRoot.lean", "HexRankMathlib/Kernel.lean",
        "HexRankMathlib/Tactic.lean", "HexRankMathlib/QuadraticTactic.lean",
    )),
    required_samples=6, absolute_only=True,
)

if __name__ == "__main__":
    # Share the placement lease used by other Hex carrier measurements.
    # No host-idleness test or waiting is involved.
    lease = None
    if "--shared-host" in sys.argv and not any(
        arg == "--cpu" or arg.startswith("--cpu=") for arg in sys.argv
    ):
        cpus = sorted(os.sched_getaffinity(0))
        offset = os.getpid() % len(cpus)
        for cpu in cpus[offset:] + cpus[:offset]:
            lease = open(f"/tmp/hex-bench-cpu-{cpu}.lock", "a")
            try:
                fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
                sys.argv.extend(["--cpu", str(cpu)])
                break
            except BlockingIOError:
                lease.close()
        else:
            raise RuntimeError("all measurement CPU leases are held")
    try:
        raise SystemExit(run_cli(SPEC, Path(__file__)))
    finally:
        if lease is not None:
            lease.close()

