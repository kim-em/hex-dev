#!/usr/bin/env python3
"""Fresh-module ordinary-kernel replay over one to three rational-function fields.

Six trial-major rounds rotate adjacent import-baseline/proof pairs and alternate
AB/BA order. Every completed arm is retained, including failures. These are
finite input observations, not an asymptotic or pure-kernel timing claim.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (
    ProbeModule, ProbePair, SweepSpec, default_output, environment, parse_args,
    run_cli, source_hashes,
)
from scripts.bench.structural_tactic_sweep import acquire_cpu

AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def prefix(depth: int) -> str:
    return (f"HexSignDetMathlib.ProofProbe.Nested.N{depth}" if depth < 3 else
            "HexSignDetMathlib.NestedProofProbe.N3")


PAIRS = tuple(
    ProbePair(
        f"depth-{depth}-{operation}",
        ProbeModule(f"{prefix(depth)}.Baseline"),
        ProbeModule(f"{prefix(depth)}.{operation}", AXIOMS,
                    f"Hex.SignDetMathlib.{prefix(depth).split('.', 1)[1]}.{operation}"),
        {"family": "literal-nested-coefficient-replay", "extension_depth": depth,
         "operation": operation, "degree": 1, "query_arity": 2,
         "graph_nodes": 2, "graph_edges": 2, "distinct_leaf_references": 1,
         "measurement_scope": "fresh-module proof of the actual graph checker result",
         "excluded_costs": ["initial import build", "certificate production",
                            "JSON parsing", "native execution", "semantic theorem application",
                            "cross-level coefficient-sign proof DAG"]},
    ) for depth in (1, 2, 3) for operation in ("Accept", "RejectArithmetic")
) + (ProbePair(
    "depth-1-RejectStale",
    ProbeModule(f"{prefix(1)}.Baseline"),
    ProbeModule(f"{prefix(1)}.RejectStale", AXIOMS,
                "Hex.SignDetMathlib.ProofProbe.Nested.N1.RejectStale"),
    {"family": "literal-nested-coefficient-replay", "extension_depth": 1,
     "operation": "RejectStale", "measurement_scope": "early literal context rejection"},
),)
SPEC = SweepSpec(
    description=__doc__ or "Nested coefficient kernel replay costs",
    pairs=PAIRS,
    probe_target="HexSignDetMathlibNestedProofProbe",
    schema="hex-sign-det-nested-kernel-v1",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-sign-det-nested-kernel",
    required_samples=6,
    retain_compiler_output=True,
    extra_sources=(Path("libraries.yml"), Path("SPEC/benchmarking.md"),
                   Path("HexPolyFast/Division.lean"), Path("HexPolyFast/HalfGcd.lean"),
                   Path("HexPolyFast/Karatsuba.lean"), Path("HexRationalFn/Normalize.lean"),
                   Path("scripts/bench/structural_tactic_sweep.py")),
)

def main() -> int:
    args = parse_args(SPEC.description, default_samples=SPEC.required_samples or 4)
    cpu, lease = acquire_cpu(args.cpu)
    try:
        env = environment()
        output = args.output or (Path.home() / ".local/state/hex/proof-probes" /
                                 default_output(env, SPEC.output_stem).name)
        output = output.resolve()
        if output.is_relative_to(ROOT.resolve()):
            raise RuntimeError("choose a measurement output path outside the repository")
        sidecar = Path(str(output) + ".samples.jsonl")
        if output.exists() or sidecar.exists():
            raise RuntimeError("measurement output exists; choose a fresh path")
        # Flush every completed arm before validation, including failed arms.
        sidecar.parent.mkdir(parents=True, exist_ok=True)
        with sidecar.open("x") as log:
            print(f"Incremental samples: {sidecar}", flush=True)
            log.write(json.dumps({"type": "metadata", "environment": env,
                                  "source_sha256": source_hashes(SPEC, Path(__file__))}) + "\n")
            log.flush()

            def observe(module, sample):
                log.write(json.dumps({"type": "sample", "module": module, **sample}) + "\n")
                log.flush()

            try:
                code = run_cli(SPEC, Path(__file__),
                               [*sys.argv[1:], "--shared-host", "--cpu", str(cpu),
                                "--output", str(output)], sample_observer=observe)
                log.write(json.dumps({"type": "complete", "code": code}) + "\n")
                log.flush()
            except BaseException as exc:
                log.write(json.dumps({"type": "failure", "exception": type(exc).__name__,
                                      "error": str(exc)}) + "\n")
                log.flush()
                print(f"Retained partial samples: {sidecar}", file=sys.stderr)
                raise
        return code
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
