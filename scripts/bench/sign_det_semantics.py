#!/usr/bin/env python3
"""Diagnostic fresh-module costs of interpreting checked BKR graphs as root counts.

An import-only baseline and a semantic theorem application use identical warm
imports. Four rotated rounds alternate adjacent AB/BA order. This is neither
the initial foundation build nor reduction of the certificate checker.
"""
from __future__ import annotations

import json
from pathlib import Path
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.fresh_module_sweep import (
    ProbeModule, ProbePair, SweepSpec, default_output, environment, parse_args,
    run_cli, source_hashes,
)
from scripts.bench.structural_tactic_sweep import acquire_cpu

AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SPEC = SweepSpec(
    description=__doc__ or "BKR semantic proof diagnostics",
    pairs=tuple(ProbePair(
        f"depth-{depth}",
        ProbeModule(f"HexSignDetMathlib.ProofProbe.D{depth}.SemanticBaseline", AXIOMS),
        ProbeModule(f"HexSignDetMathlib.ProofProbe.D{depth}.Semantic", AXIOMS),
        {"family": "same-level-graph-semantics", "depth": depth,
         "query_arity": 2**depth, "graph_nodes": depth + 1,
         "graph_edges": 2*depth, "degree": 2, "support_size": 1,
         "coefficient_extension_depth": 0,
         "measurement_scope": "application of root-count semantics to a warm accepted graph",
         "excluded_costs": ["literal checker reduction", "initial foundation build",
                            "compiled execution", "nested coefficient arithmetic"]},
    ) for depth in (1, 3, 5, 7)),
    probe_target="HexSignDetMathlibProofProbe",
    schema="hex-sign-det-semantic-probes-v1",
    measurement="paired-fresh-module-olean-wall",
    output_stem="hex-sign-det-semantics",
    required_samples=4,
    retain_compiler_output=True,
    extra_sources=(Path("libraries.yml"), Path("SPEC/benchmarking.md"),
                   Path("reports/sign-det-semantic-probes.md"),
                   Path("scripts/bench/structural_tactic_sweep.py")),
)


def main() -> int:
    args = parse_args(SPEC.description, default_samples=SPEC.required_samples or 4)
    cpu, lease = acquire_cpu(args.cpu)
    try:
        env = environment()
        output = args.output or default_output(env, SPEC.output_stem)
        if not output.is_absolute():
            output = ROOT / output
        sidecar = Path(str(output) + ".samples.jsonl")
        if output.exists() or sidecar.exists():
            raise RuntimeError("measurement output exists; choose a fresh path")
        # Flush every completed arm before validation, including failed arms.
        with tempfile.NamedTemporaryFile(mode="w", prefix="hex-sign-det-semantics-",
                                         suffix=".jsonl", delete=False) as log:
            retained = Path(log.name)
            print(f"Incremental samples: {retained}", flush=True)
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
            except BaseException:
                print(f"Retained partial samples: {retained}", file=sys.stderr)
                raise
        sidecar.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(retained, sidecar)
        return code
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
